import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nonunital.Hereditary

namespace OAI

noncomputable section
namespace NonunitalGamma
open Filter Topology Pureness
open scoped ComplexOrder ENNReal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma hereditary_inr {h c : A} (hc : c ∈ hereditaryCarrier h) :
    (Unitization.inr c : Unitization ℂ A) ∈ Pureness.hereditaryCarrier (Unitization.inr h) := by
  obtain ⟨u,hu,ht⟩ := mem_closure_iff_seq_limit.mp hc
  apply isClosed_closure.mem_of_tendsto (Unitization.isometry_inr.continuous.continuousAt.tendsto.comp ht)
  apply Eventually.of_forall
  intro n
  obtain ⟨v,hv⟩ := hu n
  apply subset_closure
  refine ⟨Unitization.inr v,?_⟩
  change Unitization.inr h * Unitization.inr v * Unitization.inr h=Unitization.inr (u n)
  rw [←hv]
  simp only [Unitization.inr_mul]

def NormalizedTrace.rank (τ : NormalizedTrace A) (a : A) : ℝ≥0∞ :=
  normalizedRootRank τ.unitized (Unitization.inr a)

lemma NormalizedTrace.hereditary_rank_le (τ : NormalizedTrace A) {h c : A}
    (hh : 0 ≤ h) (hc : 0 ≤ c) (hcm : c ∈ hereditaryCarrier h) : τ.rank c ≤ τ.rank h :=
  hereditary_rank_domination τ.unitized _ _ (Unitization.inr_nonneg_iff.mpr hh)
    (Unitization.inr_nonneg_iff.mpr hc) (hereditary_inr hcm)

lemma NormalizedTrace.rank_cyclic (τ : NormalizedTrace A) (v : A) :
    τ.rank (star v*v)=τ.rank (v*star v) := by
  simp only [NormalizedTrace.rank,Unitization.inr_mul,Unitization.inr_star]
  exact rank_star_mul_self τ.unitized (Unitization.inr v)

lemma exists_nonzero_cross (hsimple : TopologicallySimple A) {e f : A}
    (he : 0 ≤ e) (he0 : e ≠ 0) (hf0 : f ≠ 0) : ∃ z : A, e*z*f ≠ 0 := by
  by_contra hno
  have hz (z : A) : e*z*f=0 := not_not.mp (not_exists.mp hno z)
  let I : TwoSidedIdeal A := .mk' {a | ∀ z : A, e*z*a=0}
    (by intro z;simp)
    (by intro a b ha hb z;rw [mul_add,ha z,hb z,add_zero])
    (by intro a ha z;rw [mul_neg,ha z,neg_zero])
    (by intro a b hb z;simpa only [mul_assoc] using hb (z*a))
    (by intro a b ha z;rw [←mul_assoc,ha z,zero_mul])
  have hI : IsClosed (I : Set A) := by
    rw [show (I : Set A)={a | ∀ z : A,e*z*a=0} from TwoSidedIdeal.coe_mk' ..]
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun z => isClosed_eq (continuous_const.mul continuous_id) continuous_const
  have hft : f ∈ I := by simpa only [I,TwoSidedIdeal.mem_mk',Set.mem_ofPred_eq] using hz
  have hit : I=⊤ := (hsimple I hI).resolve_left (fun hi => by
    rw [hi,TwoSidedIdeal.mem_bot] at hft;exact hf0 hft)
  have hem : e ∈ I := hit.symm ▸ TwoSidedIdeal.mem_top A
  have hez : ∀ z : A,e*z*e=0 := by
    simpa only [I,TwoSidedIdeal.mem_mk',Set.mem_ofPred_eq] using hem
  have ht := ((CStarAlgebra.increasingApproximateUnit A).tendsto_mul_left e).mul_const e
  simp only [hez] at ht
  have hee : e*e=0 := tendsto_nhds_unique ht tendsto_const_nhds
  apply he0
  apply (CStarRing.star_mul_self_eq_zero_iff e).mp
  simpa only [he.star_eq] using hee

theorem exists_common_rank_minorant (hsimple : TopologicallySimple A) {e f : A}
    (he : 0 ≤ e) (he0 : e ≠ 0) (hf : 0 ≤ f) (hf0 : f ≠ 0) :
    ∃ h : A, 0 ≤ h ∧ h ≠ 0 ∧ ∀ τ : NormalizedTrace A,
      τ.rank h ≤ τ.rank e ∧ τ.rank h ≤ τ.rank f := by
  obtain ⟨z,hz⟩ := exists_nonzero_cross hsimple he he0 hf0
  let v := e*z*f
  have hvm : v*star v ∈ hereditaryCarrier e := by
    apply subset_closure
    exact ⟨z*f*f*star z,by simp only [v,star_mul,he.star_eq,hf.star_eq,mul_assoc]⟩
  have hsm : star v*v ∈ hereditaryCarrier f := by
    apply subset_closure
    exact ⟨star z*e*e*z,by simp only [v,star_mul,he.star_eq,hf.star_eq,mul_assoc]⟩
  refine ⟨star v*v,star_mul_self_nonneg v,?_,?_⟩
  · exact (CStarRing.star_mul_self_ne_zero_iff v).mpr hz
  · intro τ
    exact ⟨by rw [τ.rank_cyclic];exact τ.hereditary_rank_le he (mul_star_self_nonneg v) hvm,
      τ.hereditary_rank_le hf (star_mul_self_nonneg v) hsm⟩

omit [PartialOrder A] [StarOrderedRing A] in
lemma hereditary_mul_eq_zero {h k x y : A}
    (hx : x ∈ hereditaryCarrier h) (hy : y ∈ hereditaryCarrier k) (hhk : h * k = 0) :
    x * y = 0 := by
  obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.mp hx
  obtain ⟨v, hv, hvy⟩ := mem_closure_iff_seq_limit.mp hy
  have hz (j : ℕ) : u j * v j = 0 := by
    obtain ⟨a, ha⟩ := hu j
    obtain ⟨b, hb⟩ := hv j
    rw [← ha, ← hb]
    calc
      _ = h * a * (h * k) * b * k := by simp only [mul_assoc]
      _ = 0 := by rw [hhk]; simp
  have ht := hux.mul hvy
  simp only [hz] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

lemma exists_orthogonal_family_with_reserve (τ : NormalizedTrace A)
    (hsimple : TopologicallySimple A) (hproj : Projectionless A)
    (h : A) (hh : 0 ≤ h) (hh0 : h ≠ 0) (N : ℕ) :
    ∃ r : A, ∃ a : Fin N → A,
      0 ≤ r ∧ r ≠ 0 ∧ (∀ i, 0 ≤ a i) ∧ (∀ i, a i ≠ 0) ∧
      (∀ i j, i ≠ j → a i * a j = 0) ∧ (∀ i, a i * r = 0) := by
  induction N with
  | zero => exact ⟨h, Fin.elim0, hh, hh0, by simp, by simp, by simp, by simp⟩
  | succ N ih =>
    obtain ⟨r, a, hr, hr0, ha, ha0, horth, har⟩ := ih
    obtain ⟨e, f, he, he0, hem, hf, hf0, hfm, hef⟩ :=
      exists_orthogonal_pair_hereditary τ hsimple hproj r hr hr0
    have hae (i : Fin N) : a i * e = 0 :=
      hereditary_mul_eq_zero (self_mem_hereditary _ (ha i)) hem (har i)
    have hea (i : Fin N) : e * a i = 0 := by
      simpa only [star_mul, he.star_eq, (ha i).star_eq, star_zero] using congrArg star (hae i)
    have haf (i : Fin N) : a i * f = 0 :=
      hereditary_mul_eq_zero (self_mem_hereditary _ (ha i)) hfm (har i)
    refine ⟨f, Fin.cons e a, hf, hf0, ?_, ?_, ?_, ?_⟩
    · intro i
      cases i using Fin.cases with
      | zero => exact he
      | succ i => exact ha i
    · intro i
      cases i using Fin.cases with
      | zero => exact he0
      | succ i => exact ha0 i
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j => exact hea j
      | succ i =>
        cases j using Fin.cases with
        | zero => exact hae i
        | succ j => exact horth i j (fun heq => hij (congrArg Fin.succ heq))
    · intro i
      cases i using Fin.cases with
      | zero => exact hef
      | succ i => exact haf i

lemma exists_nonzero_positive [Nontrivial A] : ∃ h : A, 0 ≤ h ∧ h ≠ 0 := by
  obtain ⟨x,hx⟩ := exists_ne (0 : A)
  exact ⟨star x*x,star_mul_self_nonneg x,(CStarRing.star_mul_self_ne_zero_iff x).mpr hx⟩

lemma exists_finite_common_rank_minorant [Nontrivial A]
    (hsimple : TopologicallySimple A) {ι : Type*} (I : Finset ι) (e : ι → A)
    (he : ∀ i ∈ I, 0 ≤ e i) (he0 : ∀ i ∈ I,e i ≠ 0) :
    ∃ h : A,0 ≤ h ∧ h ≠ 0 ∧ ∀ τ : NormalizedTrace A,∀ i ∈ I,τ.rank h ≤ τ.rank (e i) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    obtain ⟨h,hh,hh0⟩ := exists_nonzero_positive (A := A)
    exact ⟨h,hh,hh0,by simp⟩
  | @insert i I hi ih =>
    obtain ⟨h,hh,hh0,hhr⟩ := ih (fun j hj => he j (Finset.mem_insert_of_mem hj))
      (fun j hj => he0 j (Finset.mem_insert_of_mem hj))
    obtain ⟨k,hk,hk0,hkr⟩ := exists_common_rank_minorant hsimple hh hh0
      (he i (Finset.mem_insert_self i I)) (he0 i (Finset.mem_insert_self i I))
    refine ⟨k,hk,hk0,?_⟩
    intro τ j hj
    rcases Finset.mem_insert.mp hj with rfl|hj
    · exact (hkr τ).2
    · exact (hkr τ).1.trans (hhr τ j hj)

theorem small_hereditary_rank [Nontrivial A] (hsimple : TopologicallySimple A)
    (hproj : Projectionless A) (hT : Nonempty (NormalizedTrace A)) (N : ℕ) (hN : 1 ≤ N) :
    ∃ h : A,0 ≤ h ∧ h ≠ 0 ∧ ∀ τ : NormalizedTrace A,τ.rank h ≤ 1/(N:ℝ≥0∞) := by
  classical
  obtain ⟨τ⟩ := hT
  obtain ⟨g,hg,hg0⟩ := exists_nonzero_positive (A := A)
  obtain ⟨r,a,hr,hr0,ha,ha0,horth,har⟩ :=
    exists_orthogonal_family_with_reserve τ hsimple hproj g hg hg0 N
  obtain ⟨h,hh,hh0,hR⟩ := exists_finite_common_rank_minorant hsimple Finset.univ a
    (fun i _ => ha i) (fun i _ => ha0 i)
  refine ⟨h,hh,hh0,?_⟩
  intro σ
  have hs : (N:ℝ≥0∞)*σ.rank h ≤ 1 := by
    calc
      _ = ∑ i : Fin N,σ.rank h := by simp [nsmul_eq_mul]
      _ ≤ ∑ i : Fin N,σ.rank (a i) := Finset.sum_le_sum (fun i hi => hR σ i hi)
      _ ≤ 1 := Pureness.orthogonal_rank_sum_le_one σ.unitized Finset.univ
        (fun i => Unitization.inr (a i)) (fun i _ => Unitization.inr_nonneg_iff.mpr (ha i))
        (fun i _ j _ hij => by rw [←Unitization.inr_mul,horth i j hij,Unitization.inr_zero])
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast (Nat.ne_of_gt hN))) (by simp)).mpr
  simpa only [mul_comm] using hs

end NonunitalGamma

end

end OAI
