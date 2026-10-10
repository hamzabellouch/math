import OAI.Probability.FKMaps.TreeCode

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

local instance : MeasurableSpace C(unitInterval, ℝ) := borel _
local instance : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩

def weakLadderHit (x : ℕ → ℕ) (n k : ℕ) : Prop :=
  negativeSurvival x n ∧ integerSum x (n+1)=(k:ℤ)


lemma measurableSet_weakLadderHit (n k : ℕ) : MeasurableSet {x | weakLadderHit x n k} := by
  unfold weakLadderHit negativeSurvival
  simp only [Set.ofPred_and,Set.ofPred_forall]
  exact (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ => measurableSet_lt (measurable_integerSum j) measurable_const).inter
    (measurableSet_eq_fun (measurable_integerSum (n+1)) measurable_const)


lemma weakLadderHit_decomposition (n k : ℕ) :
    {x | weakLadderHit x n k}=⋃ j : ℕ,
      {x | integerSum x n=-(j:ℤ) ∧ negativeSurvival x n} ∩ {x | x n=j+k+1} := by
  ext x
  simp only [Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_inter_iff]
  constructor
  · rintro ⟨hs,he⟩
    have hn : integerSum x n ≤ 0 := by
      cases n with
      | zero => simp
      | succ n => exact (hs _ (by omega) le_rfl).le
    refine ⟨(-integerSum x n).toNat,⟨?_,hs⟩,?_⟩
    · rw [Int.toNat_of_nonneg (by omega)]
      omega
    · rw [integerSum_succ] at he
      have hj := Int.toNat_of_nonneg (show 0 ≤ -integerSum x n by omega)
      omega
  · rintro ⟨j,⟨he,hs⟩,hx⟩
    refine ⟨hs,?_⟩
    rw [integerSum_succ,he,hx]
    push_cast
    ring


lemma weakLadderHit_decomposition_disjoint (n k : ℕ) :
    Pairwise (fun j l : ℕ => Disjoint
      ({x | integerSum x n=-(j:ℤ) ∧ negativeSurvival x n} ∩ {x | x n=j+k+1})
      ({x | integerSum x n=-(l:ℤ) ∧ negativeSurvival x n} ∩ {x | x n=l+k+1})) := by
  intro j l hjl
  apply Set.disjoint_left.mpr
  intro x hj hl
  exact hjl (by have := hj.1.1; have := hl.1.1; omega)


lemma CriticalEvenOffspring.weakLadderHit_mass (p : CriticalEvenOffspring) (n k : ℕ) :
    p.streamLaw {x | weakLadderHit x n k}=
    ∑' j : ℕ, p.streamLaw {x | integerSum x n=-(j:ℤ) ∧ negativeSurvival x n} * p.law (j+k+1) := by
  rw [weakLadderHit_decomposition,measure_iUnion (weakLadderHit_decomposition_disjoint n k)]
  · apply tsum_congr
    intro j
    exact p.prefix_inter_next n (j+k+1) _ (measurableSet_survival_endpoint j n)
      (survival_endpoint_truncate j n)
  · intro j
    exact (measurableSet_survival_endpoint j n).inter
      (measurableSet_eq_fun (measurable_pi_apply n) measurable_const)


theorem CriticalEvenOffspring.weakLadder_overshoot_mass (p : CriticalEvenOffspring) (k : ℕ) :
    (∑' n, p.streamLaw {x | weakLadderHit x n k})=∑' j : ℕ, p.law (j+k+1) := by
  simp_rw [p.weakLadderHit_mass]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro j
  rw [ENNReal.tsum_mul_right,p.negative_potential,one_mul]


lemma tail_tsum_ite (f : ℕ → ℝ≥0∞) (k : ℕ) :
    (∑' j : ℕ, f (j+k+1))=∑' r : ℕ, if k<r then f r else 0 := by
  have hi : Function.Injective (fun j : ℕ => j+k+1) := by intro a b h; dsimp at h; omega
  have hs : Function.support (fun r => if k<r then f r else 0) ⊆
      Set.range (fun j : ℕ => j+k+1) := by
    intro r hr
    have hkr : k<r := by by_contra hn; simp [Function.support,hn] at hr
    exact ⟨r-k-1,by dsimp; omega⟩
  simpa only [show ∀ j : ℕ, k<j+k+1 from by omega,ite_true] using hi.tsum_eq hs


lemma tail_tsum_total (f : ℕ → ℝ≥0∞) :
    (∑' k : ℕ, ∑' j : ℕ, f (j+k+1))=∑' r : ℕ, (r:ℝ≥0∞)*f r := by
  simp_rw [tail_tsum_ite]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro r
  rw [tsum_eq_sum (s := Finset.range r) (fun k hk => by simp [show ¬ k<r from by simpa using hk])]
  calc
    (∑ k ∈ Finset.range r, if k<r then f r else 0) = ∑ _k ∈ Finset.range r, f r := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [ite_eq_left (Finset.mem_range.mp hk)]
    _ = _ := by simp


lemma sum_range_cast_nat (r : ℕ) :
    (∑ k ∈ Finset.range r,(k:ℝ))=((r:ℝ)^2-r)/2 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ,ih]
    push_cast
    ring


lemma tail_tsum_first_moment (f : ℕ → ℝ≥0∞) :
    (∑' k : ℕ, (k:ℝ≥0∞)*(∑' j : ℕ, f (j+k+1)))=
    ∑' r : ℕ, ENNReal.ofReal (((r:ℝ)^2-r)/2)*f r := by
  simp_rw [tail_tsum_ite,← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro r
  rw [tsum_eq_sum (s := Finset.range r) (fun k hk => by simp [show ¬ k<r from by simpa using hk])]
  have he : (∑ k ∈ Finset.range r, (k:ℝ≥0∞)*(if k<r then f r else 0))=
      (∑ k ∈ Finset.range r,(k:ℝ≥0∞))*f r := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k hk => by rw [ite_eq_left (Finset.mem_range.mp hk)]
  rw [he]
  congr 1
  rw [← sum_range_cast_nat,ENNReal.ofReal_sum_of_nonneg (fun k _ => Nat.cast_nonneg k)]
  simp


lemma CriticalEvenOffspring.ladder_total (p : CriticalEvenOffspring) :
    (∑' k : ℕ, ∑' j : ℕ, p.law (j+k+1))=1 := by
  rw [tail_tsum_total]
  have h := ENNReal.ofReal_tsum_of_nonneg
    (fun k : ℕ => mul_nonneg (Nat.cast_nonneg k) (p.nonneg k)) p.mean.summable
  rw [p.mean.tsum_eq] at h
  simpa [ENNReal.ofReal_mul,Nat.cast_nonneg] using h.symm


def CriticalEvenOffspring.ladderLaw (p : CriticalEvenOffspring) : PMF ℕ :=
  ⟨fun k => ∑' j : ℕ, p.law (j+k+1), ENNReal.summable.hasSum_iff.mpr p.ladder_total⟩


@[simp] lemma CriticalEvenOffspring.ladderLaw_apply (p : CriticalEvenOffspring) (k : ℕ) :
    p.ladderLaw k=∑' j : ℕ, p.law (j+k+1) := rfl


lemma CriticalEvenOffspring.variance_eq_second_sub_one (p : CriticalEvenOffspring) :
    p.variance=(∑' k : ℕ, (k:ℝ)^2*p.mass k)-1 := by
  have he : (fun k : ℕ => ((k:ℝ)-1)^2*p.mass k)=
      (fun k : ℕ => (k:ℝ)^2*p.mass k-2*((k:ℝ)*p.mass k)+p.mass k) := by
    funext k
    ring
  rw [variance,he]
  rw [Summable.tsum_add (p.second.sub (p.mean.summable.mul_left 2)) p.total.summable,
    Summable.tsum_sub p.second (p.mean.summable.mul_left 2),tsum_mul_left,p.mean.tsum_eq,p.total.tsum_eq]
  ring


lemma CriticalEvenOffspring.ladder_first_moment (p : CriticalEvenOffspring) :
    (∑' k : ℕ, (k:ℝ≥0∞)*p.ladderLaw k)=ENNReal.ofReal (p.variance/2) := by
  simp only [p.ladderLaw_apply]
  rw [tail_tsum_first_moment]
  have hs : Summable (fun r : ℕ => (((r:ℝ)^2-r)/2)*p.mass r) := by
    apply Summable.congr ((p.second.sub p.mean.summable).div_const 2)
    intro r
    ring
  have hn (r : ℕ) : 0 ≤ (((r:ℝ)^2-r)/2)*p.mass r := by
    apply mul_nonneg _ (p.nonneg r)
    have hr : r=0 ∨ 1 ≤ r := by omega
    rcases hr with hr | hr
    · simp [hr]
    · have hr' : (1:ℝ) ≤ r := by exact_mod_cast hr
      nlinarith
  have he : (∑' r : ℕ, (((r:ℝ)^2-r)/2)*p.mass r)=p.variance/2 := by
    have hf : (fun r : ℕ => (((r:ℝ)^2-r)/2)*p.mass r)=
        fun r : ℕ => ((r:ℝ)^2*p.mass r-(r:ℝ)*p.mass r)/2 := by funext r; ring
    rw [hf,tsum_div_const,
      Summable.tsum_sub p.second p.mean.summable,p.mean.tsum_eq,p.variance_eq_second_sub_one]
  rw [← he,ENNReal.ofReal_tsum_of_nonneg hn hs]
  apply tsum_congr
  intro r
  rw [p.law_apply,ENNReal.ofReal_mul (by
    have hr : r=0 ∨ 1 ≤ r := by omega
    rcases hr with hr | hr
    · simp [hr]
    · have hr' : (1:ℝ) ≤ r := by exact_mod_cast hr
      nlinarith)]


def streamShift (n : ℕ) (x : ℕ → ℕ) : ℕ → ℕ := fun k => x (n+k)


lemma measurable_streamShift (n : ℕ) : Measurable (streamShift n) := by
  apply Measurable.of_eval
  intro k
  exact measurable_pi_apply _


lemma CriticalEvenOffspring.streamShift_preserving (p : CriticalEvenOffspring) (n : ℕ) :
    MeasurePreserving (streamShift n) p.streamLaw p.streamLaw := by
  have hi : iIndepFun (fun k (x : ℕ → ℕ) => x k) p.streamLaw :=
    iIndepFun_infinitePi (X := fun _ (k : ℕ) => k) (fun _ => measurable_id)
  have hinj : Function.Injective (fun k : ℕ => n+k) := by intro a b h; dsimp at h; omega
  have h := (hi.precomp hinj).map_fun_eq_infinitePi_map (fun k => measurable_pi_apply (n+k))
  refine ⟨measurable_streamShift n,?_⟩
  change p.streamLaw.map (fun ω i => ω (n+i))=p.streamLaw
  rw [h]
  unfold CriticalEvenOffspring.streamLaw
  congr 1
  funext k
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => p.law.toMeasure) (n+k)).map_eq


lemma CriticalEvenOffspring.truncate_indep_shift (p : CriticalEvenOffspring) (n : ℕ) :
    IndepFun (truncateStream n) (streamShift n) p.streamLaw := by
  classical
  apply IndepFun.indepFun_process (measurable_truncateStream n) (fun k => measurable_pi_apply (n+k))
  intro I
  have hi : iIndepFun (fun k (x : ℕ → ℕ) => x k) p.streamLaw :=
    iIndepFun_infinitePi (X := fun _ (k : ℕ) => k) (fun _ => measurable_id)
  have hd : Disjoint (Finset.range n) (I.image (fun k => n+k)) := by
    apply Finset.disjoint_left.mpr
    intro k hk hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    have := Finset.mem_range.mp hk
    omega
  have h := hi.indepFun_finset (Finset.range n) (I.image (fun k => n+k)) hd
    (fun k => measurable_pi_apply k)
  let f : ((Finset.range n) → ℕ) → (ℕ → ℕ) :=
    fun x k => if hk : k<n then x ⟨k,Finset.mem_range.mpr hk⟩ else 0
  let g : (I.image (fun k => n+k) → ℕ) → (I → ℕ) :=
    fun x k => x ⟨n+k,Finset.mem_image.mpr ⟨k,k.property,rfl⟩⟩
  have hf : Measurable f := by
    apply Measurable.of_eval
    intro k
    dsimp [f]
    split_ifs <;> fun_prop
  have hg : Measurable g := by fun_prop
  exact h.comp hf hg


lemma CriticalEvenOffspring.prefix_inter_shift (p : CriticalEvenOffspring)
    (n : ℕ) (E F : Set (ℕ → ℕ)) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (htr : (truncateStream n) ⁻¹' E=E) :
    p.streamLaw (E ∩ (streamShift n) ⁻¹' F)=p.streamLaw E*p.streamLaw F := by
  have h := (p.truncate_indep_shift n).measure_inter_preimage_eq_mul E F hE hF
  rw [htr,(p.streamShift_preserving n).measure_preimage hF.nullMeasurableSet] at h
  exact h


lemma weakLadderHit_truncate (n k : ℕ) :
    (truncateStream (n+1)) ⁻¹' {x | weakLadderHit x n k}={x | weakLadderHit x n k} := by
  ext x
  change weakLadderHit (truncateStream (n+1) x) n k ↔ weakLadderHit x n k
  simp only [weakLadderHit,negativeSurvival,integerSum_truncateStream x le_rfl]
  constructor <;> rintro ⟨hs,he⟩ <;> refine ⟨?_,he⟩
  · intro j hj hjn
    simpa only [integerSum_truncateStream x (by omega : j ≤ n+1)] using hs j hj hjn
  · intro j hj hjn
    simpa only [integerSum_truncateStream x (by omega : j ≤ n+1)] using hs j hj hjn


lemma weakLadderHit_unique {x : ℕ → ℕ} {n k m l : ℕ}
    (hn : weakLadderHit x n k) (hm : weakLadderHit x m l) : n=m ∧ k=l := by
  have he : n=m := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hh := hm.1 (n+1) (by omega) (by omega)
      rw [hn.2] at hh
      omega
    · have hh := hn.1 (m+1) (by omega) (by omega)
      rw [hm.2] at hh
      omega
  refine ⟨he,?_⟩
  subst m
  have := hn.2
  have := hm.2
  omega


lemma weakLadderHit_pairwise : Pairwise (fun a b : ℕ × ℕ =>
    Disjoint {x | weakLadderHit x a.1 a.2} {x | weakLadderHit x b.1 b.2}) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro x ha hb
  have h := weakLadderHit_unique ha hb
  exact hab (Prod.ext h.1 h.2)


lemma CriticalEvenOffspring.ae_weakLadderHit (p : CriticalEvenOffspring) :
    ∀ᵐ x ∂p.streamLaw, ∃ n k, weakLadderHit x n k := by
  have he : {x | ∃ n k, weakLadderHit x n k}=⋃ a : ℕ×ℕ,{x | weakLadderHit x a.1 a.2} := by
    ext x
    simp
  apply (mem_ae_iff_prob_eq_one (show MeasurableSet {x | ∃ n k, weakLadderHit x n k} from by
    rw [he]; exact MeasurableSet.iUnion fun a => measurableSet_weakLadderHit a.1 a.2)).mpr
  rw [he,measure_iUnion weakLadderHit_pairwise (fun a => measurableSet_weakLadderHit a.1 a.2),
    ENNReal.tsum_prod',ENNReal.tsum_comm]
  simp_rw [p.weakLadder_overshoot_mass]
  exact p.ladder_total


lemma measurableSet_hasWeakLadder : MeasurableSet {x : ℕ → ℕ | ∃ n, 0 ≤ integerSum x (n+1)} := by
  simp only [Set.ofPred_exists]
  exact MeasurableSet.iUnion fun n => measurableSet_le measurable_const (measurable_integerSum (n+1))


def ladderPredicate (x : ℕ → ℕ) (n : ℕ) : Prop :=
  0 ≤ integerSum x (n+1) ∨ (¬ ∃ m, 0 ≤ integerSum x (m+1)) ∧ n=0


lemma ladderPredicate_exists (x : ℕ → ℕ) : ∃ n, ladderPredicate x n := by
  by_cases h : ∃ n, 0 ≤ integerSum x (n+1)
  · obtain ⟨n,hn⟩ := h
    exact ⟨n,Or.inl hn⟩
  · exact ⟨0,Or.inr ⟨h,rfl⟩⟩


def ladderIndex (x : ℕ → ℕ) : ℕ := by
  classical
  exact Nat.find (ladderPredicate_exists x)


lemma measurable_ladderIndex : Measurable ladderIndex := by
  classical
  apply measurable_find (fun x => ladderPredicate_exists x)
  intro n
  unfold ladderPredicate
  simp only [Set.ofPred_or,Set.ofPred_and,← Set.compl_ofPred]
  exact (measurableSet_le measurable_const (measurable_integerSum (n+1))).union
    (measurableSet_hasWeakLadder.compl.inter (MeasurableSet.const _))


lemma ladderIndex_eq_of_hit {x : ℕ → ℕ} {n k : ℕ} (h : weakLadderHit x n k) :
    ladderIndex x=n := by
  classical
  apply (Nat.find_eq_iff (ladderPredicate_exists x)).mpr
  refine ⟨Or.inl (by rw [h.2]; positivity),?_⟩
  intro j hj
  rintro (hj' | hj')
  · have hh := h.1 (j+1) (by omega) (by omega)
    omega
  · exact hj'.1 ⟨n,by rw [h.2]; positivity⟩


def ladderOvershoot (x : ℕ → ℕ) : ℕ := (integerSum x (ladderIndex x+1)).toNat


def ladderTail (x : ℕ → ℕ) : ℕ → ℕ := streamShift (ladderIndex x+1) x


lemma measurable_ladderOvershoot : Measurable ladderOvershoot := by
  have hs : Measurable (fun x : ℕ → ℕ => (x,ladderIndex x+1)) :=
    measurable_id.prodMk (measurable_ladderIndex.add_const 1)
  have he : Measurable (fun z : (ℕ → ℕ)×ℕ => integerSum z.1 z.2) := by
    apply measurable_from_prod_countable_left
    intro n
    exact measurable_integerSum n
  exact (measurable_of_countable (f := Int.toNat)).comp (he.comp hs)


lemma measurable_ladderTail : Measurable ladderTail := by
  apply Measurable.of_eval
  intro k
  have hs : Measurable (fun x : ℕ → ℕ => (x,ladderIndex x+1+k)) :=
    measurable_id.prodMk ((measurable_ladderIndex.add_const 1).add_const k)
  have he : Measurable (fun z : (ℕ → ℕ)×ℕ => z.1 z.2) := by
    apply measurable_from_prod_countable_left
    intro n
    exact measurable_pi_apply n
  exact he.comp hs


lemma ladderOvershoot_of_hit {x : ℕ → ℕ} {n k : ℕ} (h : weakLadderHit x n k) :
    ladderOvershoot x=k := by
  rw [ladderOvershoot,ladderIndex_eq_of_hit h,h.2,Int.toNat_natCast]


lemma ladderTail_of_hit {x : ℕ → ℕ} {n k : ℕ} (h : weakLadderHit x n k) :
    ladderTail x=streamShift (n+1) x := by
  rw [ladderTail,ladderIndex_eq_of_hit h]


lemma CriticalEvenOffspring.ladder_slice_mass (p : CriticalEvenOffspring)
    (k : ℕ) (F : Set (ℕ → ℕ)) (hF : MeasurableSet F) :
    p.streamLaw ({x | ladderOvershoot x=k} ∩ ladderTail ⁻¹' F)=
      p.ladderLaw k*p.streamLaw F := by
  have he : ({x | ladderOvershoot x=k} ∩ ladderTail ⁻¹' F : Set (ℕ → ℕ)) =ᵐ[p.streamLaw]
      ⋃ n : ℕ, {x | weakLadderHit x n k} ∩ (streamShift (n+1)) ⁻¹' F := by
    filter_upwards [p.ae_weakLadderHit] with x hx
    apply propext
    obtain ⟨n,l,hh⟩ := hx
    constructor
    · intro hm
      have hl : l=k := (ladderOvershoot_of_hit hh).symm.trans hm.1
      subst l
      exact Set.mem_iUnion.mpr ⟨n,hh,by simpa only [Set.mem_preimage,← ladderTail_of_hit hh] using hm.2⟩
    · intro hm
      obtain ⟨m,hm,hxF⟩ := Set.mem_iUnion.mp hm
      exact ⟨ladderOvershoot_of_hit hm,by simpa only [Set.mem_preimage,ladderTail_of_hit hm] using hxF⟩
  rw [measure_congr he,measure_iUnion]
  · simp_rw [p.prefix_inter_shift (n := _)
      (hE := measurableSet_weakLadderHit _ _) (hF := hF) (htr := weakLadderHit_truncate _ _)]
    rw [ENNReal.tsum_mul_right,p.weakLadder_overshoot_mass]
    rfl
  · intro n m hnm
    apply Set.disjoint_left.mpr
    intro x hn hm
    exact hnm (weakLadderHit_unique hn.1 hm.1).1
  · intro n
    exact (measurableSet_weakLadderHit n k).inter ((measurable_streamShift (n+1)) hF)


lemma countable_slice_rectangle {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : Measure Ω) (ν : Measure β) (q : PMF ℕ) (Y : Ω → ℕ) (T : Ω → β)
    (hY : Measurable Y) (hT : Measurable T)
    (h : ∀ k E, MeasurableSet E → μ ({x | Y x=k} ∩ T ⁻¹' E)=q k*ν E)
    (A : Set ℕ) (E : Set β) (hA : MeasurableSet A) (hE : MeasurableSet E) :
    μ (Y ⁻¹' A ∩ T ⁻¹' E)=q.toMeasure A*ν E := by
  classical
  have he : Y ⁻¹' A ∩ T ⁻¹' E=⋃ k ∈ A, {x | Y x=k} ∩ T ⁻¹' E := by
    ext x
    simp only [Set.mem_inter_iff,Set.mem_preimage,Set.mem_iUnion,Set.mem_ofPred_eq]
    constructor
    · intro hx
      exact ⟨Y x,hx.1,rfl,hx.2⟩
    · rintro ⟨k,hk,he,hx⟩
      exact ⟨he.symm ▸ hk,hx⟩
  rw [he,measure_biUnion (Set.to_countable A)]
  · simp_rw [h _ E hE]
    rw [ENNReal.tsum_mul_right]
    congr 1
    rw [tsum_subtype,PMF.toMeasure_apply _ hA]
  · intro k _ l _ hkl
    apply Set.disjoint_left.mpr
    intro x hk hl
    exact hkl (hk.1.symm.trans hl.1)
  · intro k _
    exact (measurableSet_eq_fun hY measurable_const).inter (hT hE)


lemma CriticalEvenOffspring.ladder_rectangle (p : CriticalEvenOffspring)
    (A : Set ℕ) (F : Set (ℕ → ℕ)) (hF : MeasurableSet F) :
    p.streamLaw (ladderOvershoot ⁻¹' A ∩ ladderTail ⁻¹' F)=
      p.ladderLaw.toMeasure A*p.streamLaw F :=
  countable_slice_rectangle p.streamLaw p.streamLaw p.ladderLaw ladderOvershoot ladderTail
    measurable_ladderOvershoot measurable_ladderTail p.ladder_slice_mass A F ((Set.to_countable A).measurableSet) hF


lemma CriticalEvenOffspring.ladder_hasLaw (p : CriticalEvenOffspring) :
    HasLaw ladderOvershoot p.ladderLaw.toMeasure p.streamLaw := by
  refine ⟨measurable_ladderOvershoot.aemeasurable,?_⟩
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply measurable_ladderOvershoot hA]
  simpa using p.ladder_rectangle A Set.univ MeasurableSet.univ


lemma CriticalEvenOffspring.ladderTail_preserving (p : CriticalEvenOffspring) :
    MeasurePreserving ladderTail p.streamLaw p.streamLaw := by
  refine ⟨measurable_ladderTail,?_⟩
  apply Measure.ext
  intro F hF
  rw [Measure.map_apply measurable_ladderTail hF]
  simpa using p.ladder_rectangle Set.univ F hF


lemma CriticalEvenOffspring.ladder_indep_tail (p : CriticalEvenOffspring) :
    IndepFun ladderOvershoot ladderTail p.streamLaw := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro A F hA hF
  rw [(p.ladderTail_preserving).measure_preimage hF.nullMeasurableSet]
  have h := (p.ladder_hasLaw.measurePreserving measurable_ladderOvershoot).measure_preimage hA.nullMeasurableSet
  rw [h]
  exact p.ladder_rectangle A F hF


lemma CriticalEvenOffspring.ladder_integrable (p : CriticalEvenOffspring) :
    Integrable (fun k : ℕ => (k:ℝ)) p.ladderLaw.toMeasure := by
  rw [← Measure.sum_smul_dirac p.ladderLaw.toMeasure,integrable_sum_dirac_iff]
  · have hs : Summable (fun k : ℕ => ((k:ℝ≥0∞)*p.ladderLaw k).toReal) :=
      ENNReal.summable_toReal (by rw [p.ladder_first_moment]; exact ENNReal.ofReal_ne_top)
    simpa [PMF.toMeasure_apply_singleton,ENNReal.toReal_mul,mul_comm] using hs
  · intro k
    exact measure_ne_top _ _


lemma CriticalEvenOffspring.ladder_integral (p : CriticalEvenOffspring) :
    ∫ k : ℕ,(k:ℝ) ∂p.ladderLaw.toMeasure=p.variance/2 := by
  rw [integral_countable p.ladder_integrable]
  have h := congrArg ENNReal.toReal p.ladder_first_moment
  rw [ENNReal.toReal_ofReal (div_nonneg p.variance_pos.le (by norm_num)),
    ENNReal.tsum_toReal_eq (fun k => ENNReal.mul_ne_top (by simp) (PMF.apply_ne_top _ _))] at h
  simpa [measureReal_def,PMF.toMeasure_apply_singleton,ENNReal.toReal_mul,mul_comm] using h


lemma regenerative_cylinder {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → β) (T : Ω → Ω)
    (hY : Measurable Y) (hT : MeasurePreserving T μ μ) (h : IndepFun Y T μ)
    (A : ℕ → Set β) (hA : ∀ i, MeasurableSet (A i)) (n : ℕ) :
    μ {x | ∀ i < n, Y (T^[i] x) ∈ A i} =
      ∏ i ∈ Finset.range n, μ (Y ⁻¹' A i) := by
  induction n generalizing A with
  | zero => simp
  | succ n ih =>
    let E : Set Ω := {x | ∀ i < n, Y (T^[i] x) ∈ A (i+1)}
    have hE : MeasurableSet E := by
      dsimp [E]
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun (_ : i < n) =>
        (hY.comp (hT.measurable.iterate i)) (hA (i+1))
    have he : {x | ∀ i < n+1, Y (T^[i] x) ∈ A i}=Y ⁻¹' A 0 ∩ T ⁻¹' E := by
      ext x
      simp only [Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_preimage,E]
      constructor
      · intro hx
        refine ⟨by simpa using hx 0 (by omega),?_⟩
        intro i hi
        simpa only [Function.iterate_succ_apply] using hx (i+1) (by omega)
      · rintro ⟨h₀,hs⟩ i hi
        cases i with
        | zero => simpa using h₀
        | succ i => simpa only [Function.iterate_succ_apply] using hs i (by omega)
    rw [he,h.measure_inter_preimage_eq_mul _ _ (hA 0) hE,
      hT.measure_preimage hE.nullMeasurableSet,ih (fun i => A (i+1)) (fun i => hA (i+1)),
      Finset.prod_range_succ']
    exact mul_comm _ _


lemma regenerative_iIndepFun {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → β) (T : Ω → Ω)
    (hY : Measurable Y) (hT : MeasurePreserving T μ μ) (h : IndepFun Y T μ) :
    iIndepFun (fun i x => Y (T^[i] x)) μ := by
  classical
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro S A hA
  let n := S.sup id+1
  have hsub : S ⊆ Finset.range n := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  let B : ℕ → Set β := fun i => if i ∈ S then A i else Set.univ
  have hB : ∀ i, MeasurableSet (B i) := by
    intro i
    dsimp [B]
    split_ifs with hi
    · exact hA i hi
    · exact MeasurableSet.univ
  have he : (⋂ i ∈ S, (fun x => Y (T^[i] x)) ⁻¹' A i) =
      {x | ∀ i < n, Y (T^[i] x) ∈ B i} := by
    ext x
    simp only [Set.mem_iInter,Set.mem_preimage,Set.mem_ofPred_eq]
    constructor
    · intro hx i _
      dsimp [B]
      split_ifs with hi
      · exact hx i hi
      · trivial
    · intro hx i hi
      simpa [B,hi] using hx i (Finset.mem_range.mp (hsub hi))
  rw [he,regenerative_cylinder μ Y T hY hT h B hB]
  calc
    ∏ i ∈ Finset.range n, μ (Y ⁻¹' B i) = ∏ i ∈ S, μ (Y ⁻¹' B i) := by
      symm
      apply Finset.prod_subset hsub
      intro i _ hi
      simp [B,hi]
    _ = ∏ i ∈ S, μ ((fun x => Y (T^[i] x)) ⁻¹' A i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [show B i=A i by simp [B,hi]]
      symm
      exact (hT.iterate i).measure_preimage (hY (hA i hi)).nullMeasurableSet


def renewalIncrement (i : ℕ) (x : ℕ → ℕ) : ℕ :=
  ladderOvershoot (ladderTail^[i] x)


lemma measurable_renewalIncrement (i : ℕ) : Measurable (renewalIncrement i) :=
  measurable_ladderOvershoot.comp (measurable_ladderTail.iterate i)


lemma CriticalEvenOffspring.renewal_iid (p : CriticalEvenOffspring) :
    iIndepFun renewalIncrement p.streamLaw :=
  regenerative_iIndepFun p.streamLaw ladderOvershoot ladderTail
    measurable_ladderOvershoot p.ladderTail_preserving p.ladder_indep_tail


lemma CriticalEvenOffspring.renewal_hasLaw (p : CriticalEvenOffspring) (i : ℕ) :
    HasLaw (renewalIncrement i) p.ladderLaw.toMeasure p.streamLaw :=
  p.ladder_hasLaw.comp (p.ladderTail_preserving.iterate i).hasLaw


lemma CriticalEvenOffspring.renewal_strong_law (p : CriticalEvenOffspring) :
    ∀ᵐ x ∂p.streamLaw,
      Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n,(renewalIncrement i x : ℝ))/(n:ℝ))
        atTop (𝓝 (p.variance/2)) := by
  let X : ℕ → (ℕ → ℕ) → ℝ := fun i x => (renewalIncrement i x : ℝ)
  have hind : iIndepFun X p.streamLaw := p.renewal_iid.comp (fun _ => Nat.cast)
    (fun _ => measurable_of_countable _)
  have hint : Integrable (X 0) p.streamLaw :=
    ((p.renewal_hasLaw 0).measurePreserving (measurable_renewalIncrement 0)).integrable_comp_of_integrable
      p.ladder_integrable
  have hid : ∀ i, IdentDistrib (X i) (X 0) p.streamLaw p.streamLaw := by
    intro i
    exact ((p.renewal_hasLaw i).identDistrib (p.renewal_hasLaw 0)).comp (measurable_of_countable _)
  have hm : ∫ x, X 0 x ∂p.streamLaw=p.variance/2 := by
    exact ((p.renewal_hasLaw 0).integral_comp
      (measurable_of_countable (fun k : ℕ => (k:ℝ))).aestronglyMeasurable).trans p.ladder_integral
  simpa only [hm] using strong_law_ae_real X hint (fun _ _ hij => hind.indepFun hij) hid


def renewalCount (τ : ℕ → ℕ) (n : ℕ) : ℕ := Nat.findGreatest (fun r => τ r ≤ n) n


lemma renewalCount_spec {τ : ℕ → ℕ} (h₀ : τ 0=0) (n : ℕ) :
    τ (renewalCount τ n) ≤ n :=
  Nat.findGreatest_spec (P := fun r => τ r ≤ n) (Nat.zero_le n) (by simp [h₀])


lemma le_renewalCount_iff {τ : ℕ → ℕ} (hτ : StrictMono τ) (h₀ : τ 0=0)
    (r n : ℕ) : r ≤ renewalCount τ n ↔ τ r ≤ n := by
  constructor
  · intro h
    exact (hτ.monotone h).trans (renewalCount_spec h₀ n)
  · intro h
    exact Nat.le_findGreatest ((hτ.le_apply (x := r)).trans h) h


lemma renewalCount_succ_gt {τ : ℕ → ℕ} (hτ : StrictMono τ) (h₀ : τ 0=0)
    (n : ℕ) : n < τ (renewalCount τ n+1) := by
  rw [← not_le,← le_renewalCount_iff hτ h₀]
  omega


lemma renewalCount_mono {τ : ℕ → ℕ} (hτ : StrictMono τ) (h₀ : τ 0=0) :
    Monotone (renewalCount τ) := by
  intro m n hmn
  rw [le_renewalCount_iff hτ h₀]
  exact (renewalCount_spec h₀ m).trans hmn


lemma renewalCount_at {τ : ℕ → ℕ} (hτ : StrictMono τ) (h₀ : τ 0=0) (r : ℕ) :
    renewalCount τ (τ r)=r := by
  apply le_antisymm
  · exact hτ.le_iff_le.mp (renewalCount_spec h₀ (τ r))
  · exact (le_renewalCount_iff hτ h₀ r (τ r)).mpr le_rfl


lemma renewalCount_tendsto {τ : ℕ → ℕ} (hτ : StrictMono τ) (h₀ : τ 0=0) :
    Tendsto (renewalCount τ) atTop atTop := by
  apply tendsto_atTop.mpr
  intro r
  filter_upwards [Filter.eventually_ge_atTop (τ r)] with n hn
  exact (le_renewalCount_iff hτ h₀ r n).mpr hn


structure LadderEnumeration {α : Type*} [LinearOrder α] (S : ℕ → α) (τ : ℕ → ℕ) : Prop where
  zero : τ 0=0
  strictMono : StrictMono τ
  level_mono : Monotone (S ∘ τ)
  between : ∀ r k, τ r < k → k < τ (r+1) → S k < S (τ r)


lemma LadderEnumeration.le_level {α : Type*} [LinearOrder α] {S : ℕ → α} {τ : ℕ → ℕ}
    (h : LadderEnumeration S τ) (k : ℕ) : S k ≤ S (τ (renewalCount τ k)) := by
  have hk := renewalCount_spec h.zero k
  by_cases he : τ (renewalCount τ k)=k
  · rw [he]
  · exact (h.between _ k (lt_of_le_of_ne hk he) (renewalCount_succ_gt h.strictMono h.zero k)).le


lemma LadderEnumeration.maximum {α : Type*} [LinearOrder α] {S : ℕ → α} {τ : ℕ → ℕ}
    (h : LadderEnumeration S τ) {k n : ℕ} (hkn : k ≤ n) :
    S k ≤ S (τ (renewalCount τ n)) :=
  (h.le_level k).trans (h.level_mono (renewalCount_mono h.strictMono h.zero hkn))


lemma LadderEnumeration.record_at {α : Type*} [LinearOrder α] {S : ℕ → α} {τ : ℕ → ℕ}
    (h : LadderEnumeration S τ) (r : ℕ) {k : ℕ} (hk : k ≤ τ r) :
    S k ≤ S (τ r) := by
  simpa only [renewalCount_at h.strictMono h.zero] using h.maximum hk


def weakRecords {α : Type*} [LinearOrder α] (S : ℕ → α) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun k => ∀ j ≤ k, S j ≤ S k


@[simp] lemma mem_weakRecords {α : Type*} [LinearOrder α] (S : ℕ → α) (n k : ℕ) :
    k ∈ weakRecords S n ↔ 1 ≤ k ∧ k ≤ n ∧ ∀ j ≤ k, S j ≤ S k := by
  simp only [weakRecords,Finset.mem_filter,Finset.mem_Icc,and_assoc]


lemma LadderEnumeration.records {α : Type*} [LinearOrder α] {S : ℕ → α} {τ : ℕ → ℕ}
    (h : LadderEnumeration S τ) (n : ℕ) :
    weakRecords S n=(Finset.Icc 1 (renewalCount τ n)).image τ := by
  classical
  ext k
  rw [mem_weakRecords,Finset.mem_image]
  constructor
  · rintro ⟨hk1,hkn,hrec⟩
    let r := renewalCount τ k
    have hr : τ r=k := by
      by_contra he
      have hlt := lt_of_le_of_ne (renewalCount_spec h.zero k) he
      exact not_lt_of_ge (hrec (τ r) (renewalCount_spec h.zero k))
        (h.between r k hlt (renewalCount_succ_gt h.strictMono h.zero k))
    refine ⟨r,Finset.mem_Icc.mpr ⟨?_,?_⟩,hr⟩
    · by_contra hn
      have : r=0 := by omega
      rw [this,h.zero] at hr
      omega
    · exact (le_renewalCount_iff h.strictMono h.zero r n).mpr (hr ▸ hkn)
  · rintro ⟨r,hr,rfl⟩
    obtain ⟨hr1,hrn⟩ := Finset.mem_Icc.mp hr
    refine ⟨?_,(le_renewalCount_iff h.strictMono h.zero r n).mp hrn,fun j hj => h.record_at r hj⟩
    exact hr1.trans h.strictMono.le_apply


lemma LadderEnumeration.card_records {α : Type*} [LinearOrder α] {S : ℕ → α} {τ : ℕ → ℕ}
    (h : LadderEnumeration S τ) (n : ℕ) :
    (weakRecords S n).card=renewalCount τ n := by
  classical
  rw [h.records,Finset.card_image_of_injective _ h.strictMono.injective,Nat.card_Icc]
  omega


lemma LadderEnumeration.first_records_below {α : Type*} [LinearOrder α]
    {S : ℕ → α} {τ : ℕ → ℕ} (h : LadderEnumeration S τ) (n m : ℕ)
    (z : α) (hz : z ≤ S (τ m)) :
    ((weakRecords S n).filter fun k => S k < z).card ≤ m := by
  classical
  have hsub : (weakRecords S n).filter (fun k => S k < z) ⊆
      (Finset.range m).image τ := by
    intro k hk
    obtain ⟨hkr,hkz⟩ := Finset.mem_filter.mp hk
    rw [h.records] at hkr
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hkr
    refine Finset.mem_image.mpr ⟨r,Finset.mem_range.mpr ?_,rfl⟩
    by_contra hn
    exact not_lt_of_ge (hz.trans (h.level_mono (by omega : m ≤ r))) hkz
  exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans_eq (Finset.card_range m))


def ladderTime (x : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | r+1 => ladderTime x r+(ladderIndex (ladderTail^[r] x)+1)


@[simp] lemma ladderTime_zero (x : ℕ → ℕ) : ladderTime x 0=0 := rfl


lemma ladderTime_strictMono (x : ℕ → ℕ) : StrictMono (ladderTime x) := by
  apply strictMono_nat_of_lt_succ
  intro r
  dsimp [ladderTime]
  omega


lemma streamShift_add (a b : ℕ) (x : ℕ → ℕ) :
    streamShift a (streamShift b x)=streamShift (b+a) x := by
  funext k
  change x (b+(a+k))=x ((b+a)+k)
  rw [Nat.add_assoc]


lemma ladderTail_iterate (x : ℕ → ℕ) (r : ℕ) :
    ladderTail^[r] x=streamShift (ladderTime x r) x := by
  induction r with
  | zero =>
    change x=(fun k => x (0+k))
    funext k
    rw [Nat.zero_add]
  | succ r ih =>
    rw [Function.iterate_succ_apply',ladderTail,ih,streamShift_add,ladderTime,ih]


lemma integerSum_shift (x : ℕ → ℕ) (a k : ℕ) :
    integerSum (streamShift a x) k=integerSum x (a+k)-integerSum x a := by
  unfold integerSum streamShift
  rw [Finset.sum_range_add]
  ring


def HasAllLadders (x : ℕ → ℕ) : Prop :=
  ∀ r, ∃ n k, weakLadderHit (ladderTail^[r] x) n k


lemma CriticalEvenOffspring.ae_all_ladders (p : CriticalEvenOffspring) :
    ∀ᵐ x ∂p.streamLaw, HasAllLadders x := by
  rw [show HasAllLadders=(fun x => ∀ r, ∃ n k, weakLadderHit (ladderTail^[r] x) n k) from rfl,
    ae_all_iff]
  intro r
  exact (p.ladderTail_preserving.iterate r).quasiMeasurePreserving.ae p.ae_weakLadderHit


lemma ladderTime_step_level {x : ℕ → ℕ} (hx : HasAllLadders x) (r : ℕ) :
    integerSum x (ladderTime x (r+1))-integerSum x (ladderTime x r)=
      (renewalIncrement r x:ℤ) := by
  obtain ⟨n,k,h⟩ := hx r
  have hidx := ladderIndex_eq_of_hit h
  have hval := ladderOvershoot_of_hit h
  change _=(ladderOvershoot (ladderTail^[r] x):ℤ)
  rw [hval,ladderTime,hidx,← integerSum_shift,← ladderTail_iterate]
  exact h.2


lemma ladderTime_between {x : ℕ → ℕ} (hx : HasAllLadders x) (r k : ℕ)
    (hlo : ladderTime x r<k) (hhi : k<ladderTime x (r+1)) :
    integerSum x k < integerSum x (ladderTime x r) := by
  obtain ⟨n,j,h⟩ := hx r
  have hidx := ladderIndex_eq_of_hit h
  have hhi' : k<ladderTime x r+(n+1) := by simpa only [ladderTime,hidx] using hhi
  have hs := h.1 (k-ladderTime x r) (by omega) (by omega)
  rw [ladderTail_iterate,integerSum_shift,Nat.add_sub_of_le hlo.le] at hs
  omega


lemma ladderTime_enumeration {x : ℕ → ℕ} (hx : HasAllLadders x) :
    LadderEnumeration (integerSum x) (ladderTime x) := by
  refine ⟨rfl,ladderTime_strictMono x,?_,ladderTime_between hx⟩
  apply monotone_nat_of_le_succ
  intro r
  have := ladderTime_step_level hx r
  dsimp only [Function.comp_apply]
  omega


lemma ladderTime_level_sum {x : ℕ → ℕ} (hx : HasAllLadders x) (r : ℕ) :
    integerSum x (ladderTime x r)=∑ i ∈ Finset.range r,(renewalIncrement i x:ℤ) := by
  induction r with
  | zero => simp [integerSum]
  | succ r ih =>
    rw [Finset.sum_range_succ,← ih]
    have := ladderTime_step_level hx r
    omega


lemma linear_remainder_of_ratio {L : ℕ → ℝ} {ν ε : ℝ} (hν : 0<ν) (hε : 0<ε)
    (hL : ∀ r, 0 ≤ L r) (ht : Tendsto (fun r : ℕ => L r/(r:ℝ)) atTop (𝓝 ν)) :
    ∃ A : ℕ, ∀ r, |L r-ν*r| ≤ ε*L r+A := by
  let δ := min (ε*ν/2) (ν/2)
  have hδ : 0<δ := lt_min (by positivity) (by positivity)
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((Metric.tendsto_nhds.mp ht) δ hδ)
  have hlarge (r : ℕ) (hr : N+1 ≤ r) : |L r-ν*r| ≤ ε*L r := by
    have hr0 : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
    have h := hN r (by omega)
    rw [Real.dist_eq,abs_sub_lt_iff] at h
    have hlo : ν/2*(r:ℝ) ≤ L r := by
      have hδν : δ ≤ ν/2 := min_le_right _ _
      have hh : ν/2 ≤ L r/(r:ℝ) := by linarith
      exact (le_div_iff₀ hr0).mp hh
    have he : |L r-ν*r| ≤ δ*r := by
      have hh : |L r/(r:ℝ)-ν| ≤ δ := abs_le.mpr ⟨by linarith,by linarith⟩
      have heq : L r/(r:ℝ)-ν=(L r-ν*r)/(r:ℝ) := by field_simp
      rw [heq,abs_div,abs_of_pos hr0] at hh
      exact (div_le_iff₀ hr0).mp hh
    exact he.trans (by have hh := min_le_left (ε*ν/2) (ν/2); nlinarith)
  obtain ⟨A,hA⟩ := exists_nat_ge (∑ r ∈ Finset.range (N+1),|L r-ν*r|)
  refine ⟨A,fun r => ?_⟩
  by_cases hr : N+1 ≤ r
  · exact (hlarge r hr).trans (le_add_of_nonneg_right (Nat.cast_nonneg A))
  · have hh : |L r-ν*r| ≤ ∑ k ∈ Finset.range (N+1),|L k-ν*k| :=
      Finset.single_le_sum (f := fun k => |L k-ν*k|) (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (show r<N+1 by omega))
    exact (hh.trans hA).trans (le_add_of_nonneg_left (mul_nonneg hε.le (hL r)))


lemma uniform_remainder_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (L : ℕ → Ω → ℝ) (hL : ∀ r, Measurable (L r))
    (ν ε : ℝ) (hae : ∀ᵐ x ∂μ, ∃ A : ℕ, ∀ r, |L r x-ν*r| ≤ ε*L r x+A) :
    Tendsto (fun A : ℕ => μ {x | ∃ r, ε*L r x+A < |L r x-ν*r|}) atTop (𝓝 0) := by
  let E : ℕ → Set Ω := fun A => {x | ∃ r, ε*L r x+A < |L r x-ν*r|}
  have hm (A : ℕ) : MeasurableSet (E A) := by
    dsimp [E]
    simp only [ofPred_exists]
    exact MeasurableSet.iUnion fun r => measurableSet_lt
      ((hL r).const_mul ε |>.add_const A) (((hL r).sub_const (ν*r)).abs)
  have hanti : Antitone E := by
    intro A B hAB x hx
    obtain ⟨r,hr⟩ := hx
    exact ⟨r,lt_of_le_of_lt (add_le_add le_rfl (Nat.cast_le.mpr hAB)) hr⟩
  have hz : μ (⋂ A, E A)=0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hae] with x hx
    obtain ⟨A,hA⟩ := hx
    intro hmem
    obtain ⟨r,hr⟩ := Set.mem_iInter.mp hmem A
    exact not_lt_of_ge (hA r) hr
  simpa only [hz,Function.comp_def,E] using tendsto_measure_iInter_atTop (μ := μ) (fun A => (hm A).nullMeasurableSet)
    hanti ⟨0,measure_ne_top _ _⟩


lemma integrable_neg_exp_nat {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Y : Ω → ℕ) (hY : Measurable Y) :
    Integrable (fun x => Real.exp (-(Y x:ℝ))) μ := by
  apply Integrable.of_bound ((measurable_of_countable (fun k : ℕ => Real.exp (-(k:ℝ)))).comp hY).aestronglyMeasurable 1
  filter_upwards with x
  dsimp only [Function.comp_apply]
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _))


lemma nat_laplace_lt_one {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Y : Ω → ℕ) (hY : Measurable Y)
    (hint : Integrable (fun x => (Y x:ℝ)) μ) (hmean : 0 < ∫ x,(Y x:ℝ) ∂μ) :
    0 < (∫ x,Real.exp (-(Y x:ℝ)) ∂μ) ∧ (∫ x,Real.exp (-(Y x:ℝ)) ∂μ)<1 := by
  have hi := integrable_neg_exp_nat μ Y hY
  have hle : (fun x => Real.exp (-(Y x:ℝ))) ≤ᵐ[μ] fun _ => 1 :=
    ae_of_all _ fun _ => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg _))
  refine ⟨integral_exp_pos hi,lt_of_le_of_ne ?_ ?_⟩
  · simpa using integral_mono_ae hi (integrable_const (1:ℝ)) hle
  · intro he
    have he' : (∫ x,Real.exp (-(Y x:ℝ)) ∂μ)=∫ _ : Ω,(1:ℝ) ∂μ := by simpa using he
    have hae := (integral_eq_iff_of_ae_le hi (integrable_const (1:ℝ)) hle).mp he'
    have hz : (fun x => (Y x:ℝ)) =ᵐ[μ] 0 := by
      filter_upwards [hae] with x hx
      have : -(Y x:ℝ)=0 := (Real.exp_eq_one_iff _).mp hx
      simpa using neg_eq_zero.mp this
    have : (∫ x,(Y x:ℝ) ∂μ)=0 := (integral_eq_zero_iff_of_nonneg (fun _ => Nat.cast_nonneg _) hint).mpr hz
    linarith


lemma iid_nat_laplace_sum {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℕ) (hY : ∀ i, Measurable (Y i))
    (hind : iIndepFun Y μ) (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) (n : ℕ) :
    (∫ x,Real.exp (-(∑ i ∈ Finset.range n,(Y i x:ℝ))) ∂μ)=
      (∫ x,Real.exp (-(Y 0 x:ℝ)) ∂μ)^n := by
  let Z : Fin n → Ω → ℝ := fun i x => Real.exp (-(Y i x:ℝ))
  have hZ : iIndepFun Z μ := (hind.precomp Fin.val_injective).comp
    (fun (_ : Fin n) (k : ℕ) => Real.exp (-(k:ℝ))) (fun _ => measurable_of_countable _)
  have he : ∀ x, Real.exp (-(∑ i ∈ Finset.range n,(Y i x:ℝ)))=∏ i : Fin n,Z i x := by
    intro x
    rw [← Finset.sum_neg_distrib,Real.exp_sum]
    exact (Fin.prod_univ_eq_prod_range _ n).symm
  simp_rw [he]
  rw [hZ.integral_fun_prod_eq_prod_integral (fun i =>
    ((measurable_of_countable (fun k : ℕ => Real.exp (-(k:ℝ)))).comp (hY i)).aestronglyMeasurable)]
  have hm (i : Fin n) : (∫ x,Z i x ∂μ)=∫ x,Real.exp (-(Y 0 x:ℝ)) ∂μ :=
    ((hident i).comp (measurable_of_countable (fun k : ℕ => Real.exp (-(k:ℝ))))).integral_eq
  simp_rw [hm]
  simp


lemma iid_nat_lower_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (Y : ℕ → Ω → ℕ) (hY : ∀ i, Measurable (Y i))
    (hind : iIndepFun Y μ) (hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hint : Integrable (fun x => (Y 0 x:ℝ)) μ) (hmean : 0 < ∫ x,(Y 0 x:ℝ) ∂μ) :
    ∃ c ρ : ℝ, 0<c ∧ 0<ρ ∧ ρ<1 ∧ ∀ n : ℕ,
      μ {x | (∑ i ∈ Finset.range n,(Y i x:ℝ)) ≤ c*n} ≤ ENNReal.ofReal (ρ^n) := by
  let q := ∫ x,Real.exp (-(Y 0 x:ℝ)) ∂μ
  obtain ⟨hq0,hq1⟩ := nat_laplace_lt_one μ (Y 0) (hY 0) hint hmean
  change 0<q at hq0
  change q<1 at hq1
  let c := -Real.log q/2
  have hc : 0<c := by
    dsimp [c]
    have : Real.log q<0 := Real.log_neg hq0 hq1
    linarith
  let ρ := Real.exp (-c)
  have hr0 : 0<ρ := Real.exp_pos _
  have hr1 : ρ<1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hprod : Real.exp c*q=ρ := by
    change Real.exp c*q=Real.exp (-c)
    rw [← Real.exp_log hq0,← Real.exp_add]
    congr 1
    dsimp [c]
    ring
  refine ⟨c,ρ,hc,hr0,hr1,fun n => ?_⟩
  let F : Ω → ℝ := fun x => Real.exp (-(∑ i ∈ Finset.range n,(Y i x:ℝ)))
  have hm : Measurable F := by
    dsimp [F]
    fun_prop
  have hi : Integrable F μ := by
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    filter_upwards with x
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Finset.sum_nonneg fun i _ => Nat.cast_nonneg _))
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ fun x => (Real.exp_pos _).le) hi (Real.exp (-c*n))
  have he : {x | Real.exp (-c*n) ≤ F x}=
      {x | (∑ i ∈ Finset.range n,(Y i x:ℝ)) ≤ c*n} := by
    ext x
    simp only [Set.mem_ofPred_eq,F,Real.exp_le_exp,neg_mul,neg_le_neg_iff]
  rw [he,iid_nat_laplace_sum μ Y hY hind hident n] at hmark
  have hp : μ.real {x | (∑ i ∈ Finset.range n,(Y i x:ℝ)) ≤ c*n} ≤ ρ^n := by
    have heq : Real.exp (-c*n)*ρ^n=q^n := by
      rw [← hprod,mul_pow,← Real.exp_nat_mul]
      rw [← mul_assoc,← Real.exp_add]
      have : -c*(n:ℝ)+(n:ℝ)*c=0 := by ring
      rw [this,Real.exp_zero,one_mul]
    rw [← heq] at hmark
    exact (mul_le_mul_iff_right₀ (Real.exp_pos _)).mp hmark
  have hp' := ENNReal.ofReal_le_ofReal hp
  rwa [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)] at hp'


def renewalLevel (r : ℕ) (x : ℕ → ℕ) : ℝ :=
  ∑ i ∈ Finset.range r,(renewalIncrement i x:ℝ)


lemma measurable_renewalLevel (r : ℕ) : Measurable (renewalLevel r) := by
  unfold renewalLevel
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_of_countable (fun k : ℕ => (k:ℝ))).comp (measurable_renewalIncrement i)


lemma renewalLevel_nonneg (r : ℕ) (x : ℕ → ℕ) : 0 ≤ renewalLevel r x :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _


lemma CriticalEvenOffspring.renewal_uniform_remainder (p : CriticalEvenOffspring)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᵐ x ∂p.streamLaw, ∃ A : ℕ, ∀ r,
      |renewalLevel r x-(p.variance/2)*r| ≤ ε*renewalLevel r x+A := by
  filter_upwards [p.renewal_strong_law] with x hx
  exact linear_remainder_of_ratio (half_pos p.variance_pos) hε
    (fun r => renewalLevel_nonneg r x) hx


lemma CriticalEvenOffspring.renewal_remainder_probability (p : CriticalEvenOffspring)
    {ε : ℝ} (hε : 0<ε) :
    Tendsto (fun A : ℕ => p.streamLaw {x | ∃ r,
      ε*renewalLevel r x+A < |renewalLevel r x-(p.variance/2)*r|}) atTop (𝓝 0) :=
  uniform_remainder_probability p.streamLaw renewalLevel measurable_renewalLevel
    (p.variance/2) ε (p.renewal_uniform_remainder hε)


lemma CriticalEvenOffspring.renewal_lower_tail (p : CriticalEvenOffspring) :
    ∃ c ρ : ℝ, 0<c ∧ 0<ρ ∧ ρ<1 ∧ ∀ m : ℕ,
      p.streamLaw {x | renewalLevel m x ≤ c*m} ≤ ENNReal.ofReal (ρ^m) := by
  have hint : Integrable (fun x => (renewalIncrement 0 x:ℝ)) p.streamLaw :=
    ((p.renewal_hasLaw 0).measurePreserving (measurable_renewalIncrement 0)).integrable_comp_of_integrable
      p.ladder_integrable
  have hm : (∫ x,(renewalIncrement 0 x:ℝ) ∂p.streamLaw)=p.variance/2 :=
    ((p.renewal_hasLaw 0).integral_comp
      (measurable_of_countable (fun k : ℕ => (k:ℝ))).aestronglyMeasurable).trans p.ladder_integral
  exact iid_nat_lower_tail p.streamLaw renewalIncrement measurable_renewalIncrement p.renewal_iid
    (fun i => (p.renewal_hasLaw i).identDistrib (p.renewal_hasLaw 0)) hint
    (by rw [hm]; exact half_pos p.variance_pos)


lemma ladderTime_level_real {x : ℕ → ℕ} (hx : HasAllLadders x) (r : ℕ) :
    (integerSum x (ladderTime x r):ℝ)=renewalLevel r x := by
  rw [ladderTime_level_sum hx]
  simp only [Int.cast_sum,Int.cast_natCast,renewalLevel]


lemma record_count_remainder {x : ℕ → ℕ} (hx : HasAllLadders x)
    (ν ε A : ℝ) (h : ∀ r, |renewalLevel r x-ν*r| ≤ ε*renewalLevel r x+A) (n : ℕ) :
    |(integerSum x (ladderTime x (renewalCount (ladderTime x) n)):ℝ)-
      ν*(weakRecords (integerSum x) n).card| ≤
      ε*(integerSum x (ladderTime x (renewalCount (ladderTime x) n)):ℝ)+A := by
  rw [(ladderTime_enumeration hx).card_records,ladderTime_level_real hx]
  exact h _


def reverseRecords {α : Type*} [LinearOrder α] (S : ℕ → α) (a b : ℕ) : Finset ℕ :=
  (Finset.Ico a b).filter fun j => ∀ r, j ≤ r → r ≤ b → S j ≤ S r


def recordHeight {α : Type*} [LinearOrder α] (S : ℕ → α) (a b : ℕ) : ℕ :=
  (reverseRecords S a b).card


@[simp] lemma mem_reverseRecords {α : Type*} [LinearOrder α] (S : ℕ → α) (a b j : ℕ) :
    j ∈ reverseRecords S a b ↔ a ≤ j ∧ j < b ∧ ∀ r, j ≤ r → r ≤ b → S j ≤ S r := by
  simp only [reverseRecords, Finset.mem_filter, Finset.mem_Ico, and_assoc]


lemma exists_first_path_minimum {α : Type*} [LinearOrder α] (S : ℕ → α)
    {a b : ℕ} (hab : a ≤ b) :
    ∃ i, a ≤ i ∧ i ≤ b ∧ (∀ r, a ≤ r → r ≤ b → S i ≤ S r) ∧
      ∀ r, a ≤ r → r < i → S i < S r := by
  classical
  have hex : ∃ i, a ≤ i ∧ i ≤ b ∧ ∀ r, a ≤ r → r ≤ b → S i ≤ S r := by
    obtain ⟨i,hi,hmin⟩ := (Finset.Icc a b).exists_min_image S ⟨a,Finset.mem_Icc.mpr ⟨le_rfl,hab⟩⟩
    exact ⟨i,(Finset.mem_Icc.mp hi).1,(Finset.mem_Icc.mp hi).2,
      fun r ha hb => hmin r (Finset.mem_Icc.mpr ⟨ha,hb⟩)⟩
  refine ⟨Nat.find hex,(Nat.find_spec hex).1,(Nat.find_spec hex).2.1,
    (Nat.find_spec hex).2.2,?_⟩
  intro r hra hri
  by_contra hn
  have hr : r ≤ b := le_trans (le_of_lt hri) (Nat.find_spec hex).2.1
  exact Nat.find_min hex hri ⟨hra,hr,fun k hka hkb =>
    (le_of_not_gt hn).trans ((Nat.find_spec hex).2.2 k hka hkb)⟩


lemma reverseRecords_at_first_minimum {α : Type*} [LinearOrder α] (S : ℕ → α)
    {a b i : ℕ} (hai : a ≤ i) (hib : i ≤ b)
    (hmin : ∀ r, a ≤ r → r ≤ b → S i ≤ S r)
    (hfirst : ∀ r, a ≤ r → r < i → S i < S r) :
    reverseRecords S 0 i = (reverseRecords S 0 b).filter (fun j => j < a) := by
  ext j
  simp only [mem_reverseRecords, Finset.mem_filter]
  constructor
  · rintro ⟨h0,hji,hrec⟩
    have hja : j < a := by
      by_contra hn
      exact (not_le_of_gt (hfirst j (by omega) hji)) (hrec i hji.le le_rfl)
    refine ⟨⟨h0,lt_of_lt_of_le hji hib,?_⟩,hja⟩
    intro r hjr hrb
    by_cases hri : r ≤ i
    · exact hrec r hjr hri
    · exact (hrec i hji.le le_rfl).trans (hmin r (by omega) hrb)
  · rintro ⟨⟨h0,hjb,hrec⟩,hja⟩
    exact ⟨h0,lt_of_lt_of_le hja hai,fun r hjr hri => hrec r hjr (hri.trans hib)⟩


lemma reverseRecords_split {α : Type*} [LinearOrder α] (S : ℕ → α)
    {a b : ℕ} (_hab : a ≤ b) :
    reverseRecords S 0 b =
      ((reverseRecords S 0 b).filter (fun j => j < a)) ∪ reverseRecords S a b := by
  ext j
  simp only [Finset.mem_union,Finset.mem_filter,mem_reverseRecords]
  constructor
  · intro hj
    by_cases hja : j < a
    · exact Or.inl ⟨hj,hja⟩
    · exact Or.inr ⟨by omega,hj.2⟩
  · rintro (⟨hj,_⟩ | hj)
    · exact hj
    · exact ⟨Nat.zero_le j,hj.2⟩


lemma reverseRecords_shared_prefix_subset {α : Type*} [LinearOrder α] (S : ℕ → α)
    {a b r : ℕ} (har : a ≤ r) (hrb : r ≤ b) :
    (reverseRecords S 0 b).filter (fun j => j < a) ⊆ reverseRecords S 0 r := by
  intro j hj
  obtain ⟨hj,hja⟩ := Finset.mem_filter.mp hj
  obtain ⟨h0,hjb,hrec⟩ := (mem_reverseRecords ..).mp hj
  exact (mem_reverseRecords ..).mpr
    ⟨h0,lt_of_lt_of_le hja har,fun k hjk hkr => hrec k hjk (hkr.trans hrb)⟩


theorem recordHeight_interval_identity {α : Type*} [LinearOrder α] (S : ℕ → α)
    {a b : ℕ} (hab : a ≤ b) :
    ∃ i, a ≤ i ∧ i ≤ b ∧
      (∀ r, a ≤ r → r ≤ b → recordHeight S 0 i ≤ recordHeight S 0 r) ∧
      recordHeight S 0 b = recordHeight S 0 i + recordHeight S a b := by
  classical
  obtain ⟨i,hai,hib,hmin,hfirst⟩ := exists_first_path_minimum S hab
  have he := reverseRecords_at_first_minimum S hai hib hmin hfirst
  refine ⟨i,hai,hib,?_,?_⟩
  · intro r har hrb
    unfold recordHeight
    rw [he]
    exact Finset.card_le_card (reverseRecords_shared_prefix_subset S har hrb)
  · unfold recordHeight
    rw [he]
    nth_rw 1 [reverseRecords_split S hab]
    apply Finset.card_union_of_disjoint
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    have hja := (Finset.mem_filter.mp hj).2
    have haj := ((mem_reverseRecords ..).mp hj').1
    omega

end FKCRT.TreeCoding
end

end OAI
