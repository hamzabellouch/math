import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Comparison.HatPartition

namespace OAI

noncomputable section
namespace DirectComparison
open Pureness CurrentMain Filter Topology
open scoped ComplexOrder

variable {D : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma finite_runs_exhaust {I : Type*} (Γ : I → TracialState D)
    {x : D} {ε δ κ : ℝ} (hκ : 0 < κ)
    (hrun : ∀ (u : D) (_ : IsStarProjection u), ∃ P : ProjectionPacking u,
      P.ScalarGood x ε ∧ ∀ i, δ < ((Γ i).functional u).re → κ ≤ ((Γ i).functional P.total).re)
    (q : D) (hq : IsStarProjection q) :
    ∃ P : ProjectionPacking q, P.ScalarGood x ε ∧
      ∀ i, ((Γ i).functional P.residual).re ≤ δ := by
  classical
  have hiter (n : ℕ) : ∃ P : ProjectionPacking q, P.ScalarGood x ε ∧
      ∀ i, δ < ((Γ i).functional P.residual).re →
        (n:ℝ)*κ ≤ ((Γ i).functional P.total).re := by
    induction n with
    | zero =>
      refine ⟨ProjectionPacking.empty hq,ProjectionPacking.empty_good hq x ε,?_⟩
      intro _ _; simp
    | succ n ih =>
      obtain ⟨P,hP,hPi⟩ := ih
      obtain ⟨Q,hQ,hQi⟩ := hrun P.residual (P.residual_projection hq)
      refine ⟨P.append hq Q,P.append_good hq Q hP hQ,?_⟩
      intro i hi
      have hiP : δ < ((Γ i).functional P.residual).re :=
        hi.trans_le (trace_re_mono _ (P.residual_append_le hq Q))
      have h1 := hPi i hiP
      have h2 := hQi i hiP
      rw [ProjectionPacking.append_total,map_add,Complex.add_re,Nat.cast_add,Nat.cast_one]
      nlinarith
  obtain ⟨K,hK⟩ := exists_nat_gt (1/κ)
  obtain ⟨P,hP,hPi⟩ := hiter K
  refine ⟨P,hP,?_⟩
  intro i
  by_contra hi
  have h := hPi i (lt_of_not_ge hi)
  have h1 := trace_projection_le_one (Γ i) P.total_projection
  have hK' : 1 < (K:ℝ)*κ := (div_lt_iff₀ hκ).mp hK
  linarith

def SpectralProjectionSupply {I : Type*} (Γ : I → TracialState D) : Prop :=
  ∀ (h : D), 0 ≤ h → ‖h‖ ≤ 1 → ∀ α : ℝ, 0 < α → α < 1 →
    ∃ p : D, IsStarProjection p ∧ directCutoff α h*p=p ∧ p*directCutoff α h=p ∧
      ∀ i, (Γ i).functional p=(Γ i).functional (directPositiveCut α h)

lemma localized_projection {I : Type*} (Γ : I → TracialState D)
    (hsupply : SpectralProjectionSupply Γ) {v x : D} (hv : IsStarProjection v)
    (hx : IsSelfAdjoint x) (hxn : ‖x‖ ≤ 1) {f : ℝ → ℝ}
    (hf : Continuous f) (hf01 : ∀ t ∈ Set.Icc (-1:ℝ) 1, f t ∈ Set.Icc 0 1)
    {ε μ α : ℝ} (hε : 0 ≤ ε) (hα : 0 < α) (hα1 : α < 1)
    (hsupp : ∀ t ∈ Set.Icc (-1:ℝ) 1, f t ≠ 0 → |t-μ| ≤ ε) :
    ∃ p : D, IsStarProjection p ∧ p ≤ v ∧ ‖p*x*p-μ • p‖ ≤ ε ∧
      ∀ i, ((Γ i).functional (cornerCFC hv x f)).re-α ≤ ((Γ i).functional p).re := by
  have hy := cornerCFC_nonneg hv hx hxn hf (fun t ht => (hf01 t ht).1)
  obtain ⟨p,hp,hkp,hpk,hpt⟩ := hsupply (cornerCFC hv x f) hy
    (cornerCFC_norm_le_one hv hx hxn hf01) α hα hα1
  obtain ⟨hvp,hpv,hn⟩ := localized_cutoff_compression hv hp hx hxn hf hf01 hα hε hsupp hkp hpk
  refine ⟨p,hp,(hp.le_iff_mul_eq_left hv).mpr hpv,hn,?_⟩
  intro i
  rw [hpt]
  exact positiveCut_trace_lower (Γ i) hy hα.le

theorem finite_scalar_single {I : Type*} (Γ : I → TracialState D)
    (hsupply : SpectralProjectionSupply Γ) {x : D}
    (hx : IsSelfAdjoint x) (hxn : ‖x‖ ≤ 1) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (q : D) (hq : IsStarProjection q) :
    ∃ P : ProjectionPacking q, P.ScalarGood x ε ∧
      ∀ i, ((Γ i).functional P.residual).re ≤ δ := by
  classical
  let d := min δ (1/2:ℝ)
  have hd : 0 < d := lt_min hδ (by norm_num)
  obtain ⟨m,hm,μ,f,hμ,hf,hf01,hsum,hsupp⟩ := exists_localized_partition hε
  have hmR : 0 < (m:ℝ) := by exact_mod_cast hm
  let β := d/(4*m)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβ1 : β < 1 := by
    have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
    have hd1 : d ≤ 1/2 := min_le_right _ _
    dsimp [β]; apply (div_lt_one (by positivity)).mpr; linarith
  obtain ⟨κ,hκ,hκβ,hmove⟩ := uniform_moving_corner_bound (D := D) f hf hβ
  have hrun (u : D) (hu : IsStarProjection u) : ∃ P : ProjectionPacking u,
      P.ScalarGood x ε ∧ ∀ i, d < ((Γ i).functional u).re → κ ≤ ((Γ i).functional P.total).re := by
    obtain ⟨P,hP,hPi⟩ := scalar_run Γ f μ hμ
      (fun i u v hu hv hvu ht j => hmove (Γ i) u v x hu hv hvu hx hxn ht j)
      (fun v hv j => localized_projection Γ hsupply hv hx hxn (hf j)
        (fun t _ => hf01 j t) hε.le hβ hβ1 (hsupp j)) u hu Finset.univ
    refine ⟨P,hP,?_⟩
    intro i hi
    by_contra hnot
    have hsmall : ((Γ i).functional P.total).re < κ := lt_of_not_ge hnot
    have htrace : (∑ j, ((Γ i).functional (cornerCFC hu x (f j))).re) = ((Γ i).functional u).re := by
      have h := congrArg (fun z => ((Γ i).functional z).re) (sum_cornerCFC hu hx f hf hsum)
      simpa only [map_sum,Complex.re_sum] using h
    have hb := Finset.sum_le_sum (fun j (hj : j ∈ Finset.univ) => hPi i hsmall j hj)
    rw [htrace,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hb
    have hpβ : ((Γ i).functional P.total).re < β := hsmall.trans_le hκβ
    have hβeq : (m:ℝ)*β=d/4 := by dsimp [β]; field_simp
    nlinarith
  obtain ⟨P,hP,hPi⟩ := finite_runs_exhaust Γ hκ hrun q hq
  exact ⟨P,hP,fun i => (hPi i).trans (min_le_left _ _)⟩

omit [PartialOrder D] [StarOrderedRing D] in
lemma compression_persist_real {p q : D} (hp : IsStarProjection p)
    (hpq : p*q=p) (hqp : q*p=p) (x : D) (μ : ℝ) :
    ‖p*x*p-μ • p‖ ≤ ‖q*x*q-μ • q‖ := by
  have he : p*(q*x*q-μ • q)*p=p*x*p-μ • p := by
    rw [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
    simp only [←mul_assoc,hpq,hp.isIdempotentElem.eq]
    rw [mul_assoc (p*x),hqp]
  rw [←he]
  exact compress_norm_le hp _

lemma ProjectionPacking.refine_good {q x : D} {ε : ℝ} (P : ProjectionPacking q)
    (Q : ∀ i : P.Index, ProjectionPacking (P.piece i)) (hP : P.ScalarGood x ε) :
    (P.refine Q).ScalarGood x ε := by
  rintro ⟨i,j⟩
  obtain ⟨μ,hμ,hx⟩ := hP i
  refine ⟨μ,hμ,?_⟩
  exact (compression_persist_real ((Q i).projection j)
    (((Q i).projection j).le_iff_mul_eq_left (P.projection i) |>.mp ((Q i).piece_le j))
    (((Q i).projection j).le_iff_mul_eq_right (P.projection i) |>.mp ((Q i).piece_le j)) x μ).trans hx

theorem finite_scalar_family {I J : Type*} (Γ : I → TracialState D)
    (hsupply : SpectralProjectionSupply Γ) (x : J → D) (s : Finset J)
    (hx : ∀ j ∈ s, IsSelfAdjoint (x j)) (hxn : ∀ j ∈ s, ‖x j‖ ≤ 1)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (q : D) (hq : IsStarProjection q) :
    ∃ P : ProjectionPacking q, (∀ j ∈ s, P.ScalarGood (x j) ε) ∧
      ∀ i, ((Γ i).functional P.residual).re ≤ δ := by
  classical
  induction s using Finset.induction_on generalizing δ with
  | empty =>
    refine ⟨ProjectionPacking.singleton hq le_rfl,by simp,?_⟩
    intro i
    simpa only [ProjectionPacking.residual,ProjectionPacking.singleton_total,sub_self,map_zero,Complex.zero_re] using hδ.le
  | @insert j s hjs ih =>
    obtain ⟨P,hP,hPi⟩ := ih (fun k hk => hx k (Finset.mem_insert_of_mem hk))
      (fun k hk => hxn k (Finset.mem_insert_of_mem hk)) (half_pos hδ)
    let a : ℝ := δ/(2*((Fintype.card P.Index:ℝ)+1))
    have ha : 0 < a := by dsimp [a]; positivity
    have hQ (i : P.Index) := finite_scalar_single Γ hsupply (hx j (Finset.mem_insert_self _ _))
      (hxn j (Finset.mem_insert_self _ _)) hε ha (P.piece i) (P.projection i)
    choose Q hQ hQi using hQ
    refine ⟨P.refine Q,?_,?_⟩
    · intro k hk
      rcases Finset.mem_insert.mp hk with hk | hk
      · subst k
        rintro ⟨i,l⟩
        exact hQ i l
      · exact P.refine_good Q (hP k hk)
    · intro i
      rw [ProjectionPacking.refine_residual,map_add,Complex.add_re,map_sum,Complex.re_sum]
      have hb := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hQi j i)
      rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hb
      have haeq : (2*((Fintype.card P.Index:ℝ)+1))*a=δ :=
        mul_div_cancel₀ δ (by positivity)
      have hn : 0 ≤ (Fintype.card P.Index:ℝ) := Nat.cast_nonneg _
      have hp := hPi i
      nlinarith

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)]
variable (U : Ultrafilter ℕ) (hfree : (U : Filter ℕ) ≤ atTop)
local notation "D₀" => FamilyUltrapower (fun τ : TracialState A => τ) U
local notation "Λ" => familyLimitTrace (fun τ : TracialState A => τ) U

include hfree in

theorem scalar_compressions (hsimple : TopologicallySimple A)
    (hinf : ¬FiniteDimensional ℂ A) (hcmp : StrictComparison A)
    {J : Type*} (x : J → D₀) (s : Finset J)
    (hx : ∀ j ∈ s, IsSelfAdjoint (x j)) (hxn : ∀ j ∈ s, ‖x j‖ ≤ 1)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (q : D₀) (hq : IsStarProjection q) :
    ∃ P : ProjectionPacking q, (∀ j ∈ s, P.ScalarGood (x j) ε) ∧
      ∀ i : ℕ → TracialState A, ((Λ i).functional P.residual).re ≤ δ := by
  exact finite_scalar_family Λ
    (fun h hh hhn α hα hα1 => projection_supply U hfree hsimple hinf hcmp h hh hhn α hα hα1)
    x s hx hxn hε hδ q hq

end DirectComparison
end

end OAI
