import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Bases
import Mathlib.Topology.DiscreteSubset
import OAI.NumberTheory.SiegelZeros.Characters.ConditionalPrimeBias
import OAI.NumberTheory.SiegelZeros.Determinants.NormalizedCompletion
import OAI.NumberTheory.SiegelZeros.EntireFunctions.IndexedProduct
import OAI.NumberTheory.SiegelZeros.EntireFunctions.ZeroShellBounds

namespace OAI

namespace SiegelZeros

section

namespace SiegelZerosAwei.W51

variable {q : ℕ} [NeZero q]

theorem analyticOrderAt_normalizedCompletion (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (s : ℂ) : analyticOrderAt (normalizedCompletion χ) s =
      analyticOrderAt (DirichletCharacter.completedLFunction χ) s := by
  change analyticOrderAt ((fun z : ℂ => (q : ℂ) ^ (z / 2)) *
    DirichletCharacter.completedLFunction χ) s = _
  rw [analyticOrderAt_mul ((differentiable_conductorFactor (q := q)).analyticAt s)
    ((DirichletCharacter.differentiable_completedLFunction hχ).analyticAt s)]
  rw [(analyticOrderAt_eq_zero (f := fun z : ℂ => (q : ℂ) ^ (z / 2)) (z₀ := s)).mpr
    (Or.inr (conductorFactor_ne_zero (q := q) s)), zero_add]

theorem analyticOrderAt_normalizedCompletion_ne_top (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (s : ℂ) : analyticOrderAt (normalizedCompletion χ) s ≠ ⊤ := by
  intro htop
  have ha : AnalyticOnNhd ℂ (normalizedCompletion χ) Set.univ :=
    fun z _ => (differentiable_normalizedCompletion χ hχ).analyticAt z
  have hz := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ s) (analyticOrderAt_eq_top.mp htop)
  exact normalizedCompletion_ne_zero_of_one_le_re χ hχ (s := 1) (by simp)
    (hz (Set.mem_univ 1))

theorem natCast_order_normalizedCompletion (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (s : ℂ) :
    (analyticOrderNatAt (normalizedCompletion χ) s : ℕ∞) =
      analyticOrderAt (normalizedCompletion χ) s :=
  Nat.cast_analyticOrderNatAt (analyticOrderAt_normalizedCompletion_ne_top χ hχ s)

theorem order_normalizedCompletion_pos (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hz : normalizedCompletion χ s = 0) :
    0 < analyticOrderNatAt (normalizedCompletion χ) s := by
  have hn : analyticOrderAt (normalizedCompletion χ) s ≠ 0 :=
    analyticOrderAt_ne_zero.mpr
      ⟨(differentiable_normalizedCompletion χ hχ).analyticAt s, hz⟩
  apply Nat.pos_of_ne_zero
  intro hzero
  apply hn
  rw [← natCast_order_normalizedCompletion χ hχ s, hzero]
  rfl

end SiegelZerosAwei.W51

end

section

namespace SiegelZerosAwei.W51

variable {q : ℕ} [NeZero q]

theorem rootNumber_ne_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprimitive : χ.IsPrimitive) : DirichletCharacter.rootNumber χ ≠ 0 := by
  intro hroot
  have h := normalizedCompletion_one_sub χ hprimitive 0
  simp only [sub_zero, hroot, zero_mul] at h
  exact normalizedCompletion_ne_zero_of_one_le_re χ hχ (s := 1) (by simp) h

theorem normalizedCompletion_zero_mem_strip (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprimitive : χ.IsPrimitive) {ρ : ℂ} (hzero : normalizedCompletion χ ρ = 0) :
    0 < ρ.re ∧ ρ.re < 1 := by
  constructor
  · by_contra hn
    have hχinv : χ⁻¹ ≠ 1 := by simpa only [ne_eq, inv_eq_one] using hχ
    have hs : 1 ≤ (1 - ρ).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have h := normalizedCompletion_one_sub χ hprimitive (1 - ρ)
    rw [sub_sub_cancel, hzero] at h
    exact (mul_ne_zero (rootNumber_ne_zero χ hχ hprimitive)
      (normalizedCompletion_ne_zero_of_one_le_re χ⁻¹ hχinv hs)) h.symm
  · by_contra hn
    exact normalizedCompletion_ne_zero_of_one_le_re χ hχ (le_of_not_gt hn) hzero

theorem LFunction_zero_of_normalizedCompletion_zero (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive) {ρ : ℂ}
    (hzero : normalizedCompletion χ ρ = 0) : DirichletCharacter.LFunction χ ρ = 0 :=
  (LFunction_zero_iff_normalizedCompletion_zero χ
    (normalizedCompletion_zero_mem_strip χ hχ hprimitive hzero).1).mpr hzero

end SiegelZerosAwei.W51

end

section

namespace SiegelZerosAwei.W51

variable {q : ℕ} [NeZero q]

def ZeroIndex (χ : DirichletCharacter ℂ q) : Type :=
  (ρ : {z : ℂ // normalizedCompletion χ z = 0}) ×
    Fin (analyticOrderNatAt (normalizedCompletion χ) ρ.val)

def zeroValue (χ : DirichletCharacter ℂ q) (i : ZeroIndex χ) : ℂ := i.1.val

theorem zeroValue_is_zero (χ : DirichletCharacter ℂ q) (i : ZeroIndex χ) :
    normalizedCompletion χ (zeroValue χ i) = 0 := i.1.property

theorem exists_zeroIndex_iff (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ) :
    (∃ i : ZeroIndex χ, zeroValue χ i = ρ) ↔ normalizedCompletion χ ρ = 0 := by
  constructor
  · rintro ⟨i, rfl⟩
    exact zeroValue_is_zero χ i
  · intro hz
    exact ⟨⟨⟨ρ, hz⟩, ⟨0, order_normalizedCompletion_pos χ hχ hz⟩⟩, rfl⟩

theorem exists_zeroIndex_of_real_zero (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {β : ℝ} (hβ : 0 < β) (hzero : DirichletCharacter.LFunction χ (β : ℂ) = 0) :
    ∃ i : ZeroIndex χ, zeroValue χ i = (β : ℂ) := by
  apply (exists_zeroIndex_iff χ hχ (β : ℂ)).mpr
  exact (LFunction_zero_iff_normalizedCompletion_zero χ (by simpa using hβ)).mp hzero

theorem zeroValue_mem_strip (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprimitive : χ.IsPrimitive) (i : ZeroIndex χ) :
    0 < (zeroValue χ i).re ∧ (zeroValue χ i).re < 1 :=
  normalizedCompletion_zero_mem_strip χ hχ hprimitive (zeroValue_is_zero χ i)

theorem zeroValue_contribution_nonneg (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprimitive : χ.IsPrimitive) (i : ZeroIndex χ) {s : ℝ} (hs : 1 < s) :
    0 ≤ (((s : ℂ) - zeroValue χ i)⁻¹).re :=
  W03.zero_contribution_nonneg hs (zeroValue_mem_strip χ hχ hprimitive i).2.le

end SiegelZerosAwei.W51

end

section

namespace SiegelZerosAwei.W51

open Filter Set
open scoped Topology

variable {q : ℕ} [NeZero q]

theorem normalizedCompletion_zeros_closed_discrete (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) :
    IsClosed {z : ℂ | normalizedCompletion χ z = 0} ∧
      IsDiscrete {z : ℂ | normalizedCompletion χ z = 0} := by
  have ha : AnalyticOnNhd ℂ (normalizedCompletion χ) univ :=
    fun z _ => (differentiable_normalizedCompletion χ hχ).analyticAt z
  have hne := ha.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ
  have hnot : ¬ EqOn (normalizedCompletion χ) 0 univ := by
    intro hz
    exact normalizedCompletion_ne_zero_of_one_le_re χ hχ (s := 1) (by simp)
      (hz (mem_univ 1))
  have hcompl : {z : ℂ | normalizedCompletion χ z = 0}ᶜ ∈ codiscrete ℂ :=
    hne.resolve_left hnot
  have h := compl_mem_codiscrete_iff.mp hcompl
  exact h

theorem finite_normalizedCompletion_zeros_in_compact (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ {z : ℂ | normalizedCompletion χ z = 0}).Finite := by
  obtain ⟨hc, hd⟩ := normalizedCompletion_zeros_closed_discrete χ hχ
  exact (hK.inter_right hc).finite (hd.mono inter_subset_right)

theorem finite_completedLFunction_zeros_in_compact (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ {z : ℂ | DirichletCharacter.completedLFunction χ z = 0}).Finite := by
  simpa only [normalizedCompletion_zero_iff] using
    finite_normalizedCompletion_zeros_in_compact χ hχ hK

theorem finite_zeroSubtype_preimage_compact (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {K : Set ℂ} (hK : IsCompact K) :
    ((Subtype.val : {z : ℂ // normalizedCompletion χ z = 0} → ℂ) ⁻¹' K).Finite := by
  obtain ⟨hc, hd⟩ := normalizedCompletion_zeros_closed_discrete χ hχ
  exact tendsto_cofinite_cocompact_iff.mp
    (hc.tendsto_coe_cofinite_of_isDiscrete hd) K hK

theorem finite_zeroIndex_fiber (χ : DirichletCharacter ℂ q)
    (ρ : {z : ℂ // normalizedCompletion χ z = 0}) :
    ((Sigma.fst : ZeroIndex χ → {z : ℂ // normalizedCompletion χ z = 0}) ⁻¹' {ρ}).Finite := by
  apply (Set.finite_range
    (fun k : Fin (analyticOrderNatAt (normalizedCompletion χ) ρ.val) =>
      (⟨ρ, k⟩ : ZeroIndex χ))).subset
  rintro ⟨r, k⟩ hr
  have heq : r = ρ := hr
  subst r
  exact ⟨k, rfl⟩

theorem finite_zeroIndex_preimage_compact (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) {K : Set ℂ} (hK : IsCompact K) :
    (zeroValue χ ⁻¹' K).Finite := by
  exact (finite_zeroSubtype_preimage_compact χ hχ hK).preimage'
    (fun ρ _ => finite_zeroIndex_fiber χ ρ)

theorem finite_zeroIndex_norm_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (R : ℝ) :
    {i : ZeroIndex χ | ‖zeroValue χ i‖ ≤ R}.Finite := by
  simpa only [Metric.closedBall, preimage_ofPred_eq, dist_zero_right] using
    (finite_zeroIndex_preimage_compact χ hχ (isCompact_closedBall (0 : ℂ) R))

theorem countable_zeroIndex (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Countable (ZeroIndex χ) := by
  let : DiscreteTopology {z : ℂ // normalizedCompletion χ z = 0} :=
    (normalizedCompletion_zeros_closed_discrete χ hχ).2.to_subtype
  let : Countable {z : ℂ // normalizedCompletion χ z = 0} :=
    TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  unfold ZeroIndex
  infer_instance

theorem zeroValue_tendsto_cofinite_cocompact (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Tendsto (zeroValue χ) cofinite (cocompact ℂ) :=
  tendsto_cofinite_cocompact_iff.mpr (fun _ hK => finite_zeroIndex_preimage_compact χ hχ hK)

theorem zeroValue_cofinite_far (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (R : ℝ) :
    ∀ᶠ i : ZeroIndex χ in cofinite, R ≤ ‖zeroValue χ i‖ :=
  (tendsto_atTop.mp
    (tendsto_norm_cocompact_atTop.comp (zeroValue_tendsto_cofinite_cocompact χ hχ))) R

theorem nonzeroZeros_cofinite_far (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (R : ℝ) :
    ∀ᶠ ρ : {z : ℂ // normalizedCompletion χ z = 0 ∧ z ≠ 0} in cofinite,
      R ≤ ‖ρ.val‖ := by
  have ht : Tendsto
      (Subtype.val : {z : ℂ // normalizedCompletion χ z = 0 ∧ z ≠ 0} → ℂ)
      cofinite (cocompact ℂ) := by
    apply tendsto_cofinite_cocompact_iff.mpr
    intro K hK
    have hfinite := (finite_normalizedCompletion_zeros_in_compact χ hχ hK).preimage
      (f := (Subtype.val : {z : ℂ // normalizedCompletion χ z = 0 ∧ z ≠ 0} → ℂ))
      Subtype.val_injective.injOn
    apply hfinite.subset
    intro ρ hρ
    exact ⟨hρ, ρ.property.1⟩
  exact (tendsto_atTop.mp (tendsto_norm_cocompact_atTop.comp ht)) R

end SiegelZerosAwei.W51

end

section

noncomputable section
namespace WeightedTorusJets.W63

def HadamardFormulaAt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℝ) : Prop :=
  Summable (fun i : SiegelZerosAwei.W51.ZeroIndex χ =>
    (((s : ℂ) - SiegelZerosAwei.W51.zeroValue χ i)⁻¹).re) ∧
  (-deriv χ.LFunction (s : ℂ) / χ.LFunction (s : ℂ)).re =
    (1 / 2 : ℝ) * Real.log ((q : ℝ) / Real.pi) +
    (1 / 2 : ℝ) *
      (SiegelZerosAwei.W52.gammaLogDerivative
        (((s + (parity χ : ℝ)) / 2 : ℝ) : ℂ)).re -
    ∑' i : SiegelZerosAwei.W51.ZeroIndex χ,
      (((s : ℂ) - SiegelZerosAwei.W51.zeroValue χ i)⁻¹).re

theorem HadamardFormulaAt.to_expansion {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hnp : χ ≠ 1) (hprimitive : χ.IsPrimitive)
    {β s : ℝ} (hβ : 0 < β) (hzero : χ.LFunction (β : ℂ) = 0)
    (hformula : HadamardFormulaAt χ s) : HadamardExpansionAt χ β s := by
  refine ⟨SiegelZerosAwei.W51.ZeroIndex χ, SiegelZerosAwei.W51.zeroValue χ,
    ?_, hformula.1, ?_, hformula.2⟩
  · intro i
    exact SiegelZerosAwei.W51.LFunction_zero_of_normalizedCompletion_zero
      χ hnp hprimitive (SiegelZerosAwei.W51.zeroValue_is_zero χ i)
  · exact SiegelZerosAwei.W51.exists_zeroIndex_of_real_zero χ hnp hβ hzero

end WeightedTorusJets.W63

end

end

section

namespace SiegelZerosAwei.W03

open Complex Real Metric

theorem entire_order_ne_top (f : ℂ → ℂ) (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (z : ℂ) : analyticOrderAt f z ≠ ⊤ := by
  intro hz
  have ha : AnalyticOnNhd ℂ f Set.univ := fun w _ => hf.analyticAt w
  have hall := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ z) (analyticOrderAt_eq_top.mp hz)
  exact h0 (hall (Set.mem_univ 0))

theorem divisor_eq_nat_order (f : ℂ → ℂ) (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    {U : Set ℂ} {z : ℂ} (hz : z ∈ U) :
    MeromorphicOn.divisor f U z = (analyticOrderNatAt f z : ℤ) := by
  rw [MeromorphicOn.divisor_apply (fun w _ => (hf.analyticAt w).meromorphicAt) hz,
    (hf.analyticAt z).meromorphicOrderAt_eq,
    ← Nat.cast_analyticOrderNatAt (entire_order_ne_top f hf h0 z)]
  simp

theorem jensen_identity_at_zero (f : ℂ → ℂ) (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    {r : ℝ} (hr : 0 < r) :
    (∑ᶠ u : ℂ, (MeromorphicOn.divisor f (closedBall 0 r) u : ℝ) *
      Real.log (r * ‖u‖⁻¹)) =
      circleAverage (fun z => Real.log ‖f z‖) 0 r - Real.log ‖f 0‖ := by
  have hj := MeromorphicOn.circleAverage_log_norm (f := f) (c := 0) hr.ne'
    (fun z _ => (hf.analyticAt z).meromorphicAt)
  have hd0 : MeromorphicOn.divisor f (closedBall 0 r) 0 = 0 := by
    rw [divisor_eq_nat_order f hf h0 (by simp [hr.le])]
    have ho : analyticOrderAt f 0 = 0 := analyticOrderAt_eq_zero.mpr (Or.inr h0)
    simp [analyticOrderNatAt, ho]
  rw [abs_of_pos hr, hd0, Int.cast_zero, zero_mul, add_zero,
    (hf.analyticAt 0).meromorphicTrailingCoeffAt_of_ne_zero h0] at hj
  simp only [zero_sub, norm_neg] at hj
  linarith

theorem circleAverage_log_norm_le (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    {r M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ z ∈ sphere (0 : ℂ) |r|, ‖f z‖ ≤ Real.exp M) :
    circleAverage (fun z => Real.log ‖f z‖) 0 r ≤ M := by
  apply circleAverage_mono_on_of_le_circle
    (MeromorphicOn.circleIntegrable_log_norm (fun z _ => (hf.analyticAt z).meromorphicAt))
  intro z hz
  by_cases hzero : f z = 0
  · simpa [hzero] using hM
  · have h := Real.log_le_log (norm_pos_iff.mpr hzero) (hbound z hz)
    simpa only [Real.log_exp] using h

theorem finite_zero_count_mul_log_two_le (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h0 : f 0 ≠ 0) (s : Finset ℂ) {R : ℝ} (hR : 0 < R)
    (hs : ∀ u ∈ s, u ≠ 0 ∧ ‖u‖ ≤ R) :
    (∑ u ∈ s, (analyticOrderNatAt f u : ℝ)) * Real.log 2 ≤
      circleAverage (fun z => Real.log ‖f z‖) 0 (2 * R) - Real.log ‖f 0‖ := by
  classical
  let D := MeromorphicOn.divisor f (closedBall 0 (2 * R))
  let j : ℂ → ℝ := fun u => (D u : ℝ) * Real.log ((2 * R) * ‖u‖⁻¹)
  have hDnonneg : ∀ u, 0 ≤ (D u : ℝ) := by
    intro u
    exact_mod_cast (show 0 ≤ D u from
      MeromorphicOn.AnalyticOnNhd.divisor_nonneg
        (show AnalyticOnNhd ℂ f (closedBall 0 (2 * R)) from
          fun z _ => hf.analyticAt z) u)
  have hjnonneg : ∀ u, 0 ≤ j u := by
    intro u
    by_cases huD : D u = 0
    · simp [j, huD]
    · have humem : u ∈ closedBall (0 : ℂ) (2 * R) :=
        D.supportWithinDomain huD
      have hunorm : ‖u‖ ≤ 2 * R := by simpa only [mem_closedBall, dist_zero_right] using humem
      by_cases hu0 : u = 0
      · simp [j, hu0]
      · apply mul_nonneg (hDnonneg u)
        apply Real.log_nonneg
        rw [← div_eq_mul_inv, le_div_iff₀ (norm_pos_iff.mpr hu0)]
        simpa using hunorm
  have hDfinite := D.finiteSupport (isCompact_closedBall (0 : ℂ) (2 * R))
  let t : Finset ℂ := hDfinite.toFinset ∪ s
  have hj_support : Function.support j ⊆ (t : Set ℂ) := by
    intro u hu
    apply Finset.mem_union_left
    apply hDfinite.mem_toFinset.mpr
    intro huD
    apply hu
    simp [j, huD]
  have hs_j : (∑ u ∈ s, (analyticOrderNatAt f u : ℝ)) * Real.log 2 ≤ ∑ u ∈ s, j u := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro u hu
    have hu0 := (hs u hu).1
    have hunorm := (hs u hu).2
    have humem : u ∈ closedBall (0 : ℂ) (2 * R) := by
      simp only [mem_closedBall, dist_zero_right]
      linarith
    have hDu : D u = (analyticOrderNatAt f u : ℤ) := divisor_eq_nat_order f hf h0 humem
    have hlog : Real.log 2 ≤ Real.log ((2 * R) * ‖u‖⁻¹) := by
      apply Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      rw [← div_eq_mul_inv, le_div_iff₀ (norm_pos_iff.mpr hu0)]
      linarith
    change (analyticOrderNatAt f u : ℝ) * Real.log 2 ≤ (D u : ℝ) * _
    rw [hDu, Int.cast_natCast]
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  calc
    _ ≤ ∑ u ∈ s, j u := hs_j
    _ ≤ ∑ u ∈ t, j u := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_union_right) (fun u _ _ => hjnonneg u)
    _ = ∑ᶠ u, j u := (finsum_eq_sum_of_support_subset j hj_support).symm
    _ = _ := jensen_identity_at_zero f hf h0 (by positivity)

section ActualZeroCount

variable {q : ℕ} [NeZero q]

noncomputable def zeroRootFinset (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (R : ℝ) :
    Finset {z : ℂ // W51.normalizedCompletion χ z = 0} :=
  (W51.finite_zeroSubtype_preimage_compact χ hχ
    (isCompact_closedBall (0 : ℂ) R)).toFinset

@[simp] theorem mem_zeroRootFinset (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (R : ℝ)
    (ρ : {z : ℂ // W51.normalizedCompletion χ z = 0}) :
    ρ ∈ zeroRootFinset χ hχ R ↔ ‖ρ.val‖ ≤ R := by
  simp only [zeroRootFinset, Set.Finite.mem_toFinset, Set.mem_preimage,
    mem_closedBall, dist_zero_right]

noncomputable def zeroIndexFinset (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (R : ℝ) :
    Finset (W51.ZeroIndex χ) :=
  (zeroRootFinset χ hχ R).sigma (fun _ => Finset.univ)

@[simp] theorem mem_zeroIndexFinset (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (R : ℝ)
    (i : W51.ZeroIndex χ) :
    i ∈ zeroIndexFinset χ hχ R ↔ ‖W51.zeroValue χ i‖ ≤ R := by
  unfold W51.ZeroIndex at i
  unfold zeroIndexFinset W51.ZeroIndex
  simp only [Finset.mem_sigma, Finset.mem_univ, and_true,
    mem_zeroRootFinset, W51.zeroValue]

theorem zeroIndex_ncard_eq_sum_orders (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (R : ℝ) :
    {i : W51.ZeroIndex χ | ‖W51.zeroValue χ i‖ ≤ R}.ncard =
      ∑ ρ ∈ zeroRootFinset χ hχ R, analyticOrderNatAt (W51.normalizedCompletion χ) ρ.val := by
  have heq : {i : W51.ZeroIndex χ | ‖W51.zeroValue χ i‖ ≤ R} =
      (zeroIndexFinset χ hχ R : Set (W51.ZeroIndex χ)) := by
    ext i
    exact (mem_zeroIndexFinset χ hχ R i).symm
  rw [heq, Set.ncard_coe_finset]
  unfold zeroIndexFinset W51.ZeroIndex
  rw [Finset.card_sigma]
  simp only [Finset.card_univ, Fintype.card_fin]

theorem actual_zero_count_jensen (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprimitive : χ.IsPrimitive) {R : ℝ} (hR : 0 < R) :
    ({i : W51.ZeroIndex χ | ‖W51.zeroValue χ i‖ ≤ R}.ncard : ℝ) * Real.log 2 ≤
      circleAverage (fun z => Real.log ‖W51.normalizedCompletion χ z‖) 0 (2 * R) -
        Real.log ‖W51.normalizedCompletion χ 0‖ := by
  classical
  let f := W51.normalizedCompletion χ
  have hf : Differentiable ℂ f := W51.differentiable_normalizedCompletion χ hχ
  have h0 : f 0 ≠ 0 := by
    intro hz
    have h := (W51.normalizedCompletion_zero_mem_strip χ hχ hprimitive hz).1
    simp at h
  let s : Finset ℂ := (zeroRootFinset χ hχ R).image Subtype.val
  have hs : ∀ u ∈ s, u ≠ 0 ∧ ‖u‖ ≤ R := by
    intro u hu
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hu
    refine ⟨?_, (mem_zeroRootFinset χ hχ R ρ).mp hρ⟩
    intro hρ0
    apply h0
    simpa only [hρ0] using ρ.property
  have hj := finite_zero_count_mul_log_two_le f hf h0 s hR hs
  have hcount : ({i : W51.ZeroIndex χ | ‖W51.zeroValue χ i‖ ≤ R}.ncard : ℝ) =
      ∑ u ∈ s, (analyticOrderNatAt f u : ℝ) := by
    rw [zeroIndex_ncard_eq_sum_orders χ hχ R, Nat.cast_sum]
    dsimp only [s]
    rw [Finset.sum_image Subtype.val_injective.injOn]
  rw [hcount]
  exact hj

theorem actual_zero_count_le_of_growth (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprimitive : χ.IsPrimitive) {C : ℝ} (hC : 0 ≤ C)
    (hgrowth : ∀ z : ℂ, ‖W51.normalizedCompletion χ z‖ ≤
      Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    {R : ℝ} (hR : 0 < R) :
    ({i : W51.ZeroIndex χ | ‖W51.zeroValue χ i‖ ≤ R}.ncard : ℝ) * Real.log 2 ≤
      C * (1 + 2 * R) * Real.log (2 + 2 * R) -
        Real.log ‖W51.normalizedCompletion χ 0‖ := by
  have havg := circleAverage_log_norm_le (W51.normalizedCompletion χ)
    (W51.differentiable_normalizedCompletion χ hχ)
    (r := 2 * R) (M := C * (1 + 2 * R) * Real.log (2 + 2 * R))
    (mul_nonneg (mul_nonneg hC (by linarith)) (Real.log_nonneg (by linarith))) (by
      intro z hz
      have hn : ‖z‖ = 2 * R := by
        simpa only [mem_sphere, dist_zero_right, abs_of_pos (show 0 < 2 * R by positivity)] using hz
      simpa only [hn] using hgrowth z)
  exact (actual_zero_count_jensen χ hχ hprimitive hR).trans (sub_le_sub_right havg _)

end ActualZeroCount

end SiegelZerosAwei.W03

end

section

namespace SiegelZerosAwei.W51

open Filter Set
open scoped Topology

variable {q : ℕ} [NeZero q]

noncomputable def canonicalProduct (χ : DirichletCharacter ℂ q) (z : ℂ) : ℂ :=
  ∏' i : ZeroIndex χ, W03.genusOneFactor (zeroValue χ i) z

noncomputable def deletedRootProduct (χ : DirichletCharacter ℂ q)
    (r : {z : ℂ // normalizedCompletion χ z = 0}) (z : ℂ) : ℂ :=
  ∏' i : {i : ZeroIndex χ // i.1 ≠ r}, W03.genusOneFactor (zeroValue χ i.val) z

def zeroRootFiberEquiv (χ : DirichletCharacter ℂ q)
    (r : {z : ℂ // normalizedCompletion χ z = 0}) :
    {i : ZeroIndex χ // i.1 = r} ≃
      Fin (analyticOrderNatAt (normalizedCompletion χ) r.val) where
  toFun i := i.property ▸ i.val.2
  invFun k := ⟨⟨r, k⟩, rfl⟩
  left_inv := by
    rintro ⟨⟨a, k⟩, h⟩
    cases h
    rfl
  right_inv := by intro k; rfl

theorem zeroRootFiber_tprod (χ : DirichletCharacter ℂ q)
    (r : {z : ℂ // normalizedCompletion χ z = 0}) (z : ℂ) :
    (∏' i : {i : ZeroIndex χ // i.1 = r}, W03.genusOneFactor (zeroValue χ i.val) z) =
      W03.genusOneFactor r.val z ^ analyticOrderNatAt (normalizedCompletion χ) r.val := by
  rw [← (zeroRootFiberEquiv χ r).symm.tprod_eq]
  simp only [zeroRootFiberEquiv, zeroValue]
  rw [tprod_fintype]
  simp

theorem analyticOrderAt_genusOneFactor {ρ : ℂ} (hρ : ρ ≠ 0) :
    analyticOrderAt (W03.genusOneFactor ρ) ρ = 1 := by
  apply ((W03.differentiable_genusOneFactor ρ).analyticAt ρ).analyticOrderAt_eq_natCast.mpr
  refine ⟨fun z : ℂ => -ρ⁻¹ * Complex.exp (z / ρ), ?_, ?_, ?_⟩
  · fun_prop
  · exact mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero hρ)) (Complex.exp_ne_zero _)
  · apply Filter.Eventually.of_forall
    intro z
    simp only [pow_one, smul_eq_mul, W03.genusOneFactor]
    field_simp [hρ]
    ring

theorem analyticOrderAt_genusOneFactor_pow {ρ : ℂ} (hρ : ρ ≠ 0) (n : ℕ) :
    analyticOrderAt (fun z => W03.genusOneFactor ρ z ^ n) ρ = (n : ℕ∞) := by
  rw [show (fun z => W03.genusOneFactor ρ z ^ n) = (W03.genusOneFactor ρ) ^ n from rfl,
    analyticOrderAt_pow ((W03.differentiable_genusOneFactor ρ).analyticAt ρ),
    analyticOrderAt_genusOneFactor hρ]
  simp

theorem canonicalProduct_split_root (χ : DirichletCharacter ℂ q)
    (r : {z : ℂ // normalizedCompletion χ z = 0}) (z : ℂ)
    (htail : Multipliable (fun i : {i : ZeroIndex χ // i.1 ≠ r} =>
      W03.genusOneFactor (zeroValue χ i.val) z)) :
    canonicalProduct χ z =
      W03.genusOneFactor r.val z ^ analyticOrderNatAt (normalizedCompletion χ) r.val *
        deletedRootProduct χ r z := by
  let : Fintype {i : ZeroIndex χ // i.1 = r} :=
    Fintype.ofEquiv (Fin (analyticOrderNatAt (normalizedCompletion χ) r.val))
      (zeroRootFiberEquiv χ r).symm
  have hhead : Multipliable (fun i : {i : ZeroIndex χ // i.1 = r} =>
      W03.genusOneFactor (zeroValue χ i.val) z) := (hasProd_fintype _).multipliable
  have hsplit := Multipliable.tprod_mul_tprod_compl
    (f := fun i : ZeroIndex χ => W03.genusOneFactor (zeroValue χ i) z)
    (s := {i : ZeroIndex χ | i.1 = r}) hhead htail
  change (∏' i : {i : ZeroIndex χ // i.1 = r},
      W03.genusOneFactor (zeroValue χ i.val) z) * deletedRootProduct χ r z =
      canonicalProduct χ z at hsplit
  rw [zeroRootFiber_tprod χ r z] at hsplit
  exact hsplit.symm

theorem analyticOrderAt_canonicalProduct_at_root
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (r : {z : ℂ // normalizedCompletion χ z = 0}) (hr : r.val ≠ 0)
    (htail : ∀ z, Multipliable (fun i : {i : ZeroIndex χ // i.1 ≠ r} =>
      W03.genusOneFactor (zeroValue χ i.val) z))
    (hd : AnalyticAt ℂ (deletedRootProduct χ r) r.val)
    (hne : deletedRootProduct χ r r.val ≠ 0) :
    analyticOrderAt (canonicalProduct χ) r.val =
      analyticOrderAt (normalizedCompletion χ) r.val := by
  have heq : canonicalProduct χ =
      (fun z => W03.genusOneFactor r.val z ^ analyticOrderNatAt (normalizedCompletion χ) r.val) *
        deletedRootProduct χ r := by
    funext z
    exact canonicalProduct_split_root χ r z (htail z)
  have hfactor : AnalyticAt ℂ
      (fun z => W03.genusOneFactor r.val z ^ analyticOrderNatAt (normalizedCompletion χ) r.val)
      r.val := ((W03.differentiable_genusOneFactor r.val).analyticAt r.val).pow _
  have htailOrder : analyticOrderAt (deletedRootProduct χ r) r.val = 0 :=
    (analyticOrderAt_eq_zero (f := deletedRootProduct χ r) (z₀ := r.val)).mpr (Or.inr hne)
  rw [heq, analyticOrderAt_mul hfactor hd,
    analyticOrderAt_genusOneFactor_pow hr, htailOrder, add_zero]
  exact natCast_order_normalizedCompletion χ hχ r.val

end SiegelZerosAwei.W51

end

section

namespace SiegelZerosAwei.W03

theorem dyadic_count_bound_of_jensen (a : ℝ → ℝ) {C A : ℝ} (hC : 0 ≤ C)
    (hj : ∀ R > 0, a R * Real.log 2 ≤
      C * (1 + 2 * R) * Real.log (2 + 2 * R) - A) (k : ℕ) :
    a ((2 : ℝ) ^ k) ≤ ((6 * C + |A|) / Real.log 2) *
      ((k : ℝ) + 1) * (2 : ℝ) ^ k := by
  let R : ℝ := 2 ^ k
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog_eq : Real.log (4 * R) = ((k : ℝ) + 2) * Real.log 2 := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hRpos.ne']
    dsimp only [R]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hlog : Real.log (2 + 2 * R) ≤ (k : ℝ) + 2 := by
    calc
      Real.log (2 + 2 * R) ≤ Real.log (4 * R) :=
        Real.log_le_log (by positivity) (by linarith)
      _ = ((k : ℝ) + 2) * Real.log 2 := hlog_eq
      _ ≤ ((k : ℝ) + 2) * 1 :=
        mul_le_mul_of_nonneg_left hL1 (by positivity)
      _ = _ := mul_one _
  have hg : C * (1 + 2 * R) * Real.log (2 + 2 * R) ≤
      6 * C * ((k : ℝ) + 1) * R := by
    calc
      C * (1 + 2 * R) * Real.log (2 + 2 * R) ≤ C * (3 * R) * ((k : ℝ) + 2) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (by linarith : 1 + 2 * R ≤ 3 * R) hC)
          hlog (Real.log_nonneg (by linarith)) (mul_nonneg hC (by positivity))
      _ = (3 * C * R) * ((k : ℝ) + 2) := by ring
      _ ≤ (3 * C * R) * (2 * ((k : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring
  have hKR : 1 ≤ ((k : ℝ) + 1) * R := by nlinarith
  have habs : |A| ≤ |A| * (((k : ℝ) + 1) * R) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hKR (abs_nonneg A)
  have hj' := hj R hRpos
  have hnum : a R * Real.log 2 ≤ (6 * C + |A|) * ((k : ℝ) + 1) * R := by
    nlinarith [neg_le_abs A]
  have hresult := (le_div_iff₀ hL).mpr hnum
  convert hresult using 1; dsimp only [R]; ring

variable {q : ℕ} [NeZero q]

theorem actual_zero_inverse_square_summable_of_growth (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive) {C : ℝ} (hC : 0 ≤ C)
    (hgrowth : ∀ z : ℂ, ‖W51.normalizedCompletion χ z‖ ≤
      Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖))) :
    Summable (fun i : W51.ZeroIndex χ => 1 / ‖W51.zeroValue χ i‖ ^ 2) := by
  apply WeightedTorusJets.W04.summable_inv_norm_sq_of_dyadic_count
    (W51.zeroValue χ)
    ((6 * C + |Real.log ‖W51.normalizedCompletion χ 0‖|) / Real.log 2)
    (W51.finite_zeroIndex_norm_le χ hχ)
  intro k
  exact dyadic_count_bound_of_jensen
    (fun R => ({i : W51.ZeroIndex χ | ‖W51.zeroValue χ i‖ ≤ R}.ncard : ℝ)) hC
    (fun R hR => actual_zero_count_le_of_growth χ hχ hprimitive hC hgrowth hR) k

end SiegelZerosAwei.W03

end

section

noncomputable section
open Filter
open scoped Topology
namespace WeightedTorusJets.W04

theorem exists_radius_avoiding_finite {α : Type*} [Fintype α]
    (a : α → ℝ) {R : ℝ} (hR : 0 < R) :
    ∃ r : ℝ, R ≤ r ∧ r ≤ 2 * R ∧
      ∀ i : α, R / (4 * ((Fintype.card α : ℝ) + 1)) ≤ |r - a i| := by
  classical
  let n : ℕ := Fintype.card α
  let t : ℝ := R / ((n : ℝ) + 1)
  let radius (j : Fin (n + 1)) : ℝ := R + (j.val : ℝ) * t
  have ht : 0 < t := div_pos hR (by positivity)
  have hdelta : R / (4 * ((Fintype.card α : ℝ) + 1)) = t / 4 := by
    dsimp [t, n]
    field_simp [ne_of_gt (show 0 < (Fintype.card α : ℝ) + 1 by positivity)]
  have hgrid : ∃ j : Fin (n + 1), ∀ i : α, t / 4 ≤ |radius j - a i| := by
    by_contra! h
    choose f hf using h
    have hinj : Function.Injective f := by
      intro j k heq
      have hj := (abs_lt.mp (hf j))
      have hk := (abs_lt.mp (hf k))
      rw [← heq] at hk
      have hnot (u v : Fin (n + 1))
          (hu : - (t / 4) < radius u - a (f j) ∧ radius u - a (f j) < t / 4)
          (hv : - (t / 4) < radius v - a (f j) ∧ radius v - a (f j) < t / 4) :
          ¬ u.val < v.val := by
        intro huv
        have huvR : (u.val : ℝ) + 1 ≤ (v.val : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt huv)
        have hmul := mul_nonneg (show 0 ≤ (v.val : ℝ) - (u.val : ℝ) - 1 by linarith) ht.le
        dsimp only [radius] at hu hv
        nlinarith
      have hjk := hnot j k hj hk
      have hkj := hnot k j hk hj
      apply Fin.ext
      omega
    have hcard := Fintype.card_le_of_injective f hinj
    simp only [Fintype.card_fin] at hcard
    dsimp only [n] at hcard
    omega
  obtain ⟨j, hj⟩ := hgrid
  refine ⟨radius j, ?_, ?_, ?_⟩
  · have hnonneg : 0 ≤ (j.val : ℝ) * t := mul_nonneg (Nat.cast_nonneg _) ht.le
    dsimp only [radius]
    linarith
  · have hjn : (j.val : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast j.isLt.le
    have hmul := mul_le_mul_of_nonneg_right hjn ht.le
    have hcancel : ((n : ℝ) + 1) * t = R := by
      dsimp [t]
      field_simp [ne_of_gt (show 0 < (n : ℝ) + 1 by positivity)]
    dsimp only [radius]
    linarith
  · intro i
    rw [hdelta]
    exact hj i

theorem exists_radius_avoiding_finite_set {ι : Type*} (S : Set ι) (hS : S.Finite)
    (a : ι → ℝ) {R : ℝ} (hR : 0 < R) :
    ∃ r : ℝ, R ≤ r ∧ r ≤ 2 * R ∧
      ∀ i ∈ S, R / (4 * ((S.ncard : ℝ) + 1)) ≤ |r - a i| := by
  let : Fintype S := hS.fintype
  obtain ⟨r, hr, hr2, hsep⟩ := exists_radius_avoiding_finite (fun i : S => a i.val) hR
  refine ⟨r, hr, hr2, ?_⟩
  intro i hi
  have h := hsep ⟨i, hi⟩
  simpa only [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using h

theorem actual_zero_radius_count_separation {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {R : ℝ} (hR : 0 < R) :
    ∃ r : ℝ, R ≤ r ∧ r ≤ 2 * R ∧
      ∀ i : SiegelZerosAwei.W51.ZeroIndex χ,
        ‖SiegelZerosAwei.W51.zeroValue χ i‖ ≤ 6 * R →
        R / (4 * ((({i : SiegelZerosAwei.W51.ZeroIndex χ |
          ‖SiegelZerosAwei.W51.zeroValue χ i‖ ≤ 6 * R}).ncard : ℝ) + 1)) ≤
          |r - ‖SiegelZerosAwei.W51.zeroValue χ i‖| := by
  exact exists_radius_avoiding_finite_set
    {i : SiegelZerosAwei.W51.ZeroIndex χ | ‖SiegelZerosAwei.W51.zeroValue χ i‖ ≤ 6 * R}
    (SiegelZerosAwei.W51.finite_zeroIndex_norm_le χ hχ (6 * R))
    (fun i => ‖SiegelZerosAwei.W51.zeroValue χ i‖) hR

theorem eventually_count_denominator_le_cube (N : ℕ → ℝ) (C : ℝ)
    (hN : ∀ k : ℕ, N k ≤ 8 * C * ((k : ℝ) + 4) * (2 : ℝ) ^ k) :
    ∀ᶠ k : ℕ in atTop, 4 * (N k + 1) ≤ ((2 : ℝ) ^ k) ^ 3 := by
  let f : ℕ → ℝ := fun k =>
    32 * C * ((k : ℝ) + 4) * (1 / 2 : ℝ) ^ k + 4 * (1 / 4 : ℝ) ^ k
  have hlinear : Summable (fun k : ℕ => (k : ℝ) * (1 / 2 : ℝ) ^ k) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1
      (r := (1 / 2 : ℝ)) (by norm_num)
  have hfirst : Summable (fun k : ℕ => 32 * C * ((k : ℝ) + 4) * (1 / 2 : ℝ) ^ k) := by
    convert (hlinear.add (summable_geometric_two.mul_left (4 : ℝ))).mul_left (32 * C) using 1
    ext k
    ring
  have hlast : Summable (fun k : ℕ => 4 * (1 / 4 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)).mul_left 4
  have hlim : Tendsto f atTop (𝓝 0) := (hfirst.add hlast).tendsto_atTop_zero
  have he : ∀ᶠ k : ℕ in atTop, f k < 1 :=
    hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [he] with k hk
  have hR : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hk.le
    (sq_nonneg ((2 : ℝ) ^ k))
  have hfour : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, pow_right_comm]
  have hid : f k * ((2 : ℝ) ^ k) ^ 2 =
      32 * C * ((k : ℝ) + 4) * (2 : ℝ) ^ k + 4 := by
    dsimp only [f]
    rw [div_pow, one_pow, div_pow, one_pow, hfour]
    field_simp
  rw [hid, one_mul] at hmul
  have hsq : ((2 : ℝ) ^ k) ^ 2 ≤ ((2 : ℝ) ^ k) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg ((2 : ℝ) ^ k)) (sub_nonneg.mpr hR)]
  have hn := hN k
  nlinarith

theorem eventually_radius_avoiding_of_dyadic_count {ι : Type*}
    (ρ : ι → ℂ) (C : ℝ)
    (hfinite : ∀ R : ℝ, {i | ‖ρ i‖ ≤ R}.Finite)
    (hcount : ∀ k : ℕ, ({i | ‖ρ i‖ ≤ (2 : ℝ) ^ k}.ncard : ℝ) ≤
      C * ((k : ℝ) + 1) * (2 : ℝ) ^ k) :
    ∀ᶠ k : ℕ in atTop, ∃ r : ℝ,
      (2 : ℝ) ^ k ≤ r ∧ r ≤ 2 * (2 : ℝ) ^ k ∧
      ∀ i : ι, ‖ρ i‖ ≤ 6 * (2 : ℝ) ^ k →
        1 / ((2 : ℝ) ^ k) ^ 2 ≤ |r - ‖ρ i‖| := by
  let N : ℕ → ℝ := fun k => ({i | ‖ρ i‖ ≤ 6 * (2 : ℝ) ^ k}.ncard : ℝ)
  have hN : ∀ k : ℕ, N k ≤ 8 * C * ((k : ℝ) + 4) * (2 : ℝ) ^ k := by
    intro k
    have hsub : {i | ‖ρ i‖ ≤ 6 * (2 : ℝ) ^ k} ⊆
        {i | ‖ρ i‖ ≤ (2 : ℝ) ^ (k + 3)} := by
      intro i hi
      change ‖ρ i‖ ≤ (2 : ℝ) ^ (k + 3)
      change ‖ρ i‖ ≤ 6 * (2 : ℝ) ^ k at hi
      rw [pow_add]
      norm_num
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) k]
    have hc : N k ≤ ({i | ‖ρ i‖ ≤ (2 : ℝ) ^ (k + 3)}.ncard : ℝ) := by
      dsimp only [N]
      exact_mod_cast Set.ncard_le_ncard hsub (hfinite ((2 : ℝ) ^ (k + 3)))
    have hh := hc.trans (hcount (k + 3))
    convert hh using 1; push_cast; rw [pow_add]; ring
  filter_upwards [eventually_count_denominator_le_cube N C hN] with k hk
  have hR : 0 < (2 : ℝ) ^ k := by positivity
  obtain ⟨r, hr, hr2, hsep⟩ := exists_radius_avoiding_finite_set
    {i | ‖ρ i‖ ≤ 6 * (2 : ℝ) ^ k} (hfinite (6 * (2 : ℝ) ^ k))
    (fun i => ‖ρ i‖) hR
  refine ⟨r, hr, hr2, fun i hi => le_trans ?_ (hsep i hi)⟩
  change 1 / ((2 : ℝ) ^ k) ^ 2 ≤ (2 : ℝ) ^ k / (4 * (N k + 1))
  have hden : 0 < 4 * (N k + 1) := by dsimp only [N]; positivity
  apply (div_le_div_iff₀ (sq_pos_of_pos hR) hden).2
  nlinarith

theorem actual_eventually_radius_separation_of_growth {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hprimitive : χ.IsPrimitive)
    {C : ℝ} (hC : 0 ≤ C)
    (hgrowth : ∀ z : ℂ, ‖SiegelZerosAwei.W51.normalizedCompletion χ z‖ ≤
      Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖))) :
    ∀ᶠ k : ℕ in atTop, ∃ r : ℝ,
      (2 : ℝ) ^ k ≤ r ∧ r ≤ 2 * (2 : ℝ) ^ k ∧
      ∀ i : SiegelZerosAwei.W51.ZeroIndex χ,
        ‖SiegelZerosAwei.W51.zeroValue χ i‖ ≤ 6 * (2 : ℝ) ^ k →
        1 / ((2 : ℝ) ^ k) ^ 2 ≤ |r - ‖SiegelZerosAwei.W51.zeroValue χ i‖| := by
  apply eventually_radius_avoiding_of_dyadic_count
    (SiegelZerosAwei.W51.zeroValue χ)
    ((6 * C + |Real.log ‖SiegelZerosAwei.W51.normalizedCompletion χ 0‖|) / Real.log 2)
    (SiegelZerosAwei.W51.finite_zeroIndex_norm_le χ hχ)
  intro k
  exact SiegelZerosAwei.W03.dyadic_count_bound_of_jensen
    (fun R => ({i : SiegelZerosAwei.W51.ZeroIndex χ |
      ‖SiegelZerosAwei.W51.zeroValue χ i‖ ≤ R}.ncard : ℝ)) hC
    (fun R hR => SiegelZerosAwei.W03.actual_zero_count_le_of_growth
      χ hχ hprimitive hC hgrowth hR) k

end WeightedTorusJets.W04

end

end

end SiegelZeros

end OAI
