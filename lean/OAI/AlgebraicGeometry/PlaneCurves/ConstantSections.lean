import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Order.Compact
import OAI.AlgebraicGeometry.PlaneCurves.SectionBases
import OAI.AlgebraicGeometry.PlaneCurves.TorusCharts

namespace OAI

/-!
# Contraction constancy and zero-degree sections
-/

section

/-! A bounded holomorphic function on the punctured plane invariant under a
strict contraction is constant there. The proof uses the actual removable
singularity limit and convergence of contraction iterates. -/

namespace Nagata.W19

open Filter Topology

theorem contraction_invariant_nat_pow {τ : ℂ} (hτ : τ ≠ 0)
    {f : ℂ → ℂ} (hf : ∀ z, z ≠ 0 → f (τ * z) = f z)
    (z : ℂ) (hz : z ≠ 0) (n : ℕ) : f (τ ^ n * z) = f z := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [pow_succ', mul_assoc, hf _ (mul_ne_zero (pow_ne_zero n hτ) hz), hn]

theorem contraction_invariant_zpow {τ : ℂ} (hτ : τ ≠ 0)
    {f : ℂ → ℂ} (hf : ∀ z, z ≠ 0 → f (τ * z) = f z)
    (z : ℂ) (hz : z ≠ 0) (n : ℤ) : f (τ ^ n * z) = f z := by
  cases n with
  | ofNat n => simpa using contraction_invariant_nat_pow hτ hf z hz n
  | negSucc n =>
    have h := contraction_invariant_nat_pow hτ hf
      (τ ^ (-(n + 1 : ℤ)) * z) (mul_ne_zero (zpow_ne_zero _ hτ) hz) (n + 1)
    have hcancel : τ ^ (n + 1) * (τ ^ (-(n + 1 : ℤ)) * z) = z := by
      rw [zpow_neg, show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by simp,
        zpow_natCast, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hτ), one_mul]
    rw [hcancel] at h
    exact h.symm

theorem bounded_holomorphic_contraction_constant {τ : ℂ}
    (hτ : τ ≠ 0) (hτ1 : ‖τ‖ < 1) (f : ℂ → ℂ)
    (hhol : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z)
    (hperiod : ∀ z, z ≠ 0 → f (τ * z) = f z)
    (hbounded : ∃ B : ℝ, ∀ z, z ≠ 0 → ‖f z‖ ≤ B) :
    ∀ z, z ≠ 0 → f z = f 1 := by
  obtain ⟨B, hB⟩ := hbounded
  have hlim : Tendsto f (𝓝[≠] (0 : ℂ))
      (𝓝 (limUnder (𝓝[≠] (0 : ℂ)) f)) := by
    apply Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under
    · exact Filter.Eventually.mono self_mem_nhdsWithin fun z hz => hhol z hz
    · refine ⟨B + ‖f 0‖, ?_⟩
      change ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖f z - f 0‖ ≤ B + ‖f 0‖
      exact Filter.Eventually.mono self_mem_nhdsWithin fun z hz =>
        norm_sub_le_of_le (hB z hz) le_rfl
  have hvalue : ∀ z, z ≠ 0 → f z = limUnder (𝓝[≠] (0 : ℂ)) f := by
    intro z hz
    have horbit : Tendsto (fun n : ℕ => τ ^ n * z) atTop (𝓝[≠] (0 : ℂ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
      · simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hτ1).mul_const z
      · exact mul_ne_zero (pow_ne_zero n hτ) hz
    have hc : Tendsto (fun _ : ℕ => f z) atTop
        (𝓝 (limUnder (𝓝[≠] (0 : ℂ)) f)) := by
      simpa only [Function.comp_def, contraction_invariant_nat_pow hτ hperiod z hz] using
        hlim.comp horbit
    exact tendsto_nhds_unique tendsto_const_nhds hc
  intro z hz
  exact (hvalue z hz).trans (hvalue 1 one_ne_zero).symm

end Nagata.W19

end

section

/-! The actual degree-zero trivial-multiplier automorphic section space is
one-dimensional, by compact annulus bounds and removable singularities. -/

noncomputable section
namespace Nagata.W19

open Nagata.W08 Nagata.Workers.W05 Nagata.Workers.W10

theorem periodic_holomorphic_bounded {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (f : ℂ → ℂ) (hhol : ∀ z, z ≠ 0 → DifferentiableAt ℂ f z)
    (hperiod : ∀ z, z ≠ 0 → f ((τ : ℂ) * z) = f z) :
    ∃ B : ℝ, ∀ z, z ≠ 0 → ‖f z‖ ≤ B := by
  have hcont : ContinuousOn (fun z => ‖f z‖) (closedAnnulus τ) := by
    intro z hz
    exact (hhol z (norm_pos_iff.mp (lt_of_lt_of_le hτ hz.1))).continuousAt.norm.continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_closedAnnulus τ).bddAbove_image hcont
  refine ⟨B, ?_⟩
  intro z hz
  obtain ⟨k, hk⟩ := exists_zpow_in_annulus hτ hτ1 z hz
  have hval := contraction_invariant_zpow (Complex.ofReal_ne_zero.mpr (ne_of_gt hτ))
    hperiod z hz k
  rw [← hval]
  exact hB (Set.mem_image_of_mem _ hk)

theorem degree_zero_section_constant {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (f : automorphicSections (τ : ℂ) 0 1) (z : ℂ) (hz : z ≠ 0) :
    f.val z = f.val 1 := by
  have hp : ∀ z, z ≠ 0 → f.val ((τ : ℂ) * z) = f.val z := by
    intro z hz
    simpa using f.property.2.2 z hz
  exact bounded_holomorphic_contraction_constant
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hτ))
    (by simpa only [Complex.norm_of_nonneg hτ.le] using hτ1)
    f.val f.property.2.1 hp (periodic_holomorphic_bounded hτ hτ1 f.val f.property.2.1 hp) z hz

/-- Evaluation at one is a genuine linear equivalence for actual sections. -/
def degreeZeroSectionEquiv {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) :
    automorphicSections (τ : ℂ) 0 1 ≃ₗ[ℂ] ℂ where
  toFun f := f.val 1
  invFun a := normalizedConstantSection (τ : ℂ)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hτ)) a
  left_inv f := by
    apply automorphicSections_ext
    intro z hz
    rw [normalizedConstantSection_apply _ _ _ hz]
    exact (degree_zero_section_constant hτ hτ1 f z hz).symm
  right_inv a := normalizedConstantSection_apply _ _ _ one_ne_zero
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A basis of the actual section space with its single constant-one vector. -/
def degreeZeroConstantBasis {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1) :
    Module.Basis PUnit ℂ (automorphicSections (τ : ℂ) 0 1) :=
  (Module.Basis.singleton PUnit ℂ).map (degreeZeroSectionEquiv hτ hτ1).symm

@[simp] theorem degreeZeroConstantBasis_apply {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (i : PUnit) : degreeZeroConstantBasis hτ hτ1 i =
      normalizedConstantSection (τ : ℂ) (Complex.ofReal_ne_zero.mpr (ne_of_gt hτ)) 1 := by
  simp [degreeZeroConstantBasis, degreeZeroSectionEquiv]

theorem degreeZeroConstantBasis_nonzero {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ < 1)
    (i : PUnit) : degreeZeroConstantBasis hτ hτ1 i ≠ 0 :=
  (degreeZeroConstantBasis hτ hτ1).ne_zero i

end Nagata.W19

end
end

end OAI
