import OAI.Geometry.RCD.Sobolev.LocalizedGradientPair
import OAI.Geometry.RCD.Sobolev.BoundaryMaximum
import Mathlib.Topology.ContinuousMap.CompactlySupported

namespace OAI

/-! # Compact Lipschitz tests and their Sobolev classes -/

open Set Filter MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

def compactLipschitzTests (Ω : Set X) : Submodule ℝ (X →ᵇ ℝ) where
  carrier := {f | ∃ L : ℝ≥0, LipschitzWith L f ∧ HasCompactSupport ((f : X →ᵇ ℝ) : X → ℝ) ∧ tsupport f ⊆ Ω}
  zero_mem' := ⟨0, LipschitzWith.const 0, HasCompactSupport.zero, by simp⟩
  add_mem' := by
    rintro f g ⟨L, hL, hf, hs⟩ ⟨M, hM, hg, ht⟩
    refine ⟨L + M, hL.add hM, hf.add hg, ?_⟩
    exact (tsupport_add _ _).trans (union_subset hs ht)
  smul_mem' := by
    rintro c f ⟨L, hL, hf, hs⟩
    refine ⟨‖c‖₊ * L, (lipschitzWith_smul c).comp hL, hf.smul_left, ?_⟩
    exact (tsupport_smul_subset_right (fun _ => c) _).trans hs

omit [MeasurableSpace X] [BorelSpace X] in
theorem compactLipschitzTests_sup_zero {Ω : Set X} (f : compactLipschitzTests Ω) :
    (f : X →ᵇ ℝ) ⊔ 0 ∈ compactLipschitzTests Ω := by
  obtain ⟨L, hL, hc, hs⟩ := f.property
  have hsupport : tsupport ((f : X →ᵇ ℝ) ⊔ 0) ⊆ tsupport (f : X →ᵇ ℝ) := by
    apply closure_mono
    intro x hx
    change max ((f : X →ᵇ ℝ) x) 0 ≠ 0 at hx
    change (f : X →ᵇ ℝ) x ≠ 0
    intro hz
    exact hx (by simp [hz])
  exact ⟨L, hL.max_const 0,
    hc.of_isClosed_subset (isClosed_tsupport _) hsupport, hsupport.trans hs⟩

variable (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

private def testSobolev (Ω : Set X) (f : compactLipschitzTests Ω) : SobolevSpace μ hQ :=
  SobolevSpace.ofLipschitzCompact μ hQ f.property.choose_spec.1 f.property.choose_spec.2.1

private theorem testSobolev_coe (Ω : Set X) (f : compactLipschitzTests Ω) :
    SobolevSpace.toLp μ hQ (testSobolev μ hQ Ω f) =ᵐ[μ] ((f : X →ᵇ ℝ) : X → ℝ) :=
  SobolevSpace.ofLipschitzCompact_coe μ hQ _ _

/-- The lift is linear because its actual L² representative is the test. -/
def compactTestSobolev (Ω : Set X) : compactLipschitzTests Ω →ₗ[ℝ] SobolevSpace μ hQ where
  toFun := testSobolev μ hQ Ω
  map_add' f g := by
    apply Subtype.ext
    apply Lp.ext
    exact (testSobolev_coe μ hQ Ω (f + g)).trans
      ((testSobolev_coe μ hQ Ω f).add (testSobolev_coe μ hQ Ω g) |>.symm.trans
        (Lp.coeFn_add _ _).symm)
  map_smul' c f := by
    apply Subtype.ext
    apply Lp.ext
    exact (testSobolev_coe μ hQ Ω (c • f)).trans
      ((testSobolev_coe μ hQ Ω f).const_smul c |>.symm.trans (Lp.coeFn_smul c _).symm)

theorem compactTestSobolev_coe (Ω : Set X) (f : compactLipschitzTests Ω) :
    SobolevSpace.toLp μ hQ (compactTestSobolev μ hQ Ω f) =ᵐ[μ] ((f : X →ᵇ ℝ) : X → ℝ) :=
  testSobolev_coe μ hQ Ω f

/-- A local distribution of the form energy pairing plus a constant density. -/
def compactTestEnergy (Ω : Set X) (q : SobolevSpace μ hQ) (a : ℝ) :
    compactLipschitzTests Ω →ₗ[ℝ] ℝ where
  toFun f := energyForm μ hQ q (compactTestSobolev μ hQ Ω f) + a * ∫ x, (f : X →ᵇ ℝ) x ∂μ
  map_add' f g := by
    rw [map_add, energyForm_add_right]
    have hf : Integrable (f : X →ᵇ ℝ) μ := (f : X →ᵇ ℝ).continuous.integrable_of_hasCompactSupport f.property.choose_spec.2.1
    have hg : Integrable (g : X →ᵇ ℝ) μ := (g : X →ᵇ ℝ).continuous.integrable_of_hasCompactSupport g.property.choose_spec.2.1
    change _ + a * ∫ x, (f : X →ᵇ ℝ) x + (g : X →ᵇ ℝ) x ∂μ = _
    rw [integral_add hf hg]
    ring
  map_smul' c f := by
    rw [map_smul, energyForm_smul_right]
    change _ + a * ∫ x, c * (f : X →ᵇ ℝ) x ∂μ = _
    rw [integral_const_mul]
    simp only [smul_eq_mul, RingHom.id_apply]
    ring

end RegularPointCoordinates

end

end OAI
