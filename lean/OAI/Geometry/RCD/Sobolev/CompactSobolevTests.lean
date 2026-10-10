import OAI.Geometry.RCD.Sobolev.CompactLipschitzTests

namespace OAI

/-! # Continuous compact Sobolev tests and their canonical lift -/

open Set Filter MeasureTheory
open scoped BoundedContinuousFunction NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

def compactSobolevTests (Ω : Set X) : Submodule ℝ (X →ᵇ ℝ) where
  carrier := {v | HasCompactSupport ((v : X →ᵇ ℝ) : X → ℝ) ∧ tsupport v ⊆ Ω ∧
    ∃ u : SobolevSpace μ hQ, SobolevSpace.toLp μ hQ u =ᵐ[μ] ((v : X →ᵇ ℝ) : X → ℝ)}
  zero_mem' := ⟨HasCompactSupport.zero, by simp, 0, by
    simpa only [map_zero, BoundedContinuousFunction.coe_zero] using (Lp.coeFn_zero ℝ 2 μ)⟩
  add_mem' := by
    rintro f g ⟨hf, hfs, u, hu⟩ ⟨hg, hgs, v, hv⟩
    refine ⟨hf.add hg, (tsupport_add _ _).trans (union_subset hfs hgs), u + v, ?_⟩
    exact (Lp.coeFn_add _ _).trans (hu.add hv)
  smul_mem' := by
    rintro c f ⟨hf, hfs, u, hu⟩
    refine ⟨hf.smul_left, (tsupport_smul_subset_right (fun _ => c) _).trans hfs, c • u, ?_⟩
    exact (Lp.coeFn_smul c _).trans (hu.const_smul c)

private def sobolevTestLift (Ω : Set X) (v : compactSobolevTests μ hQ Ω) : SobolevSpace μ hQ :=
  v.property.2.2.choose

omit [BorelSpace X] in
private theorem sobolevTestLift_coe (Ω : Set X) (v : compactSobolevTests μ hQ Ω) :
    SobolevSpace.toLp μ hQ (sobolevTestLift μ hQ Ω v) =ᵐ[μ] ((v : X →ᵇ ℝ) : X → ℝ) :=
  v.property.2.2.choose_spec

def compactSobolevTestLift (Ω : Set X) : compactSobolevTests μ hQ Ω →ₗ[ℝ] SobolevSpace μ hQ where
  toFun := sobolevTestLift μ hQ Ω
  map_add' f g := by
    apply Subtype.ext
    apply Lp.ext
    exact (sobolevTestLift_coe μ hQ Ω (f + g)).trans
      ((sobolevTestLift_coe μ hQ Ω f).add (sobolevTestLift_coe μ hQ Ω g) |>.symm.trans
        (Lp.coeFn_add _ _).symm)
  map_smul' c f := by
    apply Subtype.ext
    apply Lp.ext
    exact (sobolevTestLift_coe μ hQ Ω (c • f)).trans
      ((sobolevTestLift_coe μ hQ Ω f).const_smul c |>.symm.trans (Lp.coeFn_smul c _).symm)

omit [BorelSpace X] in
theorem compactSobolevTestLift_coe (Ω : Set X) (v : compactSobolevTests μ hQ Ω) :
    SobolevSpace.toLp μ hQ (compactSobolevTestLift μ hQ Ω v) =ᵐ[μ] ((v : X →ᵇ ℝ) : X → ℝ) :=
  sobolevTestLift_coe μ hQ Ω v

end RegularPointCoordinates

end

end OAI
