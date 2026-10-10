import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentAutomorphism

namespace OAI

/-! # Topology of the integrated nilpotent automorphisms -/

noncomputable section
namespace PolycyclicRecognition

open LieModule
open scoped Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]
  (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hbij : Function.Bijective Exp)
  (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)

omit [T2Space G] in
include hchart in
theorem continuous_exponentialConjugate (F : L ≃ₗ⁅ℝ⁆ L) :
    Continuous (exponentialConjugate e Exp hbij F) := by
  let D := (e.symm.toLinearEquiv.trans F.toLinearEquiv).trans e.toLinearEquiv
  have heq : (exponentialConjugate e Exp hbij F : G → G) =
      chart ∘ D ∘ chart.symm := by
    funext g
    obtain ⟨x, rfl⟩ := (hbij.comp e.bijective).surjective g
    change exponentialConjugate e Exp hbij F (Exp (e x)) = _
    rw [exponentialConjugate_apply_exp]
    simp only [Function.comp_apply, ← hchart, chart.symm_apply_apply, D,
      LinearEquiv.trans_apply, LieEquiv.coe_toLinearEquiv]
    change chart (e (F x)) = chart (e (F (e.symm (e x))))
    rw [e.symm_apply_apply]
  rw [heq]
  exact chart.continuous.comp (D.toContinuousLinearEquiv.continuous.comp chart.symm.continuous)

/-- Both directions of exponential conjugation are continuous, and the
published finite Dynkin formula proves its multiplicativity. -/
def integrateNilpotentLieEquivContinuous
    (dynkin : NilpotentDynkinExpansionInput E G) (hExp : IsGroupExponential Exp)
    {c : ℕ} (hc : lowerCentralSeries ℝ L L c = ⊥) (F : L ≃ₗ⁅ℝ⁆ L) : G ≃ₜ* G := by
  let f := integrateNilpotentLieEquiv e Exp hbij dynkin hExp hc F
  refine { f with
    continuous_toFun := continuous_exponentialConjugate e Exp hbij chart hchart F
    continuous_invFun := ?_ }
  have heq : (f.symm : G → G) = exponentialConjugate e Exp hbij F.symm := by
    funext g
    apply f.injective
    rw [f.apply_symm_apply]
    obtain ⟨x, rfl⟩ := (hbij.comp e.bijective).surjective g
    change Exp (e x) = exponentialConjugate e Exp hbij F
      (exponentialConjugate e Exp hbij F.symm (Exp (e x)))
    rw [exponentialConjugate_apply_exp, exponentialConjugate_apply_exp, F.apply_symm_apply]
  change Continuous (f.symm : G → G)
  rw [heq]
  exact continuous_exponentialConjugate e Exp hbij chart hchart F.symm

end PolycyclicRecognition

end

end OAI
