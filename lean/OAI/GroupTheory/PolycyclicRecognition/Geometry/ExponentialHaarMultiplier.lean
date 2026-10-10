import OAI.GroupTheory.PolycyclicRecognition.Analysis.NilpotentHaarAutomorphisms

namespace OAI

/-! # The exact Haar multiplier of an exponential-coordinate automorphism -/

noncomputable section
namespace PolycyclicRecognition

open Module MeasureTheory
open scoped Manifold

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]
  {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [MeasurableSpace G] [BorelSpace G]
  (e : L ≃ₗ⁅ℝ⁆ GroupLieAlgebra (𝓘(ℝ, E)) G)
  (Exp : GroupLieAlgebra (𝓘(ℝ, E)) G → G) (hbij : Function.Bijective Exp)
  (chart : GroupLieAlgebra (𝓘(ℝ, E)) G ≃ₜ G) (hchart : ∀ x, chart x = Exp x)
  {n : ℕ} (b : Basis (Fin n) ℝ L)

include hchart in
/-- The pushforward multiplier is the reciprocal absolute determinant.
Consequently the multiplier of image volumes is the absolute determinant. -/
theorem exponentialConjugate_map_measure (F : L ≃ₗ⁅ℝ⁆ L) :
    Measure.map (exponentialConjugate e Exp hbij F)
      (Measure.map ((Exp ∘ e) ∘ b.equivFun.symm) volume) =
    ENNReal.ofReal |(LinearMap.det F.toLinearEquiv.toLinearMap)⁻¹| •
      Measure.map ((Exp ∘ e) ∘ b.equivFun.symm) volume := by
  let A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
    (b.equivFun.symm.trans F.toLinearEquiv).trans b.equivFun
  let f : (Fin n → ℝ) ≃ₜ G :=
    (b.equivFun.symm.trans e.toLinearEquiv).toContinuousLinearEquiv.toHomeomorph.trans chart
  have hf : (f : (Fin n → ℝ) → G) = (Exp ∘ e) ∘ b.equivFun.symm := by
    funext t
    exact hchart _
  have hAdet : LinearMap.det A.toLinearMap = LinearMap.det F.toLinearEquiv.toLinearMap := by
    have hd := congrArg Units.val (LinearEquiv.det_conj F.toLinearEquiv b.equivFun)
    simpa only [LinearEquiv.coe_det] using hd
  have hA : Measure.map A volume = ENNReal.ofReal |(LinearMap.det A.toLinearMap)⁻¹| • volume :=
    Real.map_linearMap_volume_pi_eq_smul_volume_pi A.isUnit_det'.ne_zero
  have hsem : Function.Semiconj f A (exponentialConjugate e Exp hbij F) := by
    intro t
    rw [hf]
    change Exp (e (b.equivFun.symm (A t))) = _
    simp only [A, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    exact (exponentialConjugate_apply_exp e Exp hbij F (b.equivFun.symm t)).symm
  have heq : (exponentialConjugate e Exp hbij F : G → G) = f ∘ A ∘ f.symm := by
    funext g
    obtain ⟨t, rfl⟩ := f.surjective g
    simpa only [Function.comp_apply, f.symm_apply_apply] using (hsem t).symm
  have hmeas : Measurable (exponentialConjugate e Exp hbij F) := by
    rw [heq]
    exact f.continuous.measurable.comp
      (A.toContinuousLinearEquiv.continuous.measurable.comp f.symm.continuous.measurable)
  have hcomp : (exponentialConjugate e Exp hbij F) ∘ f = f ∘ A :=
    funext (fun t => (hsem t).symm)
  have hAmeas : Measurable (A : (Fin n → ℝ) → (Fin n → ℝ)) :=
    A.toContinuousLinearEquiv.continuous.measurable
  rw [← hf, Measure.map_map hmeas f.continuous.measurable, hcomp,
    ← Measure.map_map f.continuous.measurable hAmeas,
    hA, Measure.map_smul _ f.continuous.measurable.aemeasurable, hAdet]

end PolycyclicRecognition

end

end OAI
