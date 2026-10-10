import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialHaarMultiplier

namespace OAI

/-! # Image volumes under exponential-coordinate automorphisms -/

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
/-- A positive exponential determinant is the image-volume multiplier.
This identity holds for arbitrary sets, using the measurable embedding. -/
theorem exponentialConjugate_image_measure
    (F : L ≃ₗ⁅ℝ⁆ L) (d : ℝ)
    (hd : LinearMap.det F.toLinearEquiv.toLinearMap = Real.exp d) (S : Set G) :
    (Measure.map ((Exp ∘ e) ∘ b.equivFun.symm) volume)
      (exponentialConjugate e Exp hbij F '' S) =
    ENNReal.ofReal (Real.exp d) *
      (Measure.map ((Exp ∘ e) ∘ b.equivFun.symm) volume) S := by
  let A : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
    (b.equivFun.symm.trans F.toLinearEquiv).trans b.equivFun
  let f : (Fin n → ℝ) ≃ₜ G :=
    (b.equivFun.symm.trans e.toLinearEquiv).toContinuousLinearEquiv.toHomeomorph.trans chart
  let g : G ≃ₜ G := (f.symm.trans A.toContinuousLinearEquiv.toHomeomorph).trans f
  let μ := Measure.map ((Exp ∘ e) ∘ b.equivFun.symm) volume
  have hf : (f : (Fin n → ℝ) → G) = (Exp ∘ e) ∘ b.equivFun.symm := by
    funext t
    exact hchart _
  have hg : (g : G → G) = exponentialConjugate e Exp hbij F := by
    funext x
    obtain ⟨v, rfl⟩ := f.surjective x
    change f (A (f.symm (f v))) = _
    rw [f.symm_apply_apply, hf]
    simp only [A, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, Function.comp_apply]
    change Exp (e (F (b.equivFun.symm v))) = _
    exact (exponentialConjugate_apply_exp e Exp hbij F (b.equivFun.symm v)).symm
  have hm := exponentialConjugate_map_measure e Exp hbij chart hchart b F
  rw [← hg, hd, ← Real.exp_neg, abs_of_pos (Real.exp_pos _)] at hm
  have hv := congrArg (fun ν : Measure G => ν (g '' S)) hm
  rw [g.measurableEmbedding.map_apply, Set.preimage_image_eq _ g.injective,
    Measure.smul_apply, smul_eq_mul] at hv
  have hmul : ENNReal.ofReal (Real.exp d) * ENNReal.ofReal (Real.exp (-d)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, ENNReal.ofReal_one]
  rw [← hg]
  change μ (g '' S) = ENNReal.ofReal (Real.exp d) * μ S
  calc
    μ (g '' S) = 1 * μ (g '' S) := (one_mul _).symm
    _ = (ENNReal.ofReal (Real.exp d) * ENNReal.ofReal (Real.exp (-d))) * μ (g '' S) := by rw [hmul]
    _ = ENNReal.ofReal (Real.exp d) * μ S := by rw [mul_assoc, ← hv]

end PolycyclicRecognition

end

end OAI
