import OAI.Geometry.SurfaceImmersion.Atlas.ChartFullLinearization

namespace OAI

/-! The full linearized metric perturbation preserves the support of its
varying field, including every higher-jet polynomial term. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

lemma coordinateFullLinearized_zero_of_notMem {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {X : RealModes.RField 4} {p : SmallModes.Base} (hp : p ∉ tsupport X) :
    coordinateFullLinearized P ε G X p = 0 := by
  have hx : X =ᶠ[nhds p] (fun _ => 0) := notMem_tsupport_iff_eventuallyEq.mp hp
  have hc : (X ∘ planeCoordinateIsometry) =ᶠ[nhds (planeCoordinateIsometry.symm p)] (fun _ => 0) := by
    apply hx.comp_tendsto
    simpa only [planeCoordinateIsometry.apply_symm_apply] using
      (planeCoordinateIsometry.continuous.continuousAt (x := planeCoordinateIsometry.symm p)).tendsto
  have hn : planeCoordinateIsometry.symm p ∉ tsupport (X ∘ planeCoordinateIsometry) :=
    notMem_tsupport_iff_eventuallyEq.mpr hc
  have hm : RealModes.realLinearizedTensor (G ∘ planeCoordinateIsometry.symm) X p = 0 := by
    rw [RealModes.realLinearizedTensor_congr_right hx, RealModes.realLinearizedTensor_zero_right]
  funext k
  simp only [coordinateFullLinearized, Pi.add_apply, hm, Pi.zero_apply, zero_add,
    coordinateRealLinearized, linearized]
  apply Finset.sum_eq_zero
  intro l _
  rw [(P k l).variation_zero_of_notMem G hn 0, mul_zero]

lemma coordinateFullLinearized_tsupport {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space) (X : RealModes.RField 4) :
    tsupport (coordinateFullLinearized P ε G X) ⊆ tsupport X := by
  apply closure_minimal _ (isClosed_tsupport X)
  intro p hp
  by_contra hn
  exact hp (coordinateFullLinearized_zero_of_notMem P ε G hn)

lemma fullLinearized_residual_tsupport {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {X : RealModes.RField 4} {f : SmallModes.Tensor} {S : Set SmallModes.Base}
    (hS : IsClosed S) (hX : tsupport X ⊆ S) (hf : tsupport f ⊆ S)
    (τ : ℝ) (φ : SmallModes.Base → ℝ) :
    tsupport (fun p => coordinateFullLinearized P ε G X p + QuadraticMean.displacement τ φ f p) ⊆ S := by
  apply closure_minimal _ hS
  intro p hp
  by_contra hn
  apply hp
  change coordinateFullLinearized P ε G X p + QuadraticMean.displacement τ φ f p = 0
  rw [coordinateFullLinearized_zero_of_notMem P ε G (fun hx => hn (hX hx)),
    RealModes.displacement_zero_value τ φ (image_eq_zero_of_notMem_tsupport (fun hx => hn (hf hx))),
    add_zero]

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
