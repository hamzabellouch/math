import OAI.Geometry.SurfaceImmersion.Correction.JetPolynomialLocality
import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateQuadraticExpansion

namespace OAI

/-! Mixed variations only use the germs of their four input fields. -/
noncomputable section
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.JetPolynomial

lemma MixedExpression.eval_eq_of_eventuallyEq {F G : Fin 4 → Base → Space} {x : Base}
    (h : ∀ i, F i =ᶠ[𝓝 x] G i) (e : MixedExpression) (t : ℝ) :
    e.eval F (x,t) = e.eval G (x,t) := by
  induction e with
  | coeff c =>
    change c (lowJet (F 0) x,t) = c (lowJet (G 0) x,t)
    rw [lowJet_eventuallyEq (h 0)]
  | atom i w a e ih =>
    change jet (F i) w a x * e.eval F (x,t) = jet (G i) w a x * e.eval G (x,t)
    rw [(jet_eventuallyEq (h i) w a).self_of_nhds,ih]
  | add e f ihe ihf =>
    change e.eval F (x,t)+f.eval F (x,t) = e.eval G (x,t)+f.eval G (x,t)
    rw [ihe,ihf]

namespace Perturbation

lemma coordinateQuadraticPolynomial_eq_of_eventuallyEq {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {X Y : RealModes.RField 4} {x : Base}
    (h : X ∘ planeCoordinateIsometry =ᶠ[𝓝 x] Y ∘ planeCoordinateIsometry) (t : ℝ) :
    coordinateQuadraticPolynomial P ε G X t (planeCoordinateIsometry x) =
      coordinateQuadraticPolynomial P ε G Y t (planeCoordinateIsometry x) := by
  have hf : ∀ i : Fin 4, (![G,X ∘ planeCoordinateIsometry,X ∘ planeCoordinateIsometry,0] i) =ᶠ[𝓝 x]
      (![G,Y ∘ planeCoordinateIsometry,Y ∘ planeCoordinateIsometry,0] i) := by
    intro i
    fin_cases i
    · exact Filter.EventuallyEq.rfl
    · exact h
    · exact h
    · exact Filter.EventuallyEq.rfl
  funext k
  simp only [coordinateQuadraticPolynomial,planeCoordinateIsometry.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro l _
  rw [MixedExpression.eval_eq_of_eventuallyEq hf ((P k l).variations 1) t]

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
