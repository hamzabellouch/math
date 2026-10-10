import OAI.Geometry.SurfaceImmersion.Atlas.LowJetCoordinateChange
import OAI.Geometry.SurfaceImmersion.Correction.JetPolynomialAlgebra

namespace OAI

/-! A finite jet expression depends only on the germ of its input map. -/
noncomputable section
open scoped ContDiff Topology
namespace ClosedSurfaceR4.JetPolynomial

lemma jet_eventuallyEq {G H : Base → Space} {x : Base}
    (h : G =ᶠ[𝓝 x] H) (w : List (Fin 2)) (a : Fin 4) :
    jet G w a =ᶠ[𝓝 x] jet H w a := by
  induction w with
  | nil => exact h.mono (fun _ he => congrFun he a)
  | cons i w ih =>
    filter_upwards [ih.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun L : Base →L[ℝ] ℝ => L (coordinateVector i)) hy

namespace Expression

lemma eval_eq_of_eventuallyEq {G H : Base → Space} {x : Base}
    (h : G =ᶠ[𝓝 x] H) (e : Expression) (t : ℝ) :
    e.eval G (x,t) = e.eval H (x,t) := by
  induction e with
  | coeff c =>
    change c (lowJet G x,t) = c (lowJet H x,t)
    rw [lowJet_eventuallyEq h]
  | atom w a e ih =>
    change jet G w a x * e.eval G (x,t) = jet H w a x * e.eval H (x,t)
    rw [(jet_eventuallyEq h w a).self_of_nhds,ih]
  | add e f ihe ihf =>
    change e.eval G (x,t)+f.eval G (x,t) = e.eval H (x,t)+f.eval H (x,t)
    rw [ihe,ihf]

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
