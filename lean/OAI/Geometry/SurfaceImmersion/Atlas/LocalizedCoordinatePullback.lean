import OAI.Geometry.SurfaceImmersion.Geometry.ScalarJetTransport
import OAI.Geometry.SurfaceImmersion.Atlas.CoordinateTaylorIdentity

namespace OAI

/-! Pullback of a polynomial through a local coordinate change and the
actual scalar localization of its input map. -/
noncomputable section
open Set
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.JetPolynomial
namespace Expression

def localizedCoordinatePullback (e : Expression) (T S : Base → Base)
    (a : Base → ℝ) : Expression :=
  (e.localCoordinatePullback T S).scalarProductPullback a

lemma localizedCoordinatePullback_smooth {T S : Base → Base} {a : Base → ℝ}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S) (ha : ContDiff ℝ ∞ a)
    {e : Expression} (he : e.SmoothCoeffs univ) :
    (e.localizedCoordinatePullback T S a).SmoothCoeffs univ :=
  scalarProductPullback_smooth ha (localCoordinatePullback_smooth hT hS he)

lemma localizedCoordinatePullback_eval {T S : Base → Base} {a : Base → ℝ}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S) (ha : ContDiff ℝ ∞ a)
    {U : Set Base} (hU : IsOpen U)
    (hST : ∀ x ∈ U, S (T x) = x)
    (hTS : ∀ x ∈ U, (T ∘ S) =ᶠ[𝓝 (T x)] id)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    {x : Base} (hx : x ∈ U)
    (hrel : (fun y => a y • H y) =ᶠ[𝓝 x] (G ∘ T))
    (e : Expression) (t : ℝ) :
    (e.localizedCoordinatePullback T S a).eval H (x,t) = e.eval G (T x,t) := by
  rw [localizedCoordinatePullback,scalarProductPullback_eval ha hH]
  exact localCoordinatePullback_eval_germ hT hS hU hST hTS hG (ha.smul hH) hx hrel e t

end Expression
namespace Perturbation

def localizedPolynomialPullback {n : ℕ} (P : Fin 3 → Fin n → Expression)
    (T S : Base → Base) (a : Base → ℝ) : Fin 3 → Fin n → Expression :=
  fun k r => (P k r).localizedCoordinatePullback T S a

lemma localizedPolynomialPullback_smooth {n : ℕ} {P : Fin 3 → Fin n → Expression}
    (hP : ∀ k r, (P k r).SmoothCoeffs univ)
    {T S : Base → Base} {a : Base → ℝ}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S) (ha : ContDiff ℝ ∞ a)
    (k : Fin 3) (r : Fin n) :
    (localizedPolynomialPullback P T S a k r).SmoothCoeffs univ :=
  Expression.localizedCoordinatePullback_smooth hT hS ha (hP k r)

lemma localizedPolynomialPullback_eval {n : ℕ} (P : Fin 3 → Fin n → Expression)
    {T S : Base → Base} {a : Base → ℝ}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S) (ha : ContDiff ℝ ∞ a)
    {U : Set Base} (hU : IsOpen U)
    (hST : ∀ x ∈ U, S (T x) = x)
    (hTS : ∀ x ∈ U, (T ∘ S) =ᶠ[𝓝 (T x)] id)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    {x : Base} (hx : x ∈ U)
    (hrel : (fun y => a y • H y) =ᶠ[𝓝 x] (G ∘ T)) (ε t : ℝ) :
    coordinatePolynomialValue (localizedPolynomialPullback P T S a) ε H t
        (planeCoordinateIsometry x) =
      coordinatePolynomialValue P ε G t (planeCoordinateIsometry (T x)) := by
  funext k
  simp only [coordinatePolynomialValue,LinearIsometryEquiv.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro r _
  rw [localizedPolynomialPullback,
    Expression.localizedCoordinatePullback_eval hT hS ha hU hST hTS hG hH hx hrel]

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
