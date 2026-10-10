import OAI.Geometry.SurfaceImmersion.Geometry.JetPullbackExpressions
import OAI.Geometry.SurfaceImmersion.Atlas.LowJetCoordinateChange

namespace OAI

/-! The coordinate pullback of a finite jet polynomial, with the low-jet
substitution and inverse differential proved from the actual local inverse.
No compatibility of the polynomial values is assumed. -/
noncomputable section
open Set
open scoped ContDiff Topology

namespace ClosedSurfaceR4.JetPolynomial

def coordinateLowJetSubstitution (T S : Base → Base) (J : LowJet) : LowJet :=
  lowJetCoordinateChange S (T (lowPosition J),J)

lemma coordinateLowJetSubstitution_smooth {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S) :
    ContDiff ℝ ∞ (coordinateLowJetSubstitution T S) :=
  (lowJetCoordinateChange_smooth hS).comp
    ((hT.comp lowPosition.contDiff).prodMk contDiff_id)

lemma inverse_differential_of_local_inverse {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S) (x : Base)
    (hST : S (T x) = x) (hTS : (T ∘ S) =ᶠ[𝓝 (T x)] id) :
    (fderiv ℝ T x).comp (fderiv ℝ S (T x)) = ContinuousLinearMap.id ℝ Base := by
  have hd := hTS.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp (T x) (hT.differentiable (by simp) _) (hS.differentiable (by simp) _),
    hST,fderiv_id] at hd
  exact hd

namespace Expression

/-- Transport through a smooth local inverse, including the coefficient
dependence on all positional order-two jets. -/
def localCoordinatePullback (e : Expression) (T S : Base → Base) : Expression :=
  e.coordinatePullback T S (coordinateLowJetSubstitution T S)

lemma localCoordinatePullback_smooth {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S)
    {e : Expression} (he : e.SmoothCoeffs univ) :
    (e.localCoordinatePullback T S).SmoothCoeffs univ :=
  coordinatePullback_smooth hT hS (coordinateLowJetSubstitution_smooth hT hS) he

lemma localCoordinatePullback_eval {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S)
    {U : Set Base} (hU : IsOpen U)
    (hST : ∀ x ∈ U, S (T x) = x)
    (hTS : ∀ x ∈ U, (T ∘ S) =ᶠ[𝓝 (T x)] id)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (hrel : ∀ x ∈ U, H x = G (T x))
    (e : Expression) (t : ℝ) {x : Base} (hx : x ∈ U) :
    (e.localCoordinatePullback T S).eval H (x,t) = e.eval G (T x,t) := by
  apply coordinatePullback_eval hT hS hU
    (fun y hy => inverse_differential_of_local_inverse hT hS y (hST y hy) (hTS y hy))
    hG hH hrel _ e t hx
  intro y hy
  have hgerm : H =ᶠ[𝓝 y] (G ∘ T) := by
    filter_upwards [hU.mem_nhds hy] with z hz
    exact hrel z hz
  exact (lowJetCoordinateChange_local_inverse hH hS y (hST y hy) (hTS y hy) hgerm).symm

/-- At a boundary of a support it is enough to know the actual map relation
as a germ at the point under consideration. -/
lemma localCoordinatePullback_eval_germ {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S)
    {U : Set Base} (hU : IsOpen U)
    (hST : ∀ x ∈ U, S (T x) = x)
    (hTS : ∀ x ∈ U, (T ∘ S) =ᶠ[𝓝 (T x)] id)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    {x : Base} (hx : x ∈ U) (hrel : H =ᶠ[𝓝 x] (G ∘ T))
    (e : Expression) (t : ℝ) :
    (e.localCoordinatePullback T S).eval H (x,t) = e.eval G (T x,t) := by
  have hn : {y | H y = G (T y)} ∩ U ∈ 𝓝 x :=
    Filter.inter_mem hrel (hU.mem_nhds hx)
  obtain ⟨V,hVsub,hV,hxV⟩ := mem_nhds_iff.mp hn
  exact localCoordinatePullback_eval hT hS hV
    (fun y hy => hST y (hVsub hy).2) (fun y hy => hTS y (hVsub hy).2)
    hG hH (fun y hy => (hVsub hy).1) e t hxV

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
