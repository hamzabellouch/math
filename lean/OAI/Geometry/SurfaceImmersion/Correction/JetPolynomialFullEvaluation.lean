import OAI.Geometry.SurfaceImmersion.Primitive.ExplicitPeriodicFormula
import OAI.Geometry.SurfaceImmersion.Correction.LocalFullPeriodicCorrector

namespace OAI

/-! Identification of the complete polynomial expression with the same
explicit solution supplied by the full periodic system theorem. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.JetPolynomial.Expression
open CovarianceCorrector PeriodicCorrector

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Polynomial forcing produces the explicit full corrector. The derivative
in the transverse datum is the actual derivative of the forcing primitive. -/
theorem eval_fullComponent {O : Set LowJet} {S : Set Base} (hO : IsOpen O) (hS : IsOpen S)
    {Y C X₀ : LowJet → E} {V : LowJet → C(Period, E)} {q : LowJet → ℝ}
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O) (hX : ContDiffOn ℝ ∞ X₀ O)
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hd : ∀ Q ∈ O, gramDet (Y Q) (C Q) ≠ 0)
    (hq : ContDiffOn ℝ ∞ q O) (hqp : ∀ Q ∈ O, 0 < q Q)
    (hcircle : ∀ Q ∈ O, ∀ t, inner ℝ (V Q t) (V Q t) = q Q)
    (L : E →L[ℝ] ℝ) (v : Fin 2) {h j e : Expression}
    (hh : h.SmoothCoeffs O) (hj : j.SmoothCoeffs O) (he : e.SmoothCoeffs O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    (hf jf ef : Base → C(Period, ℝ))
    (hhr : ∀ p ∈ S, ∀ t : ℝ, h.eval G (p, t) = hf p (t : Period))
    (hjr : ∀ p ∈ S, ∀ t : ℝ, j.eval G (p, t) = jf p (t : Period))
    (her : ∀ p ∈ S, ∀ t : ℝ, e.eval G (p, t) = ef p (t : Period))
    {p : Base} (hp : p ∈ S) (t : ℝ) :
    (fullComponent Y C X₀ V q L v h j e).eval G (p, t) =
      L (fullSolutionFormula (coordinateVector v) (fun x => Y (lowJet G x))
        (fun x => C (lowJet G x)) (fun x => X₀ (lowJet G x))
        (fun x => V (lowJet G x)) (fun x => q (lowJet G x)) hf jf ef (p, t)) := by
  let K := (h.primitive.slow v).sub j
  have hK : K.SmoothCoeffs O :=
    smoothCoeffs_sub (smoothCoeffs_slow hO v (smoothCoeffs_primitive hO hh)) hj
  have hk : (fun s => K.eval G (p, s)) = fun s : ℝ =>
      fderiv ℝ (fun x => PeriodicPrimitive.primitive (fun u : ℝ => hf x (u : Period)) s)
        p (coordinateVector v) - jf p (s : Period) := by
    funext s
    rw [show K = (h.primitive.slow v).sub j from rfl,
      eval_transverseDatum hO hS hG hQ v hh hp, hjr p hp s]
    have heq : (fun x => PeriodicPrimitive.primitive (fun u => h.eval G (x, u)) s) =ᶠ[𝓝 p]
        (fun x => PeriodicPrimitive.primitive (fun u : ℝ => hf x (u : Period)) s) := by
      filter_upwards [hS.mem_nhds hp] with x hx
      rw [show (fun u => h.eval G (x, u)) = (fun u : ℝ => hf x (u : Period)) from
        funext (hhr x hx)]
    rw [heq.fderiv_eq]
  have hhp : (fun s => h.eval G (p, s)) = (fun s : ℝ => hf p (s : Period)) :=
    funext (hhr p hp)
  have hep : (fun s => e.eval G (p, s)) = (fun s : ℝ => ef p (s : Period)) :=
    funext (her p hp)
  change (Expression.add (spanTerm Y C L h.primitive K)
    ((angularSource Y C X₀ V h K e).covariance V q L).primitive).eval G (p, t) = _
  rw [eval_angularCorrection hO hY hC hX hV hd hq hqp hcircle L hh hK he G (hQ hp),
    hhp, hep, hk]
  rfl

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
