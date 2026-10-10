import OAI.Geometry.SurfaceImmersion.Correction.JetPolynomialFullCorrector

namespace OAI

/-! Evaluation identities connecting the finite jet expressions to the
explicit span and covariance formulas of the periodic corrector. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology

namespace ClosedSurfaceR4.JetPolynomial
open PeriodicCorrector CovarianceCorrector

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma spanSolve_decompose (Y C : E) (a b : ℝ) :
    spanSolve Y C (a, b) = a • spanSolve Y C (1, 0) + b • spanSolve Y C (0, 1) := by
  have hp : (a, b) = a • ((1, 0) : ℝ × ℝ) + b • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  conv_lhs => rw [hp, map_add, map_smul, map_smul]

namespace Expression

lemma eval_spanTerm (Y C : LowJet → E) (L : E →L[ℝ] ℝ) (H K : Expression)
    (G : Base → Space) (p : Base) (t : ℝ) :
    (spanTerm Y C L H K).eval G (p, t) =
      L (spanSolve (Y (lowJet G p)) (C (lowJet G p)) (H.eval G (p, t), K.eval G (p, t))) := by
  conv_rhs => rw [spanSolve_decompose]
  simp only [spanTerm, eval, eval_mul, spanCoefficient,
    map_add, map_smul, smul_eq_mul]
  ring

lemma eval_metricTerm (Y C X₀ : LowJet → E) (V : LowJet → C(Period, E))
    (h K : Expression) (G : Base → Space) (p : Base) (t : ℝ) :
    (Expression.add ((Expression.coeff (metricCoefficient Y C X₀ V (1, 0))).mul h)
      ((Expression.coeff (metricCoefficient Y C X₀ V (0, 1))).mul K)).eval G (p, t) =
    inner ℝ (X₀ (lowJet G p) + V (lowJet G p) (t : Period))
      (spanSolve (Y (lowJet G p)) (C (lowJet G p)) (h.eval G (p, t), K.eval G (p, t))) := by
  conv_rhs => rw [spanSolve_decompose]
  simp only [eval, eval_mul, metricCoefficient,
    inner_add_right, inner_smul_right]
  ring

lemma eval_angularSource {O : Set LowJet} (hO : IsOpen O)
    (Y C X₀ : LowJet → E) (V : LowJet → C(Period, E))
    {h K e : Expression} (hh : h.SmoothCoeffs O) (hK : K.SmoothCoeffs O)
    (hb : ∀ b : ℝ × ℝ, ContDiffOn ℝ ∞ (metricCoefficient Y C X₀ V b) (O ×ˢ Set.univ))
    (G : Base → Space) {p : Base} (hp : lowJet G p ∈ O) (t : ℝ) :
    (angularSource Y C X₀ V h K e).eval G (p, t) =
      let a := fun s : ℝ => inner ℝ (X₀ (lowJet G p) + V (lowJet G p) (s : Period))
        (spanSolve (Y (lowJet G p)) (C (lowJet G p))
          (h.eval G (p, s), deriv (fun u => K.eval G (p, u)) s))
      e.eval G (p, t) - (a t - ∫ s in 0..1, a s) := by
  let f : Expression := Expression.add ((Expression.coeff (metricCoefficient Y C X₀ V (1, 0))).mul h)
    ((Expression.coeff (metricCoefficient Y C X₀ V (0, 1))).mul K.angle)
  have hf : f.SmoothCoeffs O :=
    ⟨smoothCoeffs_mul (hb (1, 0)) hh, smoothCoeffs_mul (hb (0, 1)) (smoothCoeffs_angle hO hK)⟩
  have ha (s : ℝ) : f.eval G (p, s) =
      inner ℝ (X₀ (lowJet G p) + V (lowJet G p) (s : Period))
        (spanSolve (Y (lowJet G p)) (C (lowJet G p))
          (h.eval G (p, s), deriv (fun u => K.eval G (p, u)) s)) := by
    rw [show f = Expression.add ((Expression.coeff (metricCoefficient Y C X₀ V (1, 0))).mul h)
      ((Expression.coeff (metricCoefficient Y C X₀ V (0, 1))).mul K.angle) from rfl,
      eval_metricTerm, eval_angle hO hK G hp]
  change (e.sub f.fluct).eval G (p, t) = _
  rw [eval_sub]
  rw [eval_fluct hO hf G hp, ha]
  simp only [ha]

lemma eval_transverseDatum {O : Set LowJet} {S : Set Base} (hO : IsOpen O) (hS : IsOpen S)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    (v : Fin 2) {h j : Expression} (hh : h.SmoothCoeffs O) {p : Base} (hp : p ∈ S) (t : ℝ) :
    ((h.primitive.slow v).sub j).eval G (p, t) =
      fderiv ℝ (fun x => PeriodicPrimitive.primitive (fun s => h.eval G (x, s)) t)
        p (coordinateVector v) - j.eval G (p, t) := by
  rw [eval_sub, eval_slow hO hS hG hQ v (smoothCoeffs_primitive hO hh) hp]
  have heq : (fun x => h.primitive.eval G (x, t)) =ᶠ[nhds p]
      (fun x => PeriodicPrimitive.primitive (fun s => h.eval G (x, s)) t) := by
    filter_upwards [hS.mem_nhds hp] with x hx
    exact eval_primitive hO hh G (hQ hx) t
  rw [heq.fderiv_eq]

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
