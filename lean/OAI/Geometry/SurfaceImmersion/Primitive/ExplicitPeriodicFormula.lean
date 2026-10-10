import OAI.Geometry.SurfaceImmersion.Correction.JetPolynomialEvaluation
import OAI.Geometry.SurfaceImmersion.Correction.PeriodicCorrectorFormula

namespace OAI

/-! The polynomial expression evaluates to the explicit vector-valued
periodic correction, including its covariance inverse and normalized integral. -/
noncomputable section
open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open PeriodicCorrector CovarianceCorrector

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma realCorrector_continuous (V : C(Period, E)) (q : ℝ) {f : ℝ → ℝ}
    (hf : Continuous f) : Continuous (realCorrector V q f) := by
  have hv : Continuous (fun t : ℝ => V (t : Period)) :=
    V.continuous.comp (AddCircle.continuous_mk' 1)
  exact continuous_const.smul ((hf.add (((hv.sub continuous_const).inner continuous_const).div_const q)).smul hv
    |>.sub continuous_const)

variable [CompleteSpace E]

lemma primitive_map (L : E →L[ℝ] ℝ) {f : ℝ → E} (hf : Continuous f) (t : ℝ) :
    L (PeriodicPrimitive.primitive f t) = PeriodicPrimitive.primitive (fun s => L (f s)) t := by
  have hr (s : ℝ) : L (PeriodicPrimitive.rawPrimitive f s) =
      PeriodicPrimitive.rawPrimitive (fun u => L (f u)) s :=
    (L.intervalIntegral_comp_comm (hf.intervalIntegrable 0 s)).symm
  simp only [PeriodicPrimitive.primitive, map_sub, hr]
  rw [← L.intervalIntegral_comp_comm
    ((PeriodicPrimitive.rawPrimitive_continuous hf).intervalIntegrable 0 1)]
  simp only [hr]

variable [FiniteDimensional ℝ E]

namespace Expression

/-- The symbolic construction is exactly the span-plus-integrated-covariance
formula, not just a formal expression with a similar order bound. -/
theorem eval_angularCorrection {O : Set LowJet} (hO : IsOpen O)
    {Y C X₀ : LowJet → E} {V : LowJet → C(Period, E)} {q : LowJet → ℝ}
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O) (hX : ContDiffOn ℝ ∞ X₀ O)
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hd : ∀ Q ∈ O, gramDet (Y Q) (C Q) ≠ 0)
    (hq : ContDiffOn ℝ ∞ q O) (hqp : ∀ Q ∈ O, 0 < q Q)
    (hcircle : ∀ Q ∈ O, ∀ t, inner ℝ (V Q t) (V Q t) = q Q)
    (L : E →L[ℝ] ℝ) {h K e : Expression}
    (hh : h.SmoothCoeffs O) (hK : K.SmoothCoeffs O) (he : e.SmoothCoeffs O)
    (G : Base → Space) {p : Base} (hp : lowJet G p ∈ O) (t : ℝ) :
    (Expression.add (spanTerm Y C L h.primitive K)
      ((angularSource Y C X₀ V h K e).covariance V q L).primitive).eval G (p, t) =
    L (angularCorrectionFunction (Y (lowJet G p)) (C (lowJet G p)) (X₀ (lowJet G p))
      (V (lowJet G p)) (q (lowJet G p))
      (fun s => h.eval G (p, s)) (fun s => K.eval G (p, s)) (fun s => e.eval G (p, s)) t) := by
  let r := angularSource Y C X₀ V h K e
  have hr : r.SmoothCoeffs O := smoothCoeffs_angularSource hO hY hC hX hV hd hh hK he
  have hw := smoothCoeffs_covariance hO hV hq hqp hcircle L hr
  have hb (b : ℝ × ℝ) : ContDiffOn ℝ ∞ (metricCoefficient Y C X₀ V b) (O ×ˢ Set.univ) :=
    ((hX.comp contDiffOn_fst (fun _ hz => hz.1)).add hV).inner ℝ
      ((contDiffOn_spanSolve hY hC contDiffOn_const hd).comp contDiffOn_fst (fun _ hz => hz.1))
  have hs (s : ℝ) : r.eval G (p, s) =
      angularSourceFunction (Y (lowJet G p)) (C (lowJet G p)) (X₀ (lowJet G p))
        (V (lowJet G p)) (fun u => h.eval G (p, u)) (fun u => K.eval G (p, u))
        (fun u => e.eval G (p, u)) s :=
    eval_angularSource hO Y C X₀ V hh hK hb G hp s
  have hf : Continuous (fun s => r.eval G (p, s)) := (eval_slice_smooth hO hr G hp).continuous
  have hW := realCorrector_continuous (V (lowJet G p)) (q (lowJet G p)) hf
  change (spanTerm Y C L h.primitive K).eval G (p, t) +
    (r.covariance V q L).primitive.eval G (p, t) = _
  rw [eval_spanTerm, eval_primitive hO hh G hp, eval_primitive hO hw G hp]
  simp only [angularCorrectionFunction, map_add]
  have heq : (fun s => r.eval G (p, s)) =
      angularSourceFunction (Y (lowJet G p)) (C (lowJet G p)) (X₀ (lowJet G p))
        (V (lowJet G p)) (fun u => h.eval G (p, u)) (fun u => K.eval G (p, u))
        (fun u => e.eval G (p, u)) := funext hs
  rw [← heq, primitive_map L hW]
  congr 1
  congr 1
  funext s
  exact eval_covariance hO V q L hr G hp s

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
