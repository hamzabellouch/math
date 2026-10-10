import OAI.Geometry.SurfaceImmersion.Geometry.JetVariations
import OAI.Geometry.SurfaceImmersion.Correction.JetPolynomialAlgebra

namespace OAI

/-! The first variation of an actual higher-jet polynomial, including the
variation of its smooth second-jet coefficients. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.Expression
open WeightedEstimates

def variation : Expression → (Base → Space) → (Base → Space) → Base × ℝ → ℝ
  | .coeff c, G, H, z =>
      fderiv ℝ c (lowJet G z.1, z.2) (variationLowJet H z.1, 0)
  | .atom w a e, G, H, z =>
      jet H w a z.1 * e.eval G z + jet G w a z.1 * e.variation G H z
  | .add e f, G, H, z => e.variation G H z + f.variation G H z

theorem variation_hasDerivAt {O : Set LowJet} (hO : IsOpen O)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    {e : Expression} (he : e.SmoothCoeffs O) (z : Base × ℝ)
    (hQ : lowJet G z.1 ∈ O) :
    HasDerivAt (fun s : ℝ => e.eval (fun p => G p + s • H p) z) (e.variation G H z) 0 := by
  induction e with
  | coeff c =>
    have hmem : (lowJet G z.1, z.2) ∈ O ×ˢ Set.univ := ⟨hQ, Set.mem_univ z.2⟩
    have hc : DifferentiableAt ℝ c (lowJet G z.1, z.2) :=
      (he.contDiffAt ((hO.prod isOpen_univ).mem_nhds hmem)).differentiableAt (by simp)
    have hj := (lowJet_affine_hasDerivAt hG hH z.1 0).prodMk (hasDerivAt_const 0 z.2)
    have hd := hc.hasFDerivAt.comp_hasDerivAt_of_eq 0 hj (by simp)
    simpa only [Function.comp_def, zero_smul, add_zero, eval, variation] using hd
  | atom w a e ih =>
    have hj : HasDerivAt (fun s : ℝ => jet (fun p => G p + s • H p) w a z.1)
        (jet H w a z.1) 0 := by
      have hpath : (fun s : ℝ => jet (fun p => G p + s • H p) w a z.1) =
          (fun s : ℝ => jet G w a z.1 + s * jet H w a z.1) := by
        funext s
        rw [jet_add (H := fun p => s • H p) hG (ContDiff.const_smul s hH), jet_smul hH]
      rw [hpath]
      simpa only [one_mul, id_eq] using
        ((hasDerivAt_id (0 : ℝ)).mul_const (jet H w a z.1)).const_add (jet G w a z.1)
    have hzero : (fun p => G p + (0 : ℝ) • H p) = G := by funext p; simp
    simpa only [eval, variation, hzero, Pi.mul_apply] using hj.fun_mul (ih he)
  | add e f ihe ihf =>
    exact (ihe he.1).add (ihf he.2)

theorem variation_smooth {O : Set LowJet} (hO : IsOpen O) {U : Set Base}
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (hQ : Set.MapsTo (lowJet G) U O) {e : Expression} (he : e.SmoothCoeffs O) :
    ContDiffOn ℝ ∞ (e.variation G H) (U ×ˢ Set.univ) := by
  induction e with
  | coeff c =>
    have hc : ContDiffOn ℝ ∞ (fderiv ℝ c) (O ×ˢ Set.univ) :=
      he.fderiv_of_isOpen (hO.prod isOpen_univ) (m := ∞) (by simp)
    exact (hc.comp (((lowJet_smooth hG).comp contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun z hz => ⟨hQ hz.1, hz.2⟩)).clm_apply
        (((variationLowJet_smooth hH).comp contDiff_fst).prodMk contDiff_const).contDiffOn
  | atom w a e ih =>
    exact (((jet_smooth hH w a).comp contDiff_fst).contDiffOn.mul (eval_smooth (e := e) hG hQ he)).add
      (((jet_smooth hG w a).comp contDiff_fst).contDiffOn.mul (ih he))
  | add e f ihe ihf => exact (ihe he.1).add (ihf he.2)

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
