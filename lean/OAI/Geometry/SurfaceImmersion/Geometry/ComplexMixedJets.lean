import OAI.Geometry.SurfaceImmersion.Correction.PolynomialVariationScaling

namespace OAI

/-! Complex evaluation of the real polynomial variations, keeping the base
map fixed and complexifying the direction jets. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MixedExpression

abbrev JetData := Fin 4 → List (Fin 2) → Fin 4 → Base → ℂ

def evalComplex : MixedExpression → (Base → Space) → JetData → Base × ℝ → ℂ
  | .coeff c, G, _, z => (c (lowJet G z.1, z.2) : ℂ)
  | .atom i w a e, G, J, z => J i w a z.1 * e.evalComplex G J z
  | .add e f, G, J, z => e.evalComplex G J z + f.evalComplex G J z

def scaleJetSlot (J : JetData) (j : Fin 3) (c : Base → ℂ) : JetData :=
  fun i w a p => if i = j.succ then c p * J i w a p else J i w a p

lemma DegreeIn.evalComplex_scaleSlot {j : Fin 3} {e : MixedExpression} {n : ℕ}
    (he : DegreeIn j e n) (G : Base → Space) (J : JetData) (c : Base → ℂ) (z : Base × ℝ) :
    e.evalComplex G (scaleJetSlot J j c) z = c z.1 ^ n * e.evalComplex G J z := by
  induction he with
  | coeff d => simp only [evalComplex, pow_zero, one_mul]
  | zero n => simp only [evalComplex, Complex.ofReal_zero, mul_zero]
  | other i w a hi h ih =>
    simp only [evalComplex, scaleJetSlot, hi, ↓reduceIte, ih]
    ring
  | same w a h ih =>
    simp only [evalComplex, scaleJetSlot, ↓reduceIte, ih, pow_succ]
    ring
  | add he hf ihe ihf => simp only [evalComplex, ihe, ihf, mul_add]

def scaleJets (J : JetData) (c : Fin 3 → Base → ℂ) : JetData :=
  scaleJetSlot (scaleJetSlot (scaleJetSlot J 0 (c 0)) 1 (c 1)) 2 (c 2)

lemma evalComplex_scaleJets {e : MixedExpression} {n : Fin 3 → ℕ}
    (he : ∀ j, DegreeIn j e (n j)) (G : Base → Space) (J : JetData)
    (c : Fin 3 → Base → ℂ) (z : Base × ℝ) :
    e.evalComplex G (scaleJets J c) z =
      ((c 0 z.1) ^ n 0 * (c 1 z.1) ^ n 1 * (c 2 z.1) ^ n 2) * e.evalComplex G J z := by
  simp only [scaleJets, (he 2).evalComplex_scaleSlot, (he 1).evalComplex_scaleSlot,
    (he 0).evalComplex_scaleSlot]
  ring

lemma evalComplex_smooth {O : Set LowJet} {U : Set Base} {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    {J : JetData} (hJ : ∀ i w a, ContDiffOn ℝ ∞ (J i w a) U)
    {e : MixedExpression} (he : e.SmoothCoeffs O) :
    ContDiffOn ℝ ∞ (e.evalComplex G J) (U ×ˢ Set.univ) := by
  induction e with
  | coeff c =>
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn
      (he.comp (((lowJet_smooth hG).comp contDiff_fst).prodMk contDiff_snd).contDiffOn
        (fun z hz => ⟨hQ hz.1, hz.2⟩))
  | atom i w a e ih =>
    exact ((hJ i w a).comp contDiffOn_fst (fun _ hz => hz.1)).mul (ih he)
  | add e f ihe ihf => exact (ihe he.1).add (ihf he.2)

lemma evalComplex_parameter_smooth {O : Set LowJet} {U : Set Base} {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O)
    {J : JetData} (hJ : ∀ i w a, ContDiffOn ℝ ∞ (J i w a) U)
    {e : MixedExpression} (he : e.SmoothCoeffs O) (t : ℝ) :
    ContDiffOn ℝ ∞ (fun p => e.evalComplex G J (p, t)) U :=
  (evalComplex_smooth hG hQ hJ he).comp (contDiffOn_id.prodMk contDiffOn_const)
    (fun _ hp => ⟨hp, Set.mem_univ t⟩)

end ClosedSurfaceR4.JetPolynomial.MixedExpression

end

end OAI
