import OAI.Geometry.SurfaceImmersion.Correction.JetPolynomialVariation

namespace OAI

/-! The actual polynomial first variation is linear in its smooth direction. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial

lemma variationLowJet_add {H K : Base → Space}
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) (p : Base) :
    variationLowJet (fun q => H q + K q) p = variationLowJet H p + variationLowJet K p := by
  funext i
  cases i with
  | inl i => simp [variationLowJet]
  | inr i => exact jet_add hH hK (lowWord i.1) i.2 p

lemma variationLowJet_smul {H : Base → Space} (hH : ContDiff ℝ ∞ H)
    (c : ℝ) (p : Base) :
    variationLowJet (fun q => c • H q) p = c • variationLowJet H p := by
  funext i
  cases i with
  | inl i => simp [variationLowJet]
  | inr i => exact jet_smul hH c (lowWord i.1) i.2 p

namespace Expression

lemma variation_add (e : Expression) (G : Base → Space) {H K : Base → Space}
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) (z : Base × ℝ) :
    e.variation G (fun q => H q + K q) z = e.variation G H z + e.variation G K z := by
  induction e with
  | coeff c =>
    simp only [variation, variationLowJet_add hH hK]
    have hp : (variationLowJet H z.1 + variationLowJet K z.1, (0 : ℝ)) =
        (variationLowJet H z.1, 0) + (variationLowJet K z.1, 0) := by simp
    rw [hp, map_add]
  | atom w a e ih =>
    simp only [variation, jet_add hH hK, ih]
    ring
  | add e f ihe ihf =>
    simp only [variation, ihe, ihf]
    ring

lemma variation_smul (e : Expression) (G : Base → Space) {H : Base → Space}
    (hH : ContDiff ℝ ∞ H) (c : ℝ) (z : Base × ℝ) :
    e.variation G (fun q => c • H q) z = c * e.variation G H z := by
  induction e with
  | coeff d =>
    simp only [variation, variationLowJet_smul hH]
    have hp : (c • variationLowJet H z.1, (0 : ℝ)) = c • (variationLowJet H z.1, (0 : ℝ)) := by simp
    rw [hp, map_smul]
    rfl
  | atom w a e ih =>
    simp only [variation, jet_smul hH, ih]
    ring
  | add e f ihe ihf =>
    simp only [variation, ihe, ihf]
    ring

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
