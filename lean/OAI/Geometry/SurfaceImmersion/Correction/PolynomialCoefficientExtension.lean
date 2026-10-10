import OAI.Geometry.SurfaceImmersion.Correction.JetPolynomialAlgebra
import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs
import OAI.Geometry.SurfaceImmersion.Geometry.LocalParameterIntegral

namespace OAI

/-! Coefficients can be extended smoothly off the permitted compact low-jet
set without changing the operator there or changing its jet order/loss. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.Expression

def cutoffCoeffs (e : Expression) (χ : LowJet → ℝ) : Expression :=
  e.mapCoeff (fun c z => χ z.1 * c z)

lemma cutoffCoeffs_smooth {e : Expression} {O : Set LowJet} (hO : IsOpen O)
    (he : e.SmoothCoeffs O) {χ : LowJet → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ O) : (e.cutoffCoeffs χ).SmoothCoeffs Set.univ := by
  induction e with
  | coeff c =>
    have hc := SmoothParameterIntegral.contDiff_supported_smul hO he hχ hs
    change ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => χ z.1 * c z) (Set.univ ×ˢ Set.univ)
    exact hc.contDiffOn
  | atom w a e ih => exact ih he
  | add e f ihe ihf => exact ⟨ihe he.1, ihf he.2⟩

lemma cutoffCoeffs_eval (e : Expression) (χ : LowJet → ℝ) (G : Base → Space) (z : Base × ℝ) :
    (e.cutoffCoeffs χ).eval G z = χ (lowJet G z.1) * e.eval G z :=
  e.eval_mapCoeff_mul G (fun x => χ x.1) z

/-- Only the compact set of low jets used by the application is retained. -/
theorem exists_global_extension {e : Expression} {O Q : Set LowJet}
    (hO : IsOpen O) (he : e.SmoothCoeffs O) (hQ : IsCompact Q) (hQO : Q ⊆ O) :
    ∃ e' : Expression, e'.SmoothCoeffs Set.univ ∧ e'.order = e.order ∧ e'.loss = e.loss ∧
      ∀ (G : Base → Space) (z : Base × ℝ), lowJet G z.1 ∈ Q → e'.eval G z = e.eval G z := by
  obtain ⟨χ, hχ, _, _, hs, hχone⟩ := CollarVelocity.compact_cutoff hQ hO hQO
  refine ⟨e.cutoffCoeffs χ, cutoffCoeffs_smooth hO he hχ hs, ?_, ?_, ?_⟩
  · exact e.order_mapCoeff _
  · exact e.loss_mapCoeff _
  · intro G z hz
    rw [cutoffCoeffs_eval, hχone _ hz, one_mul]

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
