import OAI.Geometry.SurfaceImmersion.Atlas.ChartedLeadingTensor
import OAI.Geometry.Immersion.ClosedSurface.PhaseStock
import OAI.Geometry.Immersion.ClosedSurface.AtlasPhases

namespace OAI

/-! A supported phase family has leading tensor equal to the cutoff square
 times its input tensor. This is the local identity used by the global atlas. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes RootMean WeightedEstimates FiniteMean PhaseGeometry

lemma covectorSquare_directions (ξ : SmallModes.Base) (k : Fin 3) :
    covectorSquare ξ k = phaseLinear ξ (firstDirection k) * phaseLinear ξ (secondDirection k) := by
  fin_cases k <;> simp [covectorSquare, firstDirection, secondDirection, phaseLinear_apply,
    SmallModes.dx, SmallModes.dy] <;> ring

theorem charted_cutoff_leading {n : ℕ} {P : Fin 3 → Fin n → Expression}
    {ε τ : ℝ} {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} {c : PolynomialSolveData P ε G hG φ K τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d : ChartedMeanData c r ρ R reference) (hρ : 0 < ρ)
    (χ : SmallModes.Base → ℝ) (Q : Tensor →L[ℝ] ℝ) (ξ : SmallModes.Base) (w : ℝ)
    (hw : w ≠ 0) (hphase : coordinatePhase φ = phaseLinear (w • ξ))
    (hcutoff : ∀ x ∈ c.e.source, d.cutoff (c.e x) = χ x / w)
    (hform : ∀ x ∈ c.e.source, d.form (c.e x) = Q)
    (hsupport : tsupport χ ⊆ c.e.source) {A : SmallModes.Base → Tensor}
    (hA : ContDiff ℝ ∞ A) (hball : InTrialBall Set.univ reference r A) (x : SmallModes.Base) :
    d.leading hρ A x = (χ x)^2 • (Q (A x) • covectorSquare ξ) := by
  rw [d.leading_apply hρ hA hball]
  by_cases hx : x ∈ c.e.source
  · rw [Set.indicator_of_mem hx]
    have hd (v : SmallModes.Base) : fderiv ℝ (coordinatePhase φ) x v = w * phaseLinear ξ v := by
      rw [hphase, (phaseLinear (w • ξ)).fderiv]
      simp only [phaseLinear_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    ext k
    simp only [hcutoff x hx, hform x hx, hd, Pi.smul_apply, smul_eq_mul,
      covectorSquare_directions]
    field_simp [hw]
  · have hz : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hsupport h))
    simp only [Set.indicator_of_notMem hx, hz, zero_pow (by decide : 2 ≠ 0), zero_smul]

theorem charted_partition_leading {n : ℕ} {P : Fin 3 → Fin n → Expression}
    {ε τ : ℝ} {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Fin 3 → Base → ℝ}
    {K : Fin 3 → Compacts Base} {s : ℝ≥0}
    {c : ∀ j, PolynomialSolveData P ε G hG (φ j) (K j) τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d : ∀ j, ChartedMeanData (c j) r ρ R reference) (hρ : 0 < ρ)
    (χ : SmallModes.Base → ℝ) (Q : PhaseBasis) (w : Fin 3 → ℝ)
    (hw : ∀ j, w j ≠ 0) (hphase : ∀ j, coordinatePhase (φ j) = phaseLinear (w j • Q.ξ j))
    (hcutoff : ∀ j x, x ∈ (c j).e.source → (d j).cutoff ((c j).e x) = χ x / w j)
    (hform : ∀ j x, x ∈ (c j).e.source → (d j).form ((c j).e x) = Q.Q j)
    (hsupport : ∀ j, tsupport χ ⊆ (c j).e.source) {A : SmallModes.Base → Tensor}
    (hA : ContDiff ℝ ∞ A) (hball : InTrialBall Set.univ reference r A) :
    chartedFamilyLeading d hρ A = fun x => (χ x)^2 • A x := by
  funext x
  change (∑ j : Fin 3, (d j).leading hρ A x) = _
  simp_rw [charted_cutoff_leading _ hρ χ _ _ _ (hw _) (hphase _) (hcutoff _) (hform _)
    (hsupport _) hA hball]
  rw [← Finset.smul_sum, Q.decomposition]

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
