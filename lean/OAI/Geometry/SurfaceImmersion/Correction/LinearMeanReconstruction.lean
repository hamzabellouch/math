import OAI.Geometry.SurfaceImmersion.Atlas.ChartedPartitionLeading
import OAI.Geometry.SurfaceImmersion.Correction.ChartedMeanFamilyData

namespace OAI

/-! The actual leading mean reconstructs the input tensor on an inner
domain where the common cutoff is one.  Outside this domain its exact
formula retains the cutoff square. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes PhaseGeometry FiniteMean

/-- The supported phase-chart cutoff with its inverse frequency factor. -/
def supportedPhaseCutoff {K : Compacts SmallModes.Base}
    (χ : SupportedField (F := ℝ) K)
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e.symm e.target) (hK : (K : Set SmallModes.Base) ⊆ e.source)
    (w : ℝ) : SupportedField (F := ℝ) (chartSupport e K hK) :=
  w⁻¹ • chartPush e he K hK χ

lemma supportedPhaseCutoff_eval_source {K : Compacts SmallModes.Base}
    (χ : SupportedField (F := ℝ) K)
    (e : OpenPartialHomeomorph SmallModes.Base SmallModes.Base)
    (he : ContDiffOn ℝ ∞ e.symm e.target) (hK : (K : Set SmallModes.Base) ⊆ e.source)
    (w : ℝ) {x : SmallModes.Base} (hx : x ∈ e.source) :
    supportedPhaseCutoff χ e he hK w (e x) = χ x / w := by
  change w⁻¹ * chartPush e he K hK χ (e x) = _
  rw [chartPush_eval_source e he K hK χ hx]
  exact (div_eq_inv_mul _ _).symm

theorem linear_mean_reconstruction_on {n : ℕ} {P : Fin 3 → Fin n → Expression}
    {ε τ : ℝ} {s : ℝ≥0} {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d : ChartedMeanFamilyData P ε τ s r ρ R reference) (hρ : 0 < ρ)
    (Q : PhaseBasis) (w : Fin 3 → ℝ) (hw : ∀ j, w j ≠ 0)
    (χ : SmallModes.Base → ℝ) (ψ : Fin 3 → SmallModes.Base → ℝ)
    (hphase : ∀ j, coordinatePhase (d.phase j) = phaseLinear (w j • Q.ξ j))
    (hcutoff : ∀ j x, (d.data j).cutoff x = ψ j x)
    (htransport : ∀ j x, x ∈ (d.solver j).e.source →
      ψ j ((d.solver j).e x) = χ x / w j)
    (hform : ∀ j, (d.data j).form = fun _ => Q.Q j)
    (hsupport : ∀ j, tsupport χ ⊆ (d.solver j).e.source)
    (D : Set SmallModes.Base) (hχ : ∀ x ∈ D, χ x = 1) :
    ∀ A : SmallModes.Base → Tensor, ContDiff ℝ ∞ A →
      InTrialBall Set.univ reference r A →
      ∀ x ∈ D, chartedFamilyLeading d.data hρ A x = A x := by
  intro A hA hball x hx
  have he := charted_partition_leading d.data hρ χ Q w hw hphase
    (fun j y hy => (hcutoff j _).trans (htransport j y hy))
    (fun j y _ => congrFun (hform j) ((d.solver j).e y)) hsupport hA hball
  simpa only [hχ x hx,one_pow,one_smul] using congrFun he x

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
