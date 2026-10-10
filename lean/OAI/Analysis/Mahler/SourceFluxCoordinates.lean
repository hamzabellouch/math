import OAI.Analysis.Mahler.SourceTopCoordinates
import OAI.Analysis.Mahler.SourceCoordinateForms
import OAI.Analysis.Mahler.ExactSphereFluxBridge

namespace OAI

noncomputable section
open Set Metric MeasureTheory
namespace Mahler

lemma powerFinEquiv_interleaved (k : ℕ) (s : WedgePowerSlots k) :
    (powerFinEquiv k s).val = (finProdFinEquiv (pairSlotEquiv k s)).val := by
  induction k with
  | zero => exact Fin.elim0 s
  | succ k ih =>
    cases s with
    | inl b => fin_cases b <;> rfl
    | inr s =>
      change 2 + (powerFinEquiv k s).val =
        (pairSlotEquiv k s).2.val + 2 * ((pairSlotEquiv k s).1.val + 1)
      rw [ih]
      change 2 + ((pairSlotEquiv k s).2.val + 2 * (pairSlotEquiv k s).1.val) = _
      omega

lemma sourceBoundarySlots_eq_boundaryFinEquiv (k : ℕ) :
    sourceBoundarySlots k = boundaryFinEquiv k := by
  ext s
  cases s with
  | inl i => rfl
  | inr s =>
    change 1 + (finProdFinEquiv (pairSlotEquiv k s)).val = 1 + (powerFinEquiv k s).val
    rw [powerFinEquiv_interleaved]

lemma sourceTopSlots_eq_ambientFinEquiv (k : ℕ) :
    sourceTopSlots k = ambientFinEquiv k := by
  ext s
  exact (sourceTopSlots_interleaved k s).trans (powerFinEquiv_interleaved (k+1) s).symm

/-- Coordinate Stokes and cofactor sphere integration use the
positive interleaved coordinate map, including the ambient degree cast. -/
theorem sourceCoordinates_eq_fluxCoordinates (k : ℕ) :
    sourceCoordinates k = fluxCoordinates k := by
  apply ContinuousLinearEquiv.toLinearEquiv_injective
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun ℝ (Fin ((2*k+1)+1))).ext
  intro i
  obtain ⟨s, rfl⟩ := (sourceTopSlots k).surjective i
  simp only [Pi.basisFun_apply]
  change sourceCoordinates k (MahlerStokes.coordinateBasis _ (sourceTopSlots k s)) =
    fluxCoordinates k (MahlerStokes.coordinateBasis _ (sourceTopSlots k s))
  rw [sourceCoordinates_top_basis, fluxCoordinates_basis,
    sourceTopSlots_eq_ambientFinEquiv, sphereFrame_interleaved]

/-- The bundled complex form, with its specified boundary slot order. -/
def sourceFluxForm {k : ℕ} (u : ComplexEuclidean (k+1) → ℂ)
    (x : ComplexEuclidean (k+1)) :
    ComplexEuclidean (k+1) [⋀^Fin (2*k+1)]→L[ℝ] ℂ :=
  sourceReindex (sourceBoundarySlots k) (continuousSourceBoundaryForm u k x)

lemma sourceCoordinateForm_eq_fluxPullback {k : ℕ} (u : ComplexEuclidean (k+1) → ℂ) :
    sourceCoordinateForm (sourceCoordinates k) u k = fluxPullback (sourceFluxForm u) := by
  rw [sourceCoordinates_eq_fluxCoordinates]
  rfl

lemma sourceFluxForm_toAlternatingMap {k : ℕ} (u : ComplexEuclidean (k+1) → ℂ)
    (x : ComplexEuclidean (k+1)) :
    (sourceFluxForm u x).toAlternatingMap = boundaryFormFin (dcLinear u) x := by
  change (continuousSourceBoundaryForm u k x).toAlternatingMap.domDomCongr
    (sourceBoundarySlots k) = _
  rw [continuousSourceBoundaryForm_eq, sourceBoundarySlots_eq_boundaryFinEquiv]
  rfl

lemma contDiffAt_sourceFluxForm {k : ℕ} {u : ComplexEuclidean (k+1) → ℂ}
    {x : ComplexEuclidean (k+1)} (hu : ContDiffAt ℝ 3 u x) :
    ContDiffAt ℝ 1 (sourceFluxForm u) x :=
  (sourceReindexCLM (E := ComplexEuclidean (k+1)) (sourceBoundarySlots k)).contDiff.contDiffAt.comp x
    (contDiffAt_sourceBoundaryForm hu k)

end Mahler

end

end OAI
