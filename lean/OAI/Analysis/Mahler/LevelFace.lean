import OAI.Analysis.Mahler.RegularChartStokes
import OAI.Analysis.Mahler.DCRegularity

namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace MahlerStokes

def coordinateFace {n : ℕ} (k : Fin (n+1)) (R : ℝ) (y : Fin n → ℝ) : Fin (n+1) → ℝ :=
  k.insertNth R y

lemma contDiff_coordinateFace {n : ℕ} (k : Fin (n+1)) (R : ℝ) :
    ContDiff ℝ 2 (coordinateFace k R) := by
  apply contDiff_pi.mpr
  rw [k.forall_iff_succAbove]
  constructor
  · simpa [coordinateFace] using (contDiff_const (c := R) : ContDiff ℝ 2 (fun _ : Fin n → ℝ => R))
  · intro j
    simpa [coordinateFace] using (contDiff_apply ℝ ℝ j : ContDiff ℝ 2 (fun y : Fin n → ℝ => y j))

def faceLinear {n : ℕ} (k : Fin (n+1)) : (Fin n → ℝ) →L[ℝ] (Fin (n+1) → ℝ) :=
  ContinuousLinearMap.pi (k.insertNth (0 : (Fin n → ℝ) →L[ℝ] ℝ)
    (fun j : Fin n => ContinuousLinearMap.proj j))

lemma hasFDerivAt_coordinateFace {n : ℕ} (k : Fin (n+1)) (R : ℝ) (y : Fin n → ℝ) :
    HasFDerivAt (coordinateFace k R) (faceLinear k) y := by
  apply hasFDerivAt_pi.mpr
  rw [k.forall_iff_succAbove]
  constructor
  · simpa [coordinateFace, faceLinear] using (hasFDerivAt_const R y)
  · intro j
    simpa [coordinateFace, faceLinear] using (hasFDerivAt_apply j y)

lemma faceLinear_basis {n : ℕ} (k : Fin (n+1)) (j : Fin n) :
    faceLinear k (coordinateBasis n j) = k.removeNth (coordinateBasis (n+1)) j := by
  ext i
  revert i
  rw [k.forall_iff_succAbove]
  constructor
  · simp [faceLinear, coordinateBasis, Fin.removeNth]
  · intro i
    simp [faceLinear, coordinateBasis, Fin.removeNth, Pi.single_apply]

/-- The coefficient on a coordinate boundary face equals the actual
pullback coefficient of its lower-dimensional parametrization. -/
theorem pullback_coordinateFace_coefficient {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : Fin (n+1)) (R : ℝ) (ψ : (Fin (n+1) → ℝ) → E)
    (ω : E → E [⋀^Fin n]→L[ℝ] ℝ) (y : Fin n → ℝ)
    (hψ : DifferentiableAt ℝ ψ (coordinateFace k R y)) :
    pullbackForm (fun z => ψ (coordinateFace k R z)) ω y (coordinateBasis n) =
      pullbackForm ψ ω (coordinateFace k R y) (k.removeNth (coordinateBasis (n+1))) := by
  have hd := hψ.hasFDerivAt.comp y (hasFDerivAt_coordinateFace k R y)
  change HasFDerivAt (fun z => ψ (coordinateFace k R z)) _ y at hd
  unfold pullbackForm
  rw [hd.fderiv]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, Function.comp_def,
    ContinuousLinearMap.comp_apply, faceLinear_basis]

namespace RegularBoundaryPatch
variable {n : ℕ} {U : Set (Fin (n+1) → ℝ)} {g : (Fin (n+1) → ℝ) → ℝ}

def faceParam (p : RegularBoundaryPatch (n+1) U g) (R : ℝ) (y : Fin n → ℝ) :=
  p.chart.symm (coordinateFace p.coordinate R y)

def faceDomain (p : RegularBoundaryPatch (n+1) U g) (R : ℝ) : Set (Fin n → ℝ) :=
  (coordinateFace p.coordinate R) ⁻¹' (p.chart.target ∩ p.chart.symm ⁻¹' p.domain)

 theorem isOpen_faceDomain (p : RegularBoundaryPatch (n+1) U g) (R : ℝ) : IsOpen (p.faceDomain R) :=
  ((p.chart.symm.continuousOn.isOpen_inter_preimage p.chart.open_target p.open_domain).preimage
    (contDiff_coordinateFace p.coordinate R).continuous)

 theorem faceParam_mem (p : RegularBoundaryPatch (n+1) U g) (R : ℝ)
    {y : Fin n → ℝ} (hy : y ∈ p.faceDomain R) : p.faceParam R y ∈ p.domain := hy.2

 theorem contDiffAt_faceParam (p : RegularBoundaryPatch (n+1) U g) (R : ℝ)
    {y : Fin n → ℝ} (hy : y ∈ p.faceDomain R) : ContDiffAt ℝ 2 (p.faceParam R) y :=
  (p.smooth_inverse.contDiffAt (p.chart.open_target.mem_nhds hy.1)).comp y
    (contDiff_coordinateFace p.coordinate R).contDiffAt

/-- This parametrizes the actual regular level; the level equation is
proved from the inverse chart identity. -/
theorem level_faceParam (p : RegularBoundaryPatch (n+1) U g) (R : ℝ)
    {y : Fin n → ℝ} (hy : y ∈ p.faceDomain R) : g (p.faceParam R y) = R := by
  have h := congrFun (p.chart.right_inv hy.1) p.coordinate
  rw [p.chart_eq] at h
  simpa [faceParam, levelCoordinates, coordinateFace] using h
end RegularBoundaryPatch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- Real-coordinate regular charts supply actual complex-valued level
parametrizations, for any chosen real continuous linear coordinate equivalence. -/
theorem pullback_dc_log_regular_face {n : ℕ} {U : Set (Fin (n+1) → ℝ)}
    (Ψ : (Fin (n+1) → ℝ) ≃L[ℝ] E) (τ : E → ℝ)
    (p : RegularBoundaryPatch (n+1) U (fun x => τ (Ψ x))) {R : ℝ} (hR : 0 < R)
    {y : Fin n → ℝ} (hy : y ∈ p.faceDomain R)
    (hτ : ∀ x ∈ Ψ '' U, DifferentiableAt ℝ τ x) :
    pullbackForm (fun z => Ψ (p.faceParam R z)) (dcForm (fun x => Real.log (τ x))) y =
      R⁻¹ • pullbackForm (fun z => Ψ (p.faceParam R z)) (dcForm τ) y := by
  apply pullback_dc_log_level hR
  · exact hτ _ ⟨p.faceParam R y, p.domain_U (p.faceParam_mem R hy), rfl⟩
  · exact p.level_faceParam R hy

 theorem pullback_ddc_log_regular_face {n : ℕ} {U : Set (Fin (n+1) → ℝ)}
    (Ψ : (Fin (n+1) → ℝ) ≃L[ℝ] E) (τ : E → ℝ)
    (p : RegularBoundaryPatch (n+1) U (fun x => τ (Ψ x))) {R : ℝ} (hR : 0 < R)
    {y : Fin n → ℝ} (hy : y ∈ p.faceDomain R)
    (hU : IsOpen U) (hτ : ContDiffOn ℝ 2 τ (Ψ '' U)) :
    pullbackForm (fun z => Ψ (p.faceParam R z)) (extDeriv (dcForm (fun x => Real.log (τ x)))) y =
      R⁻¹ • pullbackForm (fun z => Ψ (p.faceParam R z)) (extDeriv (dcForm τ)) y := by
  have hIU : IsOpen (Ψ '' U) := Ψ.toHomeomorph.isOpenMap _ hU
  have hτat (z : Fin n → ℝ) (hz : z ∈ p.faceDomain R) :
      ContDiffAt ℝ 2 τ (Ψ (p.faceParam R z)) :=
    hτ.contDiffAt (hIU.mem_nhds ⟨p.faceParam R z, p.domain_U (p.faceParam_mem R hz), rfl⟩)
  apply pullback_ddc_log_level (p.isOpen_faceDomain R) hy hR
  · intro z hz
    exact (hτat z hz).differentiableAt (by simp)
  · intro z hz
    exact p.level_faceParam R hz
  · exact Ψ.contDiff.contDiffAt.comp y (p.contDiffAt_faceParam R hy)
  · exact (contDiffAt_dcForm (hτat y hy)).differentiableAt one_ne_zero
  · exact (contDiffAt_dcForm_log (hτat y hy)
      ((p.level_faceParam R hy).symm ▸ hR)).differentiableAt one_ne_zero

end MahlerStokes

end

end OAI
