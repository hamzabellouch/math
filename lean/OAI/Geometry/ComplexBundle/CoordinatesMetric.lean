import OAI.Geometry.ComplexBundle.Frames
import OAI.Geometry.ComplexBundle.SmoothLine

namespace OAI

noncomputable section

/-! Finite-coordinate smooth bundles and their metrics. -/

section
open Bundle Topology
open scoped Manifold ContDiff
namespace Kaplansky
open ComplexGrassmann
variable {S ι : Type*} [Fintype S] [Fintype ι]

def finiteCoordinateEquiv (d : ℕ) (hd : Fintype.card S=d) :
    EuclideanSpace ℂ S ≃L[ℂ] (Fin d → ℂ) :=
  (LinearEquiv.ofFinrankEq (R := ℂ) (EuclideanSpace ℂ S) (Fin d → ℂ) (by simpa using hd)).toContinuousLinearEquiv

variable (K : ι → ℕ) (label : S → Option ι) (d : ℕ) (hd : Fintype.card S=d)

def finiteCoordinateCore := changeModelCore (smoothLineSumCore K label) (finiteCoordinateEquiv d hd)
abbrev FiniteCoordinateBundle := (finiteCoordinateCore K label d hd).Fiber

instance finiteCoordinateBundle_norm (P : ProjectiveProduct K) :
    NormedAddCommGroup (FiniteCoordinateBundle K label d hd P) := changeModelFiberNorm _ _ P
instance finiteCoordinateBundle_normedSpace (P : ProjectiveProduct K) :
    NormedSpace ℂ (FiniteCoordinateBundle K label d hd P) := changeModelFiberNormedSpace _ _ P

instance finiteCoordinateBundle_smooth : ContMDiffVectorBundle ∞ (Fin d → ℂ)
    (FiniteCoordinateBundle K label d hd) 𝓘(ℝ,ProjectiveProductModel K) :=
  complexCore_contMDiffVectorBundle _ _ (changeModelCore_transition_smooth _ _ _
    (finiteLineSumCore_transition_smooth _ _ (fun s => productLineCore_transition_smooth K (label s))))

/-- The finite-coordinate presentation is the same actual bundle, through
an explicit base-preserving linear homeomorphism of total spaces. -/
def finiteCoordinateTotalHomeomorph :
    TotalSpace (EuclideanSpace ℂ S) (SmoothLineSumBundle K label) ≃ₜ
      TotalSpace (Fin d → ℂ) (FiniteCoordinateBundle K label d hd) :=
  changeModelCoreTotalHomeomorph _ _

end Kaplansky

end

open Bundle Topology
namespace Kaplansky
open ComplexGrassmann
variable {S ι : Type*} [Fintype S] [Fintype ι]
  (K : ι → ℕ) (label : S → Option ι) (d : ℕ) (hd : Fintype.card S=d)

/-- Pull back the Hilbert norm, keeping the already constructed fiber topology. -/
instance (priority := 2000) finiteCoordinateHilbertNorm (P : ProjectiveProduct K) :
    NormedAddCommGroup (FiniteCoordinateBundle K label d hd P) := by
  let e := (finiteCoordinateEquiv d hd).symm
  let N := NormedAddCommGroup.induced (FiniteCoordinateBundle K label d hd P)
    (EuclideanSpace ℂ S) e.toLinearEquiv.toAddEquiv e.injective
  exact { N.replaceTopology e.toHomeomorph.isInducing.eq_induced with
    norm := N.norm
    dist_eq := N.dist_eq }

instance (priority := 2000) finiteCoordinateHilbertInner (P : ProjectiveProduct K) :
    InnerProductSpace ℂ (FiniteCoordinateBundle K label d hd P) := by
  let e : FiniteCoordinateBundle K label d hd P ≃ₗ[ℂ] EuclideanSpace ℂ S :=
    (finiteCoordinateEquiv d hd).symm.toLinearEquiv
  exact
    { norm_smul_le := fun z v => by
        change ‖e (z • v)‖ ≤ ‖z‖ * ‖e v‖
        rw [map_smul, norm_smul]
      inner := fun v w => inner ℂ (e v) (e w)
      add_left := fun v w z => by simp only [map_add, inner_add_left]
      smul_left := fun v w z => by simp only [map_smul, inner_smul_left]
      norm_sq_eq_re_inner := fun v => norm_sq_eq_re_inner (e v)
      conj_inner_symm := fun v w => inner_conj_symm _ _ }

omit [Fintype ι] in
/-- The actual sum metric is continuous in the finite-coordinate presentation. -/
theorem finiteCoordinate_continuousHermitianMetric :
    ContinuousHermitianMetric (d := d) (E := FiniteCoordinateBundle K label d hd) := by
  intro A v w hv hw
  let H := finiteCoordinateTotalHomeomorph K label d hd
  have hv' := H.symm.continuous.comp_continuousOn hv
  have hw' := H.symm.continuous.comp_continuousOn hw
  exact smoothLineSum_inner_continuousOn K label A
    (fun P => (finiteCoordinateEquiv d hd).symm (v P))
    (fun P => (finiteCoordinateEquiv d hd).symm (w P)) hv' hw'

end Kaplansky

end

end OAI
