import Mathlib
import OAI.Geometry.SmoothYau.Estimates.LpInverseGramFstContraction
import OAI.Geometry.SmoothYau.Model
import OAI.Geometry.SmoothYau.Smoothness.LinearPowerDirectional

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace
variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [FiniteDimensional ℝ A] {n : ℕ} [Fact (Module.finrank ℝ A = n+1)]
omit [FiniteDimensional ℝ A]
def unitSphereFrame (p : Metric.sphere (0 : A) 1) : Euclidean n →ₗᵢ[ℝ] A :=
  (ℝ ∙ (-(p : A)))ᗮ.subtypeₗᵢ.comp
    (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere (-p))).repr.symm.toLinearIsometry

lemma unitSphereFrame_orthogonal (p : Metric.sphere (0 : A) 1) (w : Euclidean n) :
    inner ℝ (p : A) (unitSphereFrame p w) = 0 := by
  have hh := ((OrthonormalBasis.fromOrthogonalSpanSingleton n
    (ne_zero_of_mem_unit_sphere (-p))).repr.symm w).property
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at hh
  change inner ℝ (p : A) _ = 0
  rw [real_inner_comm]
  change inner ℝ _ (-(p : A)) = 0 at hh
  rw [inner_neg_right,neg_eq_zero] at hh
  exact hh

lemma unitSphere_chart_symm (p : Metric.sphere (0 : A) 1) :
    (fun y => ((chartAt (Euclidean n) p).symm y : A)) =
      roundChart (p : A) (unitSphereFrame p) := by
  funext y
  change ((stereographic' n (-p)).symm y : A) = _
  rw [stereographic'_symm_apply]
  simp only [roundChart,unitSphereFrame,stereoInvFunAux,smul_add,smul_smul]
  rfl

lemma unitSphere_chart_center (p : Metric.sphere (0 : A) 1) : chartAt (Euclidean n) p p = 0 := by
  have hh : (chartAt (Euclidean n) p).symm 0 = p := by
    apply Subtype.ext
    change (fun y => ((chartAt (Euclidean n) p).symm y : A)) 0 = _
    rw [unitSphere_chart_symm,roundChart_zero]
  have hz : (0 : Euclidean n) ∈ (chartAt (Euclidean n) p).target := by
    change 0 ∈ (stereographic' n (-p)).target
    simp
  exact (congrArg (chartAt (Euclidean n) p) hh).symm.trans ((chartAt (Euclidean n) p).right_inv hz)

lemma unitSphere_chart_target (p : Metric.sphere (0 : A) 1) : (chartAt (Euclidean n) p).target = univ := by
  change (stereographic' n (-p)).target = _
  simp

lemma unitSphere_coordinate_embedding (p : Metric.sphere (0 : A) 1) (y : Euclidean n) (v : Euclidean n) :
    mfderiv 𝓘(ℝ,Euclidean n) 𝓘(ℝ,A)
      (fun q : Metric.sphere (0 : A) 1 => (q : A)) ((chartAt (Euclidean n) p).symm y)
      (mfderiv 𝓘(ℝ,Euclidean n) 𝓘(ℝ,Euclidean n) (chartAt (Euclidean n) p).symm y v) =
        fderiv ℝ (roundChart (p : A) (unitSphereFrame p)) y v := by
  have hy : y ∈ (chartAt (Euclidean n) p).target := by rw [unitSphere_chart_target]; trivial
  have hh := mfderiv_comp y
    ((contMDiff_coe_sphere (m := ∞)).mdifferentiable (by simp)).mdifferentiableAt
    ((contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (n := ∞) p) hy).mdifferentiableAt (by simp))
  have he := congrArg (fun L => L v) hh
  rw [mfderiv_eq_fderiv] at he
  rw [← unitSphere_chart_symm]
  exact he.symm

end


open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace
variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [FiniteDimensional ℝ A] {n : ℕ} [Fact (Module.finrank ℝ A = n+1)]
omit [FiniteDimensional ℝ A]
def unitSphereProjection (p : Metric.sphere (0 : A) 1) (a : A) : A :=
  a - inner ℝ (p : A) a • (p : A)

lemma unitSphereProjection_orthogonal (p : Metric.sphere (0 : A) 1) (a : A) :
    unitSphereProjection p a ∈ (ℝ ∙ (-(p : A)))ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
  simp [unitSphereProjection,inner_sub_left,inner_smul_left,real_inner_comm a (p : A)]

def unitSphereCoordinates (p : Metric.sphere (0 : A) 1) (a : A) : Euclidean n :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere (-p))).repr
    ⟨unitSphereProjection p a,unitSphereProjection_orthogonal p a⟩

lemma unitSphereFrame_coordinates (p : Metric.sphere (0 : A) 1) (a : A) :
    unitSphereFrame (n:=n) p (unitSphereCoordinates (n:=n) p a) = unitSphereProjection p a := by
  change (((OrthonormalBasis.fromOrthogonalSpanSingleton n
    (ne_zero_of_mem_unit_sphere (-p))).repr.symm
      ((OrthonormalBasis.fromOrthogonalSpanSingleton n
        (ne_zero_of_mem_unit_sphere (-p))).repr ⟨unitSphereProjection p a,_⟩)) : A) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

lemma unitSphereCoordinates_inner (p : Metric.sphere (0 : A) 1) (a b : A) :
    inner ℝ (unitSphereCoordinates (n:=n) p a) (unitSphereCoordinates (n:=n) p b) =
      inner ℝ a b - inner ℝ (p : A) a * inner ℝ (p : A) b := by
  rw [← (unitSphereFrame (n:=n) p).inner_map_map,unitSphereFrame_coordinates,unitSphereFrame_coordinates]
  simp [unitSphereProjection,inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
    real_inner_comm a (p : A)]

lemma unitSphereFrame_inner (p : Metric.sphere (0 : A) 1) (a : A) (w : Euclidean n) :
    inner ℝ (unitSphereFrame (n:=n) p w) a = inner ℝ w (unitSphereCoordinates (n:=n) p a) := by
  rw [← (unitSphereFrame (n:=n) p).inner_map_map,unitSphereFrame_coordinates]
  have hh := unitSphereFrame_orthogonal p w
  rw [real_inner_comm] at hh
  simp [unitSphereProjection,inner_sub_right,inner_smul_right,hh]

lemma unitSphere_inverse_gram_contraction (p : Metric.sphere (0 : A) 1) (a b : A) :
    ∑ i, ∑ j, (Matrix.gram ℝ (Module.finBasis ℝ (Euclidean n)))⁻¹ i j *
      inner ℝ (unitSphereFrame (n:=n) p (Module.finBasis ℝ (Euclidean n) j)) a *
      inner ℝ (unitSphereFrame (n:=n) p (Module.finBasis ℝ (Euclidean n) i)) b =
      inner ℝ a b - inner ℝ (p : A) a * inner ℝ (p : A) b := by
  simp_rw [unitSphereFrame_inner]
  rw [inverse_gram_contraction,unitSphereCoordinates_inner]


end YauCounterexamples
end

end OAI
