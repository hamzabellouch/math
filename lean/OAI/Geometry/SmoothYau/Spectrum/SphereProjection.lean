import Mathlib
import OAI.Geometry.SmoothYau.Estimates.LpInverseGramFstContraction
import OAI.Geometry.SmoothYau.Model
import OAI.Geometry.SmoothYau.Smoothness.LinearPowerDirectional

namespace OAI

noncomputable section
namespace YauCounterexamples
section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace

variable {n : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (n+1)) = n+1) := ⟨by simp [Euclidean]⟩

def sphereFrame (p : Sphere n) : Euclidean n →ₗᵢ[ℝ] Euclidean (n+1) :=
  (ℝ ∙ (-(p : Euclidean (n+1))))ᗮ.subtypeₗᵢ.comp
    (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere (-p))).repr.symm.toLinearIsometry

lemma sphereFrame_orthogonal (p : Sphere n) (w : Euclidean n) :
    inner ℝ (p : Euclidean (n+1)) (sphereFrame p w) = 0 := by
  have hh := ((OrthonormalBasis.fromOrthogonalSpanSingleton n
    (ne_zero_of_mem_unit_sphere (-p))).repr.symm w).property
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at hh
  change inner ℝ (p : Euclidean (n+1)) _ = 0
  rw [real_inner_comm]
  change inner ℝ _ (-(p : Euclidean (n+1))) = 0 at hh
  rw [inner_neg_right,neg_eq_zero] at hh
  exact hh

lemma sphere_chart_symm (p : Sphere n) :
    (fun y => ((chartAt (Euclidean n) p).symm y : Euclidean (n+1))) =
      roundChart (p : Euclidean (n+1)) (sphereFrame p) := by
  funext y
  change ((stereographic' n (-p)).symm y : Euclidean (n+1)) = _
  rw [stereographic'_symm_apply]
  simp only [roundChart,sphereFrame,stereoInvFunAux,smul_add,smul_smul]
  rfl

lemma sphere_chart_center (p : Sphere n) : chartAt (Euclidean n) p p = 0 := by
  have hh : (chartAt (Euclidean n) p).symm 0 = p := by
    apply Subtype.ext
    change (fun y => ((chartAt (Euclidean n) p).symm y : Euclidean (n+1))) 0 = _
    rw [sphere_chart_symm,roundChart_zero]
  have hz : (0 : Euclidean n) ∈ (chartAt (Euclidean n) p).target := by
    change 0 ∈ (stereographic' n (-p)).target
    simp
  exact (congrArg (chartAt (Euclidean n) p) hh).symm.trans ((chartAt (Euclidean n) p).right_inv hz)

lemma sphere_chart_target (p : Sphere n) : (chartAt (Euclidean n) p).target = univ := by
  change (stereographic' n (-p)).target = _
  simp

lemma sphere_coordinate_embedding (p : Sphere n) (y : Euclidean n) (v : Euclidean n) :
    mfderiv 𝓘(ℝ,Euclidean n) 𝓘(ℝ,Euclidean (n+1))
      (fun q : Sphere n => (q : Euclidean (n+1))) ((chartAt (Euclidean n) p).symm y)
      (mfderiv 𝓘(ℝ,Euclidean n) 𝓘(ℝ,Euclidean n) (chartAt (Euclidean n) p).symm y v) =
        fderiv ℝ (roundChart (p : Euclidean (n+1)) (sphereFrame p)) y v := by
  have hy : y ∈ (chartAt (Euclidean n) p).target := by rw [sphere_chart_target]; trivial
  have hh := mfderiv_comp y
    ((contMDiff_coe_sphere (m := ∞)).mdifferentiable (by simp)).mdifferentiableAt
    ((contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (n := ∞) p) hy).mdifferentiableAt (by simp))
  have he := congrArg (fun L => L v) hh
  rw [mfderiv_eq_fderiv] at he
  rw [← sphere_chart_symm]
  exact he.symm


end

section
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold BoxIntegral Metric
open scoped Topology ContDiff InnerProductSpace

def sphericalRadius (a b : Euclidean 4) (q : Sphere 3) : ℝ :=
  Real.sqrt ((inner ℝ a (q : Euclidean 4))^2+(inner ℝ b (q : Euclidean 4))^2)

lemma sphericalRadius_nonneg (a b : Euclidean 4) (q : Sphere 3) :
    0 ≤ sphericalRadius a b q := Real.sqrt_nonneg _

lemma sphericalRadius_sq (a b : Euclidean 4) (q : Sphere 3) :
    (sphericalRadius a b q)^2 =
      (inner ℝ a (q : Euclidean 4))^2+(inner ℝ b (q : Euclidean 4))^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

lemma sphericalRadius_continuous (a b : Euclidean 4) : Continuous (sphericalRadius a b) :=
  (((continuous_const.inner continuous_subtype_val).pow 2).add
    ((continuous_const.inner continuous_subtype_val).pow 2)).sqrt

lemma orthogonal_pair_sq_le (a b q : Euclidean 4)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0) :
    (inner ℝ a q)^2+(inner ℝ b q)^2 ≤ inner ℝ q q := by
  have hba : inner ℝ b a = 0 := (real_inner_comm a b).trans hab
  have hqa : inner ℝ q a = inner ℝ a q := real_inner_comm a q
  have hqb : inner ℝ q b = inner ℝ b q := real_inner_comm b q
  have h := real_inner_self_nonneg (x := q-(inner ℝ a q) • a-(inner ℝ b q) • b)
  simp only [inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
    ha,hb,hab,hba,hqa,hqb] at h
  nlinarith

lemma sphericalRadius_le_one (a b : Euclidean 4)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (q : Sphere 3) : sphericalRadius a b q ≤ 1 := by
  have h := orthogonal_pair_sq_le a b q ha hb hab
  have hq : ‖(q : Euclidean 4)‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using q.property
  rw [real_inner_self_eq_norm_sq,hq,one_pow,← sphericalRadius_sq] at h
  nlinarith [sphericalRadius_nonneg a b q]

lemma sphere_chart_source (p : Sphere 3) : (chartAt (Euclidean 3) p).source = {-p}ᶜ := by
  let : Fact (Module.finrank ℝ (Euclidean 4) = 3+1) := ⟨by simp [Euclidean]⟩
  change (stereographic' 3 (-p)).source = _
  simp

abbrev sourceAxisOne : Euclidean 4 := EuclideanSpace.single 0 1
abbrev sourceAxisTwo : Euclidean 4 := EuclideanSpace.single 1 1

lemma source_axes_orthonormal : inner ℝ sourceAxisOne sourceAxisOne = 1 ∧
    inner ℝ sourceAxisTwo sourceAxisTwo = 1 ∧ inner ℝ sourceAxisOne sourceAxisTwo = 0 := by
  norm_num [sourceAxisOne,sourceAxisTwo,EuclideanSpace.inner_single_left,PiLp.single_apply]

def sourcePole : Sphere 3 := ⟨sourceAxisOne,by simp [sourceAxisOne]⟩

lemma sphericalRadius_neg_sourcePole : sphericalRadius sourceAxisOne sourceAxisTwo (-sourcePole) = 1 := by
  norm_num [sphericalRadius,sourcePole,sourceAxisOne,sourceAxisTwo,
    EuclideanSpace.inner_single_left,PiLp.single_apply]

def sourceSignPoint : Sphere 3 :=
  ⟨EuclideanSpace.single 0 (40/401)+EuclideanSpace.single (2 : Fin 4) (399/401),by
    rw [Metric.mem_sphere,dist_zero_right]
    have hi : inner ℝ
        (EuclideanSpace.single (0 : Fin 4) (40/401 : ℝ)+EuclideanSpace.single (2 : Fin 4) (399/401))
        (EuclideanSpace.single (0 : Fin 4) (40/401 : ℝ)+EuclideanSpace.single (2 : Fin 4) (399/401)) = 1 := by
      simp only [inner_add_left,inner_add_right,EuclideanSpace.inner_single_left,PiLp.single_apply]
      norm_num [Fin.ext_iff]
    rw [real_inner_self_eq_norm_sq] at hi
    nlinarith [norm_nonneg (EuclideanSpace.single (0 : Fin 4) (40/401 : ℝ)+EuclideanSpace.single (2 : Fin 4) (399/401))]⟩

lemma sphericalRadius_sourceSignPoint :
    sphericalRadius sourceAxisOne sourceAxisTwo sourceSignPoint = 40/401 := by
  unfold sphericalRadius
  have he : (inner ℝ sourceAxisOne (sourceSignPoint : Euclidean 4))^2+
      (inner ℝ sourceAxisTwo (sourceSignPoint : Euclidean 4))^2 = (40/401 : ℝ)^2 := by
    simp only [sourceAxisOne,sourceAxisTwo,sourceSignPoint,inner_add_right,
      EuclideanSpace.inner_single_left,PiLp.single_apply]
    norm_num [Fin.ext_iff]
  rw [he,Real.sqrt_sq_eq_abs]
  norm_num

lemma sphericalRadius_sublevel_in_source (p : Sphere 3) (a b : Euclidean 4)
    (hp : sphericalRadius a b (-p) = 1) {R : ℝ} (hR : R < 1) :
    {q | sphericalRadius a b q ≤ R} ⊆ (chartAt (Euclidean 3) p).source := by
  intro q hq
  rw [sphere_chart_source]
  intro hneg
  have he : q = -p := hneg
  change sphericalRadius a b q ≤ R at hq
  rw [he,hp] at hq
  exact (not_le_of_gt hR) hq

def sphericalCoverage (p : Sphere 3) (a b : Euclidean 4) (R : ℝ) : Set (Euclidean 3) :=
  chartAt (Euclidean 3) p '' {q | sphericalRadius a b q ≤ R}

lemma sphericalCoverage_compact (p : Sphere 3) (a b : Euclidean 4)
    (hp : sphericalRadius a b (-p) = 1) {R : ℝ} (hR : R < 1) :
    IsCompact (sphericalCoverage p a b R) := by
  have hc : IsCompact {q : Sphere 3 | sphericalRadius a b q ≤ R} :=
    (isClosed_le (sphericalRadius_continuous a b) continuous_const).isCompact
  exact hc.image_of_continuousOn ((chartAt (Euclidean 3) p).continuousOn.mono
    (sphericalRadius_sublevel_in_source p a b hp hR))

lemma mem_sphericalCoverage_iff (p : Sphere 3) (a b : Euclidean 4)
    (hp : sphericalRadius a b (-p) = 1) {R : ℝ} (hR : R < 1) (y : Euclidean 3) :
    y ∈ sphericalCoverage p a b R ↔
      sphericalRadius a b ((chartAt (Euclidean 3) p).symm y) ≤ R := by
  constructor
  · rintro ⟨q,hq,rfl⟩
    rw [(chartAt (Euclidean 3) p).left_inv (sphericalRadius_sublevel_in_source p a b hp hR hq)]
    exact hq
  · intro hy
    exact ⟨(chartAt (Euclidean 3) p).symm y,hy,
      (chartAt (Euclidean 3) p).right_inv (by rw [sphere_chart_target]; trivial)⟩

lemma sphericalCoverage_mono (p : Sphere 3) (a b : Euclidean 4) {R S : ℝ} (h : R ≤ S) :
    sphericalCoverage p a b R ⊆ sphericalCoverage p a b S :=
  image_mono (fun _ hx => hx.trans h)

lemma sphere_chart_symm_continuous (p : Sphere 3) : Continuous (chartAt (Euclidean 3) p).symm := by
  exact continuousOn_univ.mp (by simpa only [sphere_chart_target] using
    (chartAt (Euclidean 3) p).continuousOn_symm)

lemma sphericalCoverage_subset_open (p : Sphere 3) (a b : Euclidean 4)
    (hp : sphericalRadius a b (-p) = 1) {R S : ℝ} (hR : R < 1) (hRS : R < S) :
    sphericalCoverage p a b R ⊆
      {y | sphericalRadius a b ((chartAt (Euclidean 3) p).symm y) < S} := by
  intro y hy
  exact ((mem_sphericalCoverage_iff p a b hp hR y).mp hy).trans_lt hRS

lemma sphericalCoverage_open (p : Sphere 3) (a b : Euclidean 4) (S : ℝ) :
    IsOpen {y | sphericalRadius a b ((chartAt (Euclidean 3) p).symm y) < S} :=
  isOpen_lt ((sphericalRadius_continuous a b).comp (sphere_chart_symm_continuous p)) continuous_const


end

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Manifold
open scoped Topology ContDiff
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology InnerProductSpace
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Module Manifold
open scoped Topology ContDiff InnerProductSpace Matrix
variable {n : ℕ}
local instance : Fact (Module.finrank ℝ (Euclidean (n+1)) = n+1) := ⟨by simp [Euclidean]⟩

def sphereProjection (p : Sphere n) (a : Euclidean (n+1)) : Euclidean (n+1) :=
  a - inner ℝ (p : Euclidean (n+1)) a • (p : Euclidean (n+1))

lemma sphereProjection_orthogonal (p : Sphere n) (a : Euclidean (n+1)) :
    sphereProjection p a ∈ (ℝ ∙ (-(p : Euclidean (n+1))))ᗮ := by
  rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
  simp [sphereProjection,inner_sub_left,inner_smul_left,real_inner_comm a (p : Euclidean (n+1))]

def sphereCoordinates (p : Sphere n) (a : Euclidean (n+1)) : Euclidean n :=
  (OrthonormalBasis.fromOrthogonalSpanSingleton n (ne_zero_of_mem_unit_sphere (-p))).repr
    ⟨sphereProjection p a,sphereProjection_orthogonal p a⟩

lemma sphereFrame_coordinates (p : Sphere n) (a : Euclidean (n+1)) :
    sphereFrame p (sphereCoordinates p a) = sphereProjection p a := by
  change (((OrthonormalBasis.fromOrthogonalSpanSingleton n
    (ne_zero_of_mem_unit_sphere (-p))).repr.symm
      ((OrthonormalBasis.fromOrthogonalSpanSingleton n
        (ne_zero_of_mem_unit_sphere (-p))).repr ⟨sphereProjection p a,_⟩)) : Euclidean (n+1)) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

lemma sphereCoordinates_inner (p : Sphere n) (a b : Euclidean (n+1)) :
    inner ℝ (sphereCoordinates p a) (sphereCoordinates p b) =
      inner ℝ a b - inner ℝ (p : Euclidean (n+1)) a * inner ℝ (p : Euclidean (n+1)) b := by
  rw [← (sphereFrame p).inner_map_map,sphereFrame_coordinates,sphereFrame_coordinates]
  simp [sphereProjection,inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
    real_inner_comm a (p : Euclidean (n+1))]

lemma sphereFrame_inner (p : Sphere n) (a : Euclidean (n+1)) (w : Euclidean n) :
    inner ℝ (sphereFrame p w) a = inner ℝ w (sphereCoordinates p a) := by
  rw [← (sphereFrame p).inner_map_map,sphereFrame_coordinates]
  have hh := sphereFrame_orthogonal p w
  rw [real_inner_comm] at hh
  simp [sphereProjection,inner_sub_right,inner_smul_right,hh]

lemma sphere_inverse_gram_contraction (p : Sphere n) (a b : Euclidean (n+1)) :
    ∑ i, ∑ j, (Matrix.gram ℝ (Module.finBasis ℝ (Euclidean n)))⁻¹ i j *
      inner ℝ (sphereFrame p (Module.finBasis ℝ (Euclidean n) j)) a *
      inner ℝ (sphereFrame p (Module.finBasis ℝ (Euclidean n) i)) b =
      inner ℝ a b - inner ℝ (p : Euclidean (n+1)) a * inner ℝ (p : Euclidean (n+1)) b := by
  simp_rw [sphereFrame_inner]
  rw [inverse_gram_contraction,sphereCoordinates_inner]

section Planar
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def planarLinear (a b : E) : E →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (innerSL ℝ a) + Complex.I • (Complex.ofRealCLM.comp (innerSL ℝ b))

lemma planarLinear_apply (a b x : E) :
    planarLinear a b x = (inner ℝ a x : ℂ) + Complex.I * (inner ℝ b x : ℂ) := by
  rfl
lemma planarLinear_apply_flip (a b x : E) :
    planarLinear a b x = (inner ℝ x a : ℂ) + Complex.I * (inner ℝ x b : ℂ) := by
  rw [planarLinear_apply,real_inner_comm a x,real_inner_comm b x]
end Planar

lemma complex_bilinear_expand (r a b c d : ℝ) :
    (r:ℂ) * ((a:ℂ)+Complex.I*b) * ((c:ℂ)+Complex.I*d) =
      ((r*a*c-r*b*d:ℝ):ℂ) + Complex.I * ((r*a*d+r*b*c:ℝ):ℂ) := by
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]


theorem sphere_planar_contraction (p : Sphere n) (a b : Euclidean (n+1))
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0) :
    ∑ i, ∑ j, ((Matrix.gram ℝ (Module.finBasis ℝ (Euclidean n)))⁻¹ i j : ℂ) *
      planarLinear a b (sphereFrame p (Module.finBasis ℝ (Euclidean n) j)) *
      planarLinear a b (sphereFrame p (Module.finBasis ℝ (Euclidean n) i)) =
        -(planarLinear a b (p : Euclidean (n+1)))^2 := by
  simp_rw [planarLinear_apply_flip,complex_bilinear_expand]
  simp_rw [Finset.sum_add_distrib,← Finset.mul_sum,← Complex.ofReal_sum,
    Finset.sum_sub_distrib]
  simp only [Finset.sum_add_distrib]
  rw [sphere_inverse_gram_contraction,sphere_inverse_gram_contraction,
    sphere_inverse_gram_contraction,sphere_inverse_gram_contraction]
  rw [ha,hb,hab,real_inner_comm a b,hab]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im,pow_two]; ring



end YauCounterexamples
end

end OAI
