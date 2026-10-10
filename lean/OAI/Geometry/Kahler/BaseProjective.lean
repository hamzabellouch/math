import OAI.Geometry.Kahler.BaseRadialLaw

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open Set Filter Topology
open scoped ContDiff
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

def projectiveDistance (ξ p : Sphere) : ℝ := Real.sqrt (1-‖bracket (ξ:Base) (p:Base)‖^2)

def bloch (ξ : Sphere) : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![radialU ξ,radialR ξ,radialJ ξ]

lemma bloch_continuous : Continuous bloch := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact radialU_continuous
  · exact radialR_continuous
  · exact radialJ_continuous

lemma bracket_coordinates (z p : Base) : bracket z p = z 0*star (p 0)+z 1*star (p 1) := by
  simp [bracket,Fin.sum_univ_two,inner]

lemma bracket_radial_identity (ξ p : Sphere) :
    ‖bracket (ξ:Base) (p:Base)‖^2 = radialU ξ*radialU p+radialV ξ*radialV p+
      2*(radialR ξ*radialR p+radialJ ξ*radialJ p) := by
  rw [← Complex.normSq_eq_norm_sq,bracket_coordinates]
  simp only [radialU,radialV,radialR,radialJ,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

lemma bloch_dist_sq (ξ p : Sphere) :
    dist (bloch ξ) (bloch p)^2 = 1-‖bracket (ξ:Base) (p:Base)‖^2 := by
  rw [dist_eq_norm,EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_three,PiLp.sub_apply]
  change |radialU ξ-radialU p|^2+|radialR ξ-radialR p|^2+|radialJ ξ-radialJ p|^2 = _
  simp only [sq_abs]
  rw [bracket_radial_identity]
  have hvξ : radialV ξ = 1-radialU ξ := by linarith [radialUV ξ]
  have hvp : radialV p = 1-radialU p := by linarith [radialUV p]
  have hξ := radialRI ξ
  have hp := radialRI p
  rw [hvξ] at hξ ⊢
  rw [hvp] at hp ⊢
  nlinarith

lemma projectiveDistance_eq_dist (ξ p : Sphere) : projectiveDistance ξ p = dist (bloch ξ) (bloch p) := by
  rw [projectiveDistance,← bloch_dist_sq,Real.sqrt_sq (dist_nonneg)]

lemma projectiveDistance_triangle (ξ p q : Sphere) :
    projectiveDistance ξ q ≤ projectiveDistance ξ p+projectiveDistance p q := by
  simp only [projectiveDistance_eq_dist]
  exact dist_triangle _ _ _

lemma projectiveDistance_nonneg (ξ p : Sphere) : 0 ≤ projectiveDistance ξ p := Real.sqrt_nonneg _
lemma projectiveDistance_symm (ξ p : Sphere) : projectiveDistance ξ p = projectiveDistance p ξ := by
  simp only [projectiveDistance_eq_dist,dist_comm]
lemma projectiveDistance_self (ξ : Sphere) : projectiveDistance ξ ξ = 0 := by
  simp [projectiveDistance_eq_dist]

lemma projectiveDistance_continuous (p : Sphere) : Continuous (fun ξ => projectiveDistance ξ p) := by
  simpa only [projectiveDistance_eq_dist] using bloch_continuous.dist continuous_const

lemma bracket_norm_le_one (ξ p : Sphere) : ‖bracket (ξ:Base) (p:Base)‖ ≤ 1 := by
  simpa only [bracket,sphere_norm,one_mul] using norm_inner_le_norm (p:Base) (ξ:Base)

lemma projectiveDistance_sq (ξ p : Sphere) : projectiveDistance ξ p^2 = 1-‖bracket (ξ:Base) (p:Base)‖^2 := by
  rw [projectiveDistance_eq_dist,bloch_dist_sq]

lemma projectiveDistance_le_one (ξ p : Sphere) : projectiveDistance ξ p ≤ 1 := by
  have hs := projectiveDistance_sq ξ p
  have hn := projectiveDistance_nonneg ξ p
  nlinarith [sq_nonneg ‖bracket (ξ:Base) (p:Base)‖]

def adaptedIsometry (p : Sphere) : Base ≃ₗᵢ[ℂ] Base :=
  suIsometry (star ((p:Base) 0)) (star ((p:Base) 1)) (by
    simpa only [Complex.normSq_conj,Complex.star_def,radialU,radialV] using radialUV p)

lemma adaptedIsometry_zero (p : Sphere) (z : Base) : adaptedIsometry p z 0 = bracket z (p:Base) := by
  simp only [adaptedIsometry,suIsometry_zero,bracket_coordinates]
  ring

lemma adapted_radialU (ξ p : Sphere) : radialU (sphereAction (adaptedIsometry p) ξ) = ‖bracket (ξ:Base) (p:Base)‖^2 := by
  simp only [radialU,sphereAction_coe,adaptedIsometry_zero,Complex.normSq_eq_norm_sq]

lemma projective_cap_measure (p : Sphere) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    sigma {ξ | projectiveDistance ξ p < s} = ENNReal.ofReal (s^2) := by
  let a : unitInterval := ⟨1-s^2,by constructor <;> nlinarith⟩
  have he : {ξ | projectiveDistance ξ p < s} =
      (sphereAction (adaptedIsometry p)) ⁻¹' (radialUnit ⁻¹' Ioi a) := by
    ext ξ
    change projectiveDistance ξ p < s ↔ (a:ℝ) < radialU (sphereAction (adaptedIsometry p) ξ)
    rw [adapted_radialU]
    dsimp [a]
    have hp := projectiveDistance_sq ξ p
    have hnn := projectiveDistance_nonneg ξ p
    constructor <;> intro h <;> nlinarith
  rw [he,(sphereAction_preserves (adaptedIsometry p)).measure_preimage_emb (sphereAction _).measurableEmbedding,
    ← Measure.map_apply radialUnit_continuous.measurable measurableSet_Ioi,radial_law,unitInterval.volume_Ioi]
  congr 1
  dsimp [a]
  ring

end PinchedHartogs.BaseConstruction

end

end OAI
