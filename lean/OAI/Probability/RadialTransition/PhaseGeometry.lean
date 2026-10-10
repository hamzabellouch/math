import OAI.Probability.RadialTransition.TruncatedFamily

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma phaseSlope_zero : phaseSlope 0=parameter 0 0 := by simp [phaseSlope,phaseDensity]
lemma phaseSlope_one : phaseSlope 1=parameter (3*packingDensity/4) packingDensity := by
  simp only [phaseSlope, phaseDensity, Matrix.cons_val_one, Matrix.cons_val_zero]
  congr 1
  dsimp [phaseMass]
  field_simp
  ring
lemma phaseSlope_two : phaseSlope 2=parameter (12*packingDensity) (4*packingDensity) := by
  change parameter (phaseMass/2*(4*packingDensity)^2) (4*packingDensity)=_
  congr 1
  dsimp [phaseMass]
  field_simp
  ring

lemma phase_densities_separated (i j : Fin 3) (hij : i ≠ j) :
    packingDensity ≤ |phaseSlope i 1-phaseSlope j 1| := by
  have hp := packingDensity_pos
  fin_cases i <;> fin_cases j <;> simp_all [phaseSlope_zero,phaseSlope_one,phaseSlope_two,abs_of_pos,abs_of_neg] <;>
    linarith

def phaseRadius : ℝ := packingDensity/128
def pressureRadius : ℝ := packingDensity/32
lemma phaseRadius_pos : 0 < phaseRadius := div_pos packingDensity_pos (by norm_num)
lemma pressureRadius_pos : 0 < pressureRadius := div_pos packingDensity_pos (by norm_num)
lemma phaseRadius_lt : phaseRadius < packingDensity/16 := by dsimp [phaseRadius]; linarith [packingDensity_pos]

def directionalMax (z : Parameter) : ℝ := finiteMax (fun i : Fin 3 => inner ℝ (phaseSlope i-targetSlope) z)

lemma directional_lower (z : Parameter) : packingDensity/8*‖z‖ ≤ directionalMax z := by
  let m := directionalMax z
  let A := inner ℝ (phaseSlope 0-targetSlope) z
  let B := inner ℝ (phaseSlope 1-targetSlope) z
  let C := inner ℝ (phaseSlope 2-targetSlope) z
  have hA : A ≤ m := le_finiteMax (fun i : Fin 3 => inner ℝ (phaseSlope i-targetSlope) z) 0
  have hB : B ≤ m := le_finiteMax (fun i : Fin 3 => inner ℝ (phaseSlope i-targetSlope) z) 1
  have hC : C ≤ m := le_finiteMax (fun i : Fin 3 => inner ℝ (phaseSlope i-targetSlope) z) 2
  have hsum : A+B+C=0 := by
    dsimp [A,B,C]
    rw [phaseSlope_zero,phaseSlope_one,phaseSlope_two]
    simp only [parameter_inner, PiLp.sub_apply, parameter_zero,parameter_one,targetSlope]
    ring
  have hm : 0 ≤ m := by linarith
  have hAl : -2*m ≤ A := by linarith
  have hBl : -2*m ≤ B := by linarith
  have hCl : -2*m ≤ C := by linarith
  have hcoord₀ : |packingDensity*z 0| ≤ 2*m := by
    dsimp [A,B,C] at hA hB hC hAl hBl hCl
    rw [phaseSlope_zero] at hA hAl
    rw [phaseSlope_one] at hB hBl
    rw [phaseSlope_two] at hC hCl
    simp only [parameter_inner, PiLp.sub_apply, parameter_zero,parameter_one,targetSlope] at hA hB hC hAl hBl hCl
    rw [abs_le]
    constructor <;> nlinarith
  have hcoord₁ : |packingDensity*z 1| ≤ 5*m := by
    dsimp [A,B,C] at hA hB hC hAl hBl hCl
    rw [phaseSlope_zero] at hA hAl
    rw [phaseSlope_one] at hB hBl
    rw [phaseSlope_two] at hC hCl
    simp only [parameter_inner, PiLp.sub_apply, parameter_zero,parameter_one,targetSlope] at hA hB hC hAl hBl hCl
    rw [abs_le]
    constructor <;> nlinarith
  rw [abs_mul,abs_of_pos packingDensity_pos] at hcoord₀ hcoord₁
  have hn := mul_le_mul_of_nonneg_left (parameter_norm_le z) packingDensity_pos.le
  change packingDensity/8*‖z‖ ≤ m
  nlinarith

lemma mem_closedHull_of_inner_le {G : Set Parameter} {v : Parameter}
    (h : ∀ z : Parameter, ∃ w ∈ G, inner ℝ v z ≤ inner ℝ w z) :
    v ∈ closure (convexHull ℝ G) := by
  by_contra hv
  obtain ⟨ell,c,hsep,hvc⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ G).closure isClosed_closure hv
  let z : Parameter := (InnerProductSpace.toDual ℝ Parameter).symm ell
  have hell (w : Parameter) : inner ℝ w z=ell w := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  obtain ⟨w,hw,hh⟩ := h z
  have hs := hsep w (subset_closure (subset_convexHull ℝ G hw))
  rw [hell,hell] at hh
  linarith

lemma robust_phase_triangle (w : Fin 3 → Parameter)
    (hw : ∀ i, w i ∈ Metric.closedBall (phaseSlope i) phaseRadius) :
    Metric.closedBall targetSlope pressureRadius ⊆ closure (convexHull ℝ (range w)) := by
  intro v hv
  apply mem_closedHull_of_inner_le
  intro z
  obtain ⟨i,hi⟩ := finiteMax_attained (fun i : Fin 3 => inner ℝ (phaseSlope i-targetSlope) z)
  have hd := directional_lower z
  change directionalMax z=inner ℝ (phaseSlope i-targetSlope) z at hi
  rw [hi] at hd
  have hvn : ‖v-targetSlope‖ ≤ pressureRadius := Metric.mem_closedBall.mp hv
  have hwn : ‖phaseSlope i-w i‖ ≤ phaseRadius := by
    rw [norm_sub_rev]
    exact Metric.mem_closedBall.mp (hw i)
  have hvz := (real_inner_le_norm (v-targetSlope) z).trans (mul_le_mul_of_nonneg_right hvn (norm_nonneg z))
  have hwz := (real_inner_le_norm (phaseSlope i-w i) z).trans (mul_le_mul_of_nonneg_right hwn (norm_nonneg z))
  refine ⟨w i, mem_range_self i, ?_⟩
  rw [inner_sub_left] at hd hvz hwz
  dsimp [pressureRadius,phaseRadius] at hvz hwz
  nlinarith [mul_nonneg packingDensity_pos.le (norm_nonneg z)]

def exclusionNormal : Fin 3 → Parameter := ![parameter 1 (-15/4),parameter (-1) 3,parameter 1 (-3/4)]

lemma exclusionNormal_norm (i : Fin 3) : ‖exclusionNormal i‖ ≤ 5 := by
  have hn := parameter_norm_le (exclusionNormal i)
  fin_cases i <;> norm_num [exclusionNormal] at hn ⊢ <;> linarith

lemma exclusion_gap (i j : Fin 3) (hij : j ≠ i) :
    inner ℝ (phaseSlope j) (exclusionNormal i)+3*packingDensity/4 ≤ inner ℝ targetSlope (exclusionNormal i) := by
  have hp := packingDensity_pos
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals norm_num [phaseSlope,phaseDensity,phaseMass,exclusionNormal,parameter_inner,targetSlope]
  all_goals field_simp
  all_goals nlinarith

lemma exclusion_ball (i j : Fin 3) (hij : j ≠ i) {v : Parameter}
    (hv : v ∈ Metric.closedBall (phaseSlope j) phaseRadius) :
    inner ℝ v (exclusionNormal i) ≤ inner ℝ targetSlope (exclusionNormal i)-packingDensity/2 := by
  have hn : ‖v-phaseSlope j‖ ≤ phaseRadius := Metric.mem_closedBall.mp hv
  have hh := (real_inner_le_norm (v-phaseSlope j) (exclusionNormal i)).trans
    (mul_le_mul hn (exclusionNormal_norm i) (norm_nonneg _) phaseRadius_pos.le)
  rw [inner_sub_left] at hh
  have hg := exclusion_gap i j hij
  dsimp [phaseRadius] at hh
  linarith [packingDensity_pos]

lemma phase_plane_at_center (i : Fin 3) : limitingPlane i 1 (-3/4)=0 := by
  have hp := packingDensity_pos.ne'
  fin_cases i <;> dsimp [limitingPlane,phaseDensity,phaseOffset,phaseMass] <;> field_simp <;> ring

lemma phase_plane_difference (i : Fin 3) (x : Parameter) :
    limitingPlane i (x 0) (x 1)=inner ℝ (phaseSlope i) (x-phaseCenter) := by
  have hh := phase_plane_at_center i
  dsimp [limitingPlane] at hh ⊢
  simp only [phaseSlope,phaseCenter,parameter_inner,PiLp.sub_apply,parameter_zero,parameter_one]
  nlinarith

lemma threePlane_center : onParameters threePlane phaseCenter=0 := by
  change finiteMax (fun i => limitingPlane i 1 (-3/4))=0
  apply le_antisymm
  · apply finiteMax_le
    intro i
    rw [phase_plane_at_center]
  · have hh := le_finiteMax (fun i => limitingPlane i 1 (-3/4)) (0:Fin 3)
    rw [phase_plane_at_center] at hh
    exact hh

lemma threePlane_growth (x : Parameter) :
    pressureRadius*‖x-phaseCenter‖ ≤ onParameters threePlane x-onParameters threePlane phaseCenter-
      inner ℝ targetSlope (x-phaseCenter) := by
  rw [threePlane_center,sub_zero]
  obtain ⟨i,hi⟩ := finiteMax_attained (fun i : Fin 3 => inner ℝ (phaseSlope i-targetSlope) (x-phaseCenter))
  have hd := directional_lower (x-phaseCenter)
  change directionalMax (x-phaseCenter)=_ at hi
  rw [hi,inner_sub_left] at hd
  have hh := le_finiteMax (fun i => limitingPlane i (x 0) (x 1)) i
  rw [phase_plane_difference] at hh
  change inner ℝ (phaseSlope i) (x-phaseCenter) ≤ onParameters threePlane x at hh
  dsimp [pressureRadius]
  nlinarith [mul_nonneg packingDensity_pos.le (norm_nonneg (x-phaseCenter))]

end RadialTransition
end

end OAI
