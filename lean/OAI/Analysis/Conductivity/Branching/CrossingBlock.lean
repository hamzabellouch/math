import Mathlib
import OAI.Analysis.Conductivity.Variational.CrossingHxx
import OAI.Analysis.Conductivity.Variational.CrossingEstimates
import OAI.Analysis.Conductivity.Branching.CascadeProfile

namespace OAI

noncomputable section

namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

def crossingValue (L z x y : ℝ) : ℝ :=
  crossingFirst L z*cos x + crossingSecond L z*cos (2*y)

def crossingXX (L z x y : ℝ) : ℝ :=
  9 + crossingHxx (exp (-3*z)) (crossingSecond L z) (crossingResidualSecond L z) 1 2 x y

def crossingYY (L z x y : ℝ) : ℝ :=
  1/4 + crossingHxx (exp (-z)) (crossingFirst L z) (crossingResidualFirst L z) 2 1 y x

def crossingXY (L z x y : ℝ) : ℝ :=
  crossingHxy (exp (-3*z)) (crossingResidualSecond L z) 1 2 x y +
  crossingHxy (exp (-z)) (crossingResidualFirst L z) 2 1 y x

def crossingCurrentX (L z x y : ℝ) : ℝ :=
  -9*crossingFirst L z*sin x - crossingResidualSecond L z*cos x*sin x*cos (2*y) -
    2*crossingResidualFirst L z*(sin (2*y))^2*sin x

def crossingCurrentY (L z x y : ℝ) : ℝ :=
  -(crossingSecond L z/2)*sin (2*y) - crossingResidualSecond L z*(sin x)^2*sin (2*y) -
    (crossingResidualFirst L z/2)*cos (2*y)*sin (2*y)*cos x

def crossingCurrentZ (L z x y : ℝ) : ℝ :=
  deriv (crossingFirst L) z*cos x + deriv (crossingSecond L) z*cos (2*y)

lemma crossing_first_on_left {L z : ℝ} (hL : 0 < L) (hz : z ≤ 0) :
    crossingFirst L z = exp (-3*z) := by
  rw [crossingFirst,crossingOff_eq_one hL (by linarith),one_mul]
lemma crossing_second_on_right {L z : ℝ} (hL : 0 < L) (hz : 0 ≤ z) :
    crossingSecond L z = exp (-z) := by
  rw [crossingSecond,crossingOn_eq_one hL (by linarith),one_mul]

lemma crossing_corrections_left {L z : ℝ} (hL : 0 < L) (hz : z ≤ 0) (x y : ℝ) :
    crossingYY L z x y = 1/4 ∧
    crossingXY L z x y = crossingHxy (exp (-3*z)) (crossingResidualSecond L z) 1 2 x y := by
  have hr := crossingResidualFirst_zero hL (show z < L/2 by linarith)
  simp [crossingYY,crossingXY,hr,crossingHxx,crossingHxy]
lemma crossing_corrections_right {L z : ℝ} (hL : 0 < L) (hz : 0 ≤ z) (x y : ℝ) :
    crossingXX L z x y = 9 ∧
    crossingXY L z x y = crossingHxy (exp (-z)) (crossingResidualFirst L z) 2 1 y x := by
  have hr := crossingResidualSecond_zero hL (show -L/2 < z by linarith)
  simp [crossingXX,crossingXY,hr,crossingHxx,crossingHxy]

lemma crossing_current_constitution {L : ℝ} (hL : 0 < L) (z x y : ℝ) :
    crossingCurrentX L z x y =
      crossingXX L z x y*(-crossingFirst L z*sin x) +
      crossingXY L z x y*(-2*crossingSecond L z*sin (2*y)) ∧
    crossingCurrentY L z x y =
      crossingXY L z x y*(-crossingFirst L z*sin x) +
      crossingYY L z x y*(-2*crossingSecond L z*sin (2*y)) := by
  have he₁ : exp (-3*z) ≠ 0 := (exp_pos _).ne'
  have he₂ : exp (-z) ≠ 0 := (exp_pos _).ne'
  by_cases hz : z ≤ 0
  · have hf := crossing_first_on_left hL hz
    have hr := crossingResidualFirst_zero hL (show z < L/2 by linarith)
    obtain ⟨hyy,hxy⟩ := crossing_corrections_left hL hz x y
    rw [hyy,hxy]
    constructor <;> dsimp only [crossingCurrentX,crossingCurrentY,crossingXX] <;>
      rw [hr,hf] <;> simp only [crossingHxx,crossingHxy,one_mul,one_pow,mul_one] <;>
      field_simp <;> ring
  · have hg := crossing_second_on_right hL (le_of_not_ge hz)
    have hr := crossingResidualSecond_zero hL (show -L/2 < z by linarith)
    obtain ⟨hxx,hxy⟩ := crossing_corrections_right hL (le_of_not_ge hz) x y
    rw [hxx,hxy]
    constructor <;> dsimp only [crossingCurrentX,crossingCurrentY,crossingYY] <;>
      rw [hr,hg] <;> simp only [crossingHxx,crossingHxy,one_mul,mul_one] <;>
      field_simp <;> ring

lemma crossing_value_hasDerivAt_x (L z x y : ℝ) :
    HasDerivAt (fun x => crossingValue L z x y) (-crossingFirst L z*sin x) x := by
  exact (((hasDerivAt_cos x).const_mul (crossingFirst L z)).add_const
    (crossingSecond L z*cos (2*y))).congr_deriv (g' := -crossingFirst L z*sin x) (by ring)
lemma crossing_value_hasDerivAt_y (L z x y : ℝ) :
    HasDerivAt (fun y => crossingValue L z x y) (-2*crossingSecond L z*sin (2*y)) y := by
  exact (((((hasDerivAt_id y).const_mul 2).cos).const_mul (crossingSecond L z)).const_add
    (crossingFirst L z*cos x)).congr_deriv (g' := -2*crossingSecond L z*sin (2*y))
    (by simp only [id_eq,mul_one]; ring)
lemma crossing_value_hasDerivAt_z (L z x y : ℝ) :
    HasDerivAt (fun z => crossingValue L z x y) (crossingCurrentZ L z x y) z := by
  exact (((crossingFirst_smooth L).differentiable (by simp) z).hasDerivAt.mul_const (cos x)).add
    (((crossingSecond_smooth L).differentiable (by simp) z).hasDerivAt.mul_const (cos (2*y)))

lemma crossing_current_divergence (L z x y : ℝ) :
    deriv (fun z => crossingCurrentZ L z x y) z +
    deriv (fun x => crossingCurrentX L z x y) x +
    deriv (fun y => crossingCurrentY L z x y) y = 0 := by
  have hsx := hasDerivAt_sin x
  have hcx := hasDerivAt_cos x
  have hy := (hasDerivAt_id y).const_mul 2
  have hsy := hy.sin
  have hcy := hy.cos
  have hx := ((hsx.const_mul (-9*crossingFirst L z)).sub
    (((hcx.mul hsx).const_mul (crossingResidualSecond L z)).mul_const (cos (2*y)))).sub
    (hsx.const_mul (2*crossingResidualFirst L z*(sin (2*y))^2))
  have hy' := ((hsy.const_mul (-(crossingSecond L z/2))).sub
    (hsy.const_mul (crossingResidualSecond L z*(sin x)^2))).sub
    (((hcy.mul hsy).const_mul (crossingResidualFirst L z/2)).mul_const (cos x))
  have hz := (((smooth_deriv_infty (crossingFirst_smooth L)).differentiable (by simp) z).hasDerivAt.mul_const
    (cos x)).add (((smooth_deriv_infty (crossingSecond_smooth L)).differentiable (by simp) z).hasDerivAt.mul_const
    (cos (2*y)))
  simp only [Pi.mul_def,Pi.sub_def,Pi.add_def,id_eq,mul_one] at hx hy' hz
  have hex : (fun x => crossingCurrentX L z x y) =
      (fun x => -9*crossingFirst L z*sin x - crossingResidualSecond L z*(cos x*sin x)*cos (2*y) -
        (2*crossingResidualFirst L z*(sin (2*y))^2)*sin x) := by
    funext x; unfold crossingCurrentX; ring
  have hey : (fun y => crossingCurrentY L z x y) =
      (fun y => -(crossingSecond L z/2)*sin (2*y) - crossingResidualSecond L z*(sin x)^2*sin (2*y) -
        (crossingResidualFirst L z/2)*(cos (2*y)*sin (2*y))*cos x) := by
    funext y; unfold crossingCurrentY; ring
  rw [hex,hey,hx.deriv,hy'.deriv]
  simp only [crossingCurrentZ]
  rw [hz.deriv]
  have hr₁ : deriv (deriv (crossingFirst L)) z = crossingResidualFirst L z+9*crossingFirst L z := by
    unfold crossingResidualFirst; ring
  have hr₂ : deriv (deriv (crossingSecond L)) z = crossingResidualSecond L z+crossingSecond L z := by
    unfold crossingResidualSecond; ring
  rw [hr₁,hr₂]
  linear_combination
    -(crossingResidualSecond L z*cos (2*y)) * Real.sin_sq_add_cos_sq x +
    -(crossingResidualFirst L z*cos x) * Real.sin_sq_add_cos_sq (2*y)

lemma cascadeProfile_next_connector_zero {L K s : ℝ} (hL : 0 < L)
    (hs : s ≤ K+2) : cascadeProfile L K (2*(s-cascadeLength L K)) = 0 := by
  apply cascadeProfile_zero_left hL
  unfold cascadeLength
  linarith

lemma cascadeProfile_crossing_current {L K s : ℝ} (hL : 0 < L) (hK : 0 < K)
    (hs : K+2 ≤ s) :
    cascadeProfile L K s = connectorProfile K (K+2)*exp (-3*L)*
      crossingFirst L (s-(K+2+L)) := by
  rw [cascadeProfile_outgoing hL hK hs,crossingFirst]
  have he : exp (-3*(s-(K+2))) = exp (-3*L)*exp (-3*(s-(K+2+L))) := by
    rw [←exp_add]
    congr 1
    ring
  rw [he]
  ring

lemma cascadeProfile_crossing_next {L K s : ℝ} (hL : 0 < L) (hK : 0 < K)
    (hs : s ≤ cascadeLength L K) :
    cascadeRatio L K*cascadeProfile L K (2*(s-cascadeLength L K)) =
      connectorProfile K (K+2)*exp (-3*L)*crossingSecond L (s-(K+2+L)) := by
  rw [cascadeProfile_incoming hL hK (by linarith),cascadeRatio,crossingSecond]
  have ha : 2*(s-cascadeLength L K)/2+L = s-(K+2+L) := by
    unfold cascadeLength
    ring
  rw [ha]
  have he : exp (-4*L)*exp (-(2*(s-cascadeLength L K))/2) =
      exp (-3*L)*exp (-(s-(K+2+L))) := by
    rw [←exp_add,←exp_add]
    congr 1
    unfold cascadeLength
    ring
  calc
    _ = connectorProfile K (K+2)*crossingOn L (s-(K+2+L))*
        (exp (-4*L)*exp (-(2*(s-cascadeLength L K))/2)) := by ring
    _ = _ := by rw [he]; ring

lemma cascade_overlap_value {L K s : ℝ} (hL : 0 < L) (hK : 0 < K)
    (hs₁ : K+2 ≤ s) (hs₂ : s ≤ cascadeLength L K) (a x y : ℝ) :
    a*cascadeProfile L K s*cos x +
      (a*cascadeRatio L K)*cascadeProfile L K (2*(s-cascadeLength L K))*cos (2*y) =
    (a*connectorProfile K (K+2)*exp (-3*L))*crossingValue L (s-(K+2+L)) x y := by
  rw [cascadeProfile_crossing_current hL hK hs₁]
  have hh := cascadeProfile_crossing_next hL hK hs₂
  dsimp only [crossingValue]
  calc
    _ = a*(connectorProfile K (K+2)*exp (-3*L)*crossingFirst L (s-(K+2+L)))*cos x +
      a*(cascadeRatio L K*cascadeProfile L K (2*(s-cascadeLength L K)))*cos (2*y) := by ring
    _ = _ := by rw [hh]; ring

end ScalarConductivity

end

end OAI
