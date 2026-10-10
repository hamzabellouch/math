import OAI.Geometry.Arnold.MidpointGeometry

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace ArnoldCounterexample.Construction
open ArnoldCounterexample.Quadric ArnoldCounterexample.Field
open scoped ContDiff Topology NNReal
open Set Filter

def constant : ℝ≥0 := vectorField_lipschitz.choose
lemma lipschitz : LipschitzWith constant vectorField := vectorField_lipschitz.choose_spec

def epsilon : ℝ := 1 / (100 * ((constant:ℝ)+1))
lemma epsilon_pos : 0 < epsilon := by unfold epsilon; positivity

def parameter (t : ℝ) : ℝ := epsilon * Real.sin (Real.pi * t / 2)
lemma parameter_smooth : ContDiff ℝ ∞ parameter := by unfold parameter; fun_prop
lemma parameter_zero : parameter 0 = 0 := by simp [parameter]
lemma parameter_one : parameter 1 = epsilon := by simp [parameter]
lemma parameter_small : ∀ t, ‖parameter t‖ * constant < 1/10 := by
  intro t
  have hc : 0 ≤ (constant:ℝ) := constant.coe_nonneg
  have hden : 0 < 100 * ((constant:ℝ)+1) := by positivity
  have he : epsilon * (constant:ℝ) < 1/100 := by
    unfold epsilon
    rw [one_div_mul_eq_div, div_lt_iff₀ hden]
    linarith
  have hb : ‖parameter t‖ ≤ epsilon := by
    rw [parameter, norm_mul, Real.norm_eq_abs, abs_of_pos epsilon_pos, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) epsilon_pos.le).trans_eq (mul_one _)
  exact lt_trans (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hb hc) he) (by norm_num)
lemma parameter_contract : ∀ t, ‖parameter t‖ * constant < 1 :=
  fun t ↦ lt_trans (parameter_small t) (by norm_num)

def center : ℝ × CV → CV := Midpoint.resolvent vectorField lipschitz parameter parameter_contract
def forwardMid : ℝ × CV → CV := Midpoint.step vectorField lipschitz parameter parameter_contract
def backwardMid : ℝ × CV → CV :=
  Midpoint.step vectorField lipschitz (fun t ↦ -parameter t) (Midpoint.neg_small parameter_contract)
def midHamiltonian : ℝ × CV → ℝ :=
  Midpoint.hamiltonian vectorField lipschitz parameter parameter_contract potential

lemma center_smooth : ContDiff ℝ ∞ center :=
  Midpoint.resolvent_smooth _ lipschitz vectorField_smooth _ _ parameter_smooth
lemma forwardMid_smooth : ContDiff ℝ ∞ forwardMid :=
  Midpoint.step_smooth _ lipschitz vectorField_smooth _ _ parameter_smooth
lemma backwardMid_smooth : ContDiff ℝ ∞ backwardMid :=
  Midpoint.step_smooth _ lipschitz vectorField_smooth _ _ parameter_smooth.neg
lemma midHamiltonian_smooth : ContDiff ℝ ∞ midHamiltonian :=
  Midpoint.hamiltonian_smooth _ lipschitz vectorField_smooth _ _ parameter_smooth _ potential_smooth

lemma forwardMid_preserves (t : ℝ) (z : UnitQuadric) : IsUnitQuadric (forwardMid (t,z)) :=
  midpoint_preserves lipschitz parameter parameter_contract t z
lemma backwardMid_preserves (t : ℝ) (z : UnitQuadric) : IsUnitQuadric (backwardMid (t,z)) :=
  midpoint_preserves lipschitz _ (Midpoint.neg_small parameter_contract) t z

lemma center_phase_general (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖*constant < 1)
    (p : ℝ × CV) (c : ℂ) (hc : Complex.normSq c = 1) :
    Midpoint.resolvent vectorField lipschitz τ hτ (p.1,c•p.2) =
      c • Midpoint.resolvent vectorField lipschitz τ hτ p := by
  exact Midpoint.resolvent_symmetry _ lipschitz τ hτ (c • (LinearMap.id : CV →ₗ[ℝ] CV))
    (fun z ↦ vectorField_phase c hc z) p

lemma center_phase (p : ℝ × CV) (c : ℂ) (hc : Complex.normSq c = 1) :
    center (p.1,c•p.2) = c • center p := center_phase_general _ _ p c hc

lemma forwardMid_phase (p : ℝ × CV) (c : ℂ) (hc : Complex.normSq c = 1) :
    forwardMid (p.1,c•p.2) = c • forwardMid p := by
  simp only [forwardMid, Midpoint.step, center_phase_general _ _ p c hc, smul_sub, smul_comm c]
lemma backwardMid_phase (p : ℝ × CV) (c : ℂ) (hc : Complex.normSq c = 1) :
    backwardMid (p.1,c•p.2) = c • backwardMid p := by
  simp only [backwardMid, Midpoint.step, center_phase_general _ _ p c hc, smul_sub, smul_comm c]
lemma midHamiltonian_phase (p : ℝ × CV) (c : ℂ) (hc : Complex.normSq c = 1) :
    midHamiltonian (p.1,c•p.2) = midHamiltonian p := by
  simp only [midHamiltonian, Midpoint.hamiltonian, center_phase_general _ _ p c hc, potential_phase c hc]

lemma backward_forward (p : ℝ × CV) : backwardMid (p.1,forwardMid p) = p.2 :=
  Midpoint.step_inverse _ lipschitz parameter parameter_contract p
lemma forward_backward (p : ℝ × CV) : forwardMid (p.1,backwardMid p) = p.2 := by
  simpa only [neg_neg, forwardMid, backwardMid] using Midpoint.step_inverse _ lipschitz (fun t ↦ -parameter t)
    (Midpoint.neg_small parameter_contract) p
lemma forwardMid_start (z : CV) : forwardMid (0,z) = z :=
  Midpoint.step_zero _ lipschitz _ _ 0 parameter_zero z

lemma center_bound (t : ℝ) (z : UnitQuadric) : normSquared (center (t,z)) ∈ Ioo (1/2:ℝ) 2 :=
  ⟨center_norm_gt_half lipschitz _ _ parameter_small t z,
    lt_of_le_of_lt (center_norm_le_one lipschitz _ _ t z) (by norm_num)⟩

lemma mid_equation (t : ℝ) (z : UnitQuadric) (v : CV) :
    omega (deriv (fun s ↦ forwardMid (s,z)) t) v =
      fderiv ℝ (fun w ↦ midHamiltonian (t,w)) (forwardMid (t,z)) v := by
  simpa only [forwardMid, midHamiltonian, symplectic_apply] using Midpoint.step_hamiltonian_equation symplectic symplectic_skew _ lipschitz vectorField_smooth
    parameter parameter_contract parameter_smooth potential potential_smooth (t,z)
    (vectorField_hamiltonian (lt_trans (center_bound t z).2 (by norm_num))) v

lemma center_identity (p : ℝ × CV) : center p = p.2 + parameter p.1 • vectorField (center p) :=
  Midpoint.resolvent_eq _ lipschitz _ _ p
lemma forwardMid_center (p : ℝ × CV) : forwardMid p = center p + parameter p.1 • vectorField (center p) :=
  Midpoint.step_center _ lipschitz _ _ p
lemma center_average (p : ℝ × CV) : (2:ℝ) • center p = p.2 + forwardMid p := by
  dsimp [forwardMid, Midpoint.step, center]
  module

lemma center_zero_coordinate (p : ℝ × CV) : center p 0 = p.2 0 := by
  have h := congrFun (center_identity p) 0
  simpa only [Pi.add_apply, Pi.smul_apply, vectorField_zero_coordinate, smul_zero, add_zero] using h
lemma forwardMid_zero_coordinate (p : ℝ × CV) : forwardMid p 0 = p.2 0 := by
  rw [forwardMid_center]
  simp only [Pi.add_apply, Pi.smul_apply, vectorField_zero_coordinate, smul_zero, add_zero,
    center_zero_coordinate]

end ArnoldCounterexample.Construction

end

end OAI
