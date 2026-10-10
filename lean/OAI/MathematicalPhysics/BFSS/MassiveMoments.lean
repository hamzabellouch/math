import Mathlib
import OAI.MathematicalPhysics.BFSS.PotentialBounds

namespace OAI

/-! Global core gradient and confining moment bounds. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open MeasureTheory Matrix Finset
variable {N : ℕ} (M : AlgebraData N)

def deformedCoreEnergy (h m : ℝ) (f : SmoothCore N) : ℝ :=
  (1/16 : ℝ) * ∑ α : SpinIndex, ‖coreToL2 (M.deformedCoreCharge h m α f)‖^2

lemma weighted_core_square_integrable (g : Boson N → ℝ) (hg : Continuous g) (f : SmoothCore N) :
    Integrable (fun x => g x * ‖f x‖^2) volume := by
  have hc : HasCompactSupport (fun x : Boson N => ‖f x‖^2) :=
    f.hasCompactSupport.comp_left (g := fun z : Fermion N => ‖z‖^2) (by simp)
  exact (hg.mul (f.continuous.norm.pow 2)).integrable_of_hasCompactSupport
    (hc.mul_left (f := g))

lemma bosonic_core_integrable (h m : ℝ) (f : SmoothCore N) :
    Integrable (fun x => M.deformedBosonicPotential h m x * ‖f x‖^2) volume := by
  have hh : (fun x : Boson N => M.deformedBosonicPotential h m x * ‖f x‖^2) =
      fun x => (1/16 : ℝ) * ∑ α : SpinIndex, ‖MixedEnergy.field (M.deformedRealField h m α)
        (M.deformedRealField_contDiff h m α) f x‖^2 := by
    funext x
    exact (M.deformed_potential_average h m x (f x)).symm
  rw [hh]
  exact (integrable_finsetSum _ (fun α _ => coreNormSq_integrable _)).const_mul _

lemma fermion_core_integrable (h m : ℝ) (f : SmoothCore N) :
    Integrable (fun x => inner ℝ (f x) (M.deformedFermionField h m x (f x))) volume := by
  have hh : (fun x : Boson N => inner ℝ (f x) (M.deformedFermionField h m x (f x))) =
      fun x => (1/16 : ℝ) * inner ℝ (f x)
        (MixedEnergy.remainderCore (M.kineticSkewSymbol) (M.deformedRealField h m)
          (M.deformedRealField_contDiff h m) f x) := by
    funext x
    rw [MixedEnergy.remainderCore_apply _ _ _ (M.deformedRealField_anticommutator h m)]
    simp only [deformedFermionField, _root_.smul_apply, real_inner_smul_right]
  rw [hh]
  exact (MixedEnergy.inner_integrable _ _).const_mul _

lemma deformedPotential_fermion_lower (hN : 2 ≤ N) (h m : ℝ) (hh : 0 < h) (hm : 0 < m) :
    ∃ a : ℝ, 0 < a ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ (x : Boson N) (z : Fermion N),
      (a*‖x‖^2 - K) * ‖z‖^2 ≤ M.deformedBosonicPotential h m x * ‖z‖^2 +
        inner ℝ z (M.deformedFermionField h m x z) := by
  obtain ⟨c,hc,C,hC,hbound⟩ := M.deformedBosonicPotential_global hN
  let A := c*m^2
  let B := M.fermionGrowthConstant*h
  let D := C*(m^4/h^2) + M.fermionGrowthConstant*m
  have hA : 0 < A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity [M.fermionGrowthConstant_nonneg]
  let K := D + B^2/(2*A)
  refine ⟨A/2,by positivity,K,by dsimp [K]; positivity,?_⟩
  intro x z
  have hy : A/2*‖x‖^2 - K ≤ A*‖x‖^2 - B*‖x‖ - D := by
    have he : (A*‖x‖ - B)^2/(2*A) =
        (A*‖x‖^2 - B*‖x‖ - D) - (A/2*‖x‖^2-K) := by
      dsimp [K]
      field_simp [ne_of_gt hA]
      ring
    have hs : 0 ≤ (A*‖x‖ - B)^2/(2*A) := by positivity
    rw [he] at hs
    linarith
  have hu := hbound h m hh hm x
  have hl : A*‖x‖^2 - B*‖x‖ - D ≤ M.deformedBosonicPotential h m x -
      M.fermionGrowthConstant*(h*‖x‖+m) := by
    dsimp [A,B,D]
    linarith
  have hz := mul_le_mul_of_nonneg_right (hy.trans hl) (sq_nonneg ‖z‖)
  have hf := M.deformedFermionField_inner_lower h m x z
  rw [abs_of_pos hh, abs_of_pos hm] at hf
  nlinarith

theorem massive_core_gradient_moment (hN : 2 ≤ N) (h m : ℝ) (hh : 0 < h) (hm : 0 < m) :
    ∃ a : ℝ, 0 < a ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ f : SmoothCore N,
      (1/2 : ℝ) * ∑ p : SpaceIndex × ColorIndex N,
        ‖coreToL2 (coordinateDerivative p.1 p.2 f)‖^2 +
        a * (∫ x : Boson N, ‖x‖^2 * ‖f x‖^2) ≤
      M.deformedCoreEnergy h m f + K*‖coreToL2 f‖^2 := by
  obtain ⟨a,ha,K,hK,hbound⟩ := M.deformedPotential_fermion_lower hN h m hh hm
  refine ⟨a,ha,K,hK,?_⟩
  intro f
  have hi : Integrable (fun x : Boson N => (a*‖x‖^2-K)*‖f x‖^2) volume :=
    weighted_core_square_integrable _ (by fun_prop) f
  have hmom := weighted_core_square_integrable (fun x : Boson N => ‖x‖^2) (by fun_prop) f
  have hc := coreNormSq_integrable f
  have hr := (M.bosonic_core_integrable h m f).add (M.fermion_core_integrable h m f)
  have hint := integral_mono hi hr (fun x => hbound x (f x))
  have he : (∫ x : Boson N, (a*‖x‖^2-K)*‖f x‖^2) =
      a*(∫ x : Boson N, ‖x‖^2*‖f x‖^2) - K*‖coreToL2 f‖^2 := by
    simp_rw [sub_mul, mul_assoc]
    rw [integral_sub (hmom.const_mul a) (hc.const_mul K), integral_const_mul,
      integral_const_mul, ← coreToL2_norm_sq]
  rw [he] at hint
  simp only [Pi.add_apply] at hint
  unfold deformedCoreEnergy
  rw [M.averaged_core_energy]
  linarith

end
end BFSSQuantum.AlgebraData

end OAI
