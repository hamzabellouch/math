import OAI.Analysis.Cotype.PrimalMomentLifts
import OAI.Analysis.Cotype.CotypeAmplification

namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
theorem finiteL2Dual_norm (g : Ω → (X →L[ℝ] ℝ)) :
    ‖finiteL2Dual g‖ = ‖(toLp 2 g : PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ)))‖ := by
  apply (finiteL2Dual_norm_le g).antisymm
  let R := ‖(toLp 2 g : PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ)))‖
  have hR : 0 ≤ R := norm_nonneg _
  have hR2 : R^2 = ∑ i, ‖g i‖^2 := PiLp.norm_sq_eq_of_L2 _ _
  have hsq : R^2 ≤ ‖finiteL2Dual g‖ * R := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let S := ∑ i, ‖g i‖
    have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => norm_nonneg _)
    let δ := ε / (S+1)
    have hδ : 0 < δ := div_pos hε (by positivity)
    choose x hx he using (fun i => exists_unit_eval_gt (g i) (by linarith : ‖g i‖ - δ < ‖g i‖))
    let z : PiLp 2 (fun _ : Ω => X) := toLp 2 (fun i => ‖g i‖ • x i)
    have hzn : ‖z‖ ≤ R := by
      apply (sq_le_sq₀ (norm_nonneg _) hR).mp
      rw [PiLp.norm_sq_eq_of_L2, hR2]
      apply Finset.sum_le_sum
      intro i _
      have hh : ‖g i‖ * ‖x i‖ ≤ ‖g i‖ := mul_le_of_le_one_right (norm_nonneg _) (hx i)
      simpa only [z, ofLp_toLp, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
        (sq_le_sq₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mpr hh
    have hv : finiteL2Dual g z ≤ ‖finiteL2Dual g‖ * R := by
      exact (le_abs_self _).trans ((finiteL2Dual g).le_opNorm z |>.trans
        (mul_le_mul_of_nonneg_left hzn (norm_nonneg _)))
    have hδS : δ * S ≤ ε := by
      have hh : δ * (S+1) = ε := by dsimp [δ]; field_simp
      nlinarith
    calc
      R^2 = ∑ i, ‖g i‖^2 := hR2
      _ ≤ ∑ i, (‖g i‖ * (g i (x i)) + δ * ‖g i‖) :=
        Finset.sum_le_sum (fun i _ => by
          nlinarith [mul_le_mul_of_nonneg_left (show ‖g i‖ ≤ g i (x i) + δ by linarith [he i]) (norm_nonneg (g i))])
      _ = finiteL2Dual g z + δ*S := by
        simp only [finiteL2Dual_apply, z, map_smul, smul_eq_mul, S,
          Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ _ := by linarith
  change R ≤ ‖finiteL2Dual g‖
  by_cases hz : R = 0
  · rw [hz]; exact norm_nonneg _
  have hp : 0 < R := lt_of_le_of_ne hR (Ne.symm hz)
  nlinarith

theorem tupleDualCoordinates_norm (ψ : PiLp 2 (fun _ : Ω => X) →L[ℝ] ℝ) :
    ‖(toLp 2 (tupleDualCoordinates ψ) : PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ)))‖ = ‖ψ‖ := by
  rw [← finiteL2Dual_norm]
  exact congrArg norm (tupleDual_eq ψ).symm

theorem fixedCotypeBound_dual_l2Amplification {m : ℕ} {D : ℝ}
    (hD : FixedCotypeBound (X →L[ℝ] ℝ) m D) :
    FixedCotypeBound (PiLp 2 (fun _ : Ω => X) →L[ℝ] ℝ) m D := by
  have h := fixedCotypeBound_l2Amplification (Ω := Ω) hD
  refine ⟨hD.1, fun x => ?_⟩
  let y : Fin m → PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ)) :=
    fun i => toLp 2 (tupleDualCoordinates (x i))
  have hy : ∀ i, ‖y i‖ = ‖x i‖ := fun i => tupleDualCoordinates_norm (x i)
  have hr (u : Cube m) : rademacherSum (PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ))) y u =
      toLp 2 (tupleDualCoordinates (rademacherSum (PiLp 2 (fun _ : Ω => X) →L[ℝ] ℝ) x u)) := by
    ext a z
    simp [rademacherSum, tupleDualCoordinates, y]
  have hnorm : cubeL2 (PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ)))
      (rademacherSum (PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ))) y) =
      cubeL2 (PiLp 2 (fun _ : Ω => X) →L[ℝ] ℝ)
        (rademacherSum (PiLp 2 (fun _ : Ω => X) →L[ℝ] ℝ) x) := by
    simp only [cubeL2, hr, tupleDualCoordinates_norm]
  simpa only [hy, hnorm] using h.2 y

end Cotype

end

end OAI
