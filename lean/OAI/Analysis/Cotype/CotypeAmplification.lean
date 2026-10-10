import OAI.Analysis.Cotype.WalshAmplification

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
@[simp] theorem rademacherSum_piLp_apply {m : ℕ}
    (x : Fin m → PiLp 2 (fun _ : Ω => X)) (ε : Cube m) (a : Ω) :
    rademacherSum (PiLp 2 (fun _ : Ω => X)) x ε a =
      rademacherSum X (fun i => x i a) ε := by
  simp [rademacherSum]

omit [DecidableEq Ω] in
theorem fixedCotypeBound_l2Amplification {m : ℕ} {D : ℝ}
    (h : FixedCotypeBound X m D) : FixedCotypeBound (PiLp 2 (fun _ : Ω => X)) m D := by
  refine ⟨h.1, fun x => ?_⟩
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg h.1 (cubeL2_nonneg _))).mp
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)), mul_pow, cubeL2_piLp_sq,
    Finset.mul_sum]
  simp_rw [PiLp.norm_sq_eq_of_L2]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  have ha := (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg h.1 (cubeL2_nonneg _))).mpr (h.2 (fun i => x i a))
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)), mul_pow] at ha
  simpa only [rademacherSum_piLp_apply] using ha

end Cotype

end

end OAI
