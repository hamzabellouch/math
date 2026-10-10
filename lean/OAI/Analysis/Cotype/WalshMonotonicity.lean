import OAI.Analysis.Cotype.WalshCoordinates

namespace OAI

noncomputable section
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem operatorWalsh_join {n j : ℕ} (T : X →L[ℝ] Y)
    (f : Cube (n+j) → X) (a : Cube n) (b : Cube j) :
    operatorWalsh T f (cubeJoin n j (a,b)) =
      vectorWalsh (fun d : Cube j => operatorWalsh T
        (fun c : Cube n => f (cubeJoin n j (c,d))) a) b :=
  vectorWalsh_join _ a b

theorem operatorWalsh_add_le {n j : ℕ} (T : X →L[ℝ] Y) (f : Cube (n+j) → X) :
    cubeL2 Y (operatorWalsh T f) ≤ walshNorm n T * cubeL2 X f := by
  rw [cubeL2_join]
  simp_rw [operatorWalsh_join]
  calc
    _ ≤ cubeL2 ℝ (fun a : Cube n => cubeL2 Y (fun d : Cube j =>
        operatorWalsh T (fun c : Cube n => f (cubeJoin n j (c,d))) a)) := by
      apply cubeL2_mono
      intro a
      simpa only [Real.norm_eq_abs, abs_of_nonneg (cubeL2_nonneg _)] using
        vectorWalsh_L2_le (fun d : Cube j => operatorWalsh T
          (fun c : Cube n => f (cubeJoin n j (c,d))) a)
    _ = cubeL2 ℝ (fun d : Cube j => cubeL2 Y
        (operatorWalsh T (fun c : Cube n => f (cubeJoin n j (c,d))))) :=
      cubeL2_comm _
    _ ≤ cubeL2 ℝ (fun d : Cube j => walshNorm n T * cubeL2 X
        (fun c : Cube n => f (cubeJoin n j (c,d)))) := by
      apply cubeL2_mono
      intro d
      simpa only [Real.norm_eq_abs, abs_of_nonneg (cubeL2_nonneg _),
        abs_of_nonneg (mul_nonneg (walshNorm_nonneg n T) (cubeL2_nonneg _))] using
        operatorWalsh_le_walshNorm T (fun c : Cube n => f (cubeJoin n j (c,d)))
    _ = _ := by
      rw [show (fun d : Cube j => walshNorm n T * cubeL2 X
        (fun c : Cube n => f (cubeJoin n j (c,d)))) =
        (fun d : Cube j => walshNorm n T • cubeL2 X
        (fun c : Cube n => f (cubeJoin n j (c,d)))) from rfl]
      rw [cubeL2_smul, abs_of_nonneg (walshNorm_nonneg n T), cubeL2_comm]
      rw [← cubeL2_join]

theorem walshNorm_add_le (n j : ℕ) (T : X →L[ℝ] Y) :
    walshNorm (n+j) T ≤ walshNorm n T :=
  walshNorm_le_of_bound T (walshNorm_nonneg n T) (operatorWalsh_add_le T)

theorem walshNorm_antitone (T : X →L[ℝ] Y) : Antitone (fun n => walshNorm n T) := by
  intro n k h
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
  exact walshNorm_add_le n j T

end Cotype

end

end OAI
