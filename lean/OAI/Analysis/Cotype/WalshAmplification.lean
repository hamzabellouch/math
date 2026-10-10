import OAI.Analysis.Cotype.WalshMonotonicity

namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def l2AmplificationLinear (T : X →L[ℝ] Y) :
    PiLp 2 (fun _ : Ω => X) →ₗ[ℝ] PiLp 2 (fun _ : Ω => Y) where
  toFun x := toLp 2 (fun a => T (x a))
  map_add' x y := by ext a; exact T.map_add _ _
  map_smul' c x := by ext a; exact T.map_smul c _

omit [DecidableEq Ω] in
theorem l2AmplificationLinear_bound (T : X →L[ℝ] Y) (x : PiLp 2 (fun _ : Ω => X)) :
    ‖l2AmplificationLinear T x‖ ≤ ‖T‖ * ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  exact Finset.sum_le_sum (fun a _ => by
    simpa [l2AmplificationLinear, mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg T) (norm_nonneg (x a)))).mpr
        (T.le_opNorm (x a)))

def l2Amplification (T : X →L[ℝ] Y) :
    PiLp 2 (fun _ : Ω => X) →L[ℝ] PiLp 2 (fun _ : Ω => Y) :=
  (l2AmplificationLinear (Ω := Ω) T).mkContinuous ‖T‖
    (fun x => l2AmplificationLinear_bound T x)

omit [DecidableEq Ω] in
@[simp] theorem l2Amplification_apply (T : X →L[ℝ] Y)
    (x : PiLp 2 (fun _ : Ω => X)) (a : Ω) : l2Amplification T x a = T (x a) := rfl

omit [NormedSpace ℝ X] [DecidableEq Ω] in
theorem cubeL2_piLp_sq {n : ℕ} (f : Cube n → PiLp 2 (fun _ : Ω => X)) :
    cubeL2 (PiLp 2 (fun _ : Ω => X)) f ^ 2 =
      ∑ a : Ω, cubeL2 X (fun u => f u a) ^ 2 := by
  simp_rw [cubeL2_sq, PiLp.norm_sq_eq_of_L2]
  simp only [average, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

omit [DecidableEq Ω] in
@[simp] theorem operatorWalsh_amplification_apply {n : ℕ} (T : X →L[ℝ] Y)
    (f : Cube n → PiLp 2 (fun _ : Ω => X)) (v : Cube n) (a : Ω) :
    operatorWalsh (l2Amplification T) f v a =
      operatorWalsh T (fun u => f u a) v := by
  simp [operatorWalsh, vectorWalsh, average]

omit [DecidableEq Ω] in
theorem operatorWalsh_amplification_bound {n : ℕ} (T : X →L[ℝ] Y)
    (f : Cube n → PiLp 2 (fun _ : Ω => X)) :
    cubeL2 (PiLp 2 (fun _ : Ω => Y)) (operatorWalsh (l2Amplification T) f) ≤
      walshNorm n T * cubeL2 (PiLp 2 (fun _ : Ω => X)) f := by
  apply (sq_le_sq₀ (cubeL2_nonneg _)
    (mul_nonneg (walshNorm_nonneg n T) (cubeL2_nonneg _))).mp
  rw [mul_pow, cubeL2_piLp_sq, cubeL2_piLp_sq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  simp only [operatorWalsh_amplification_apply]
  simpa only [mul_pow] using (sq_le_sq₀ (cubeL2_nonneg _)
    (mul_nonneg (walshNorm_nonneg n T) (cubeL2_nonneg _))).mpr
      (operatorWalsh_le_walshNorm T (fun u => f u a))

omit [DecidableEq Ω] in
theorem walshNorm_amplification_le (n : ℕ) (T : X →L[ℝ] Y) :
    walshNorm n (l2Amplification (Ω := Ω) T) ≤ walshNorm n T :=
  walshNorm_le_of_bound _ (walshNorm_nonneg n T) (operatorWalsh_amplification_bound T)

omit [NormedSpace ℝ X] in
theorem cubeL2_piLp_single {n : ℕ} (a : Ω) (f : Cube n → X) :
    cubeL2 (PiLp 2 (fun _ : Ω => X)) (fun u => PiLp.single 2 a (f u)) = cubeL2 X f := by
  simp [cubeL2, PiLp.norm_single]

theorem operatorWalsh_amplification_single {n : ℕ} (T : X →L[ℝ] Y)
    (a : Ω) (f : Cube n → X) :
    operatorWalsh (l2Amplification T) (fun u => PiLp.single 2 a (f u)) =
      fun v => PiLp.single 2 a (operatorWalsh T f v) := by
  classical
  funext v
  ext b
  simp only [operatorWalsh_amplification_apply, PiLp.single, ofLp_toLp]
  by_cases h : b = a
  · subst b
    simp
  · simp [h, operatorWalsh, vectorWalsh, average]

theorem walshNorm_amplification [Nonempty Ω] (n : ℕ) (T : X →L[ℝ] Y) :
    walshNorm n (l2Amplification (Ω := Ω) T) = walshNorm n T := by
  apply (walshNorm_amplification_le n T).antisymm
  apply walshNorm_le_of_bound T (walshNorm_nonneg n _)
  intro f
  obtain ⟨a⟩ := ‹Nonempty Ω›
  have h := operatorWalsh_le_walshNorm (l2Amplification T)
    (fun u => PiLp.single 2 a (f u))
  simpa only [operatorWalsh_amplification_single, cubeL2_piLp_single] using h

end Cotype

end

end OAI
