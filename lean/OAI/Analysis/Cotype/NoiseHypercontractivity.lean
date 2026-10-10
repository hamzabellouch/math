import OAI.Analysis.Cotype.CubeNoise

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype

theorem average_nonneg {α : Type*} [Fintype α] {f : α → ℝ} (h : ∀ a, 0 ≤ f a) :
    0 ≤ average f := mul_nonneg (by positivity) (Finset.sum_nonneg (fun a _ => h a))

theorem average_mono {α : Type*} [Fintype α] {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    average f ≤ average g :=
  mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => h a)) (by positivity)

theorem average_mul_sq_le {n : ℕ} (f g : Cube n → ℝ) :
    average (fun u => f u * g u) ^ 2 ≤
      average (fun u => f u ^ 2) * average (fun u => g u ^ 2) := by
  have h : |average (fun u => f u * g u)| ≤ cubeL2 ℝ f * cubeL2 ℝ g := by
    calc
      _ ≤ average (fun u => |f u * g u|) := by
        simpa only [Real.norm_eq_abs] using norm_average_le (fun u => f u * g u)
      _ ≤ _ := by simpa only [abs_mul, Real.norm_eq_abs] using average_norm_mul_le f g
  have hh := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (cubeL2_nonneg _) (cubeL2_nonneg _))).mpr h
  simpa only [sq_abs, mul_pow, cubeL2_sq, Real.norm_eq_abs, sq_abs] using hh

theorem cubeNoise_fourth_le {n : ℕ} (f : Cube n → ℝ) :
    average (fun u => cubeNoise f u ^ 4) ≤ average (fun u => f u ^ 2) ^ 2 := by
  induction n with
  | zero => simp [cubeNoise, average, Cube]; ring_nf; rfl
  | succ n ih =>
    let f0 : Cube n → ℝ := fun u => f (Fin.cons false u)
    let f1 : Cube n → ℝ := fun u => f (Fin.cons true u)
    let a : Cube n → ℝ := fun u => (1/2 : ℝ) • f0 u + (1/2 : ℝ) • f1 u
    let b : Cube n → ℝ := fun u => (1/2 : ℝ) • f0 u + (-1/2 : ℝ) • f1 u
    let A := cubeNoise a
    let B := cubeNoise b
    have ha (u : Cube n) : A u = (cubeNoise f0 u + cubeNoise f1 u) / 2 := by
      have h0 := congrFun (cubeNoise_smul (1/2 : ℝ) f0) u
      have h1 := congrFun (cubeNoise_smul (1/2 : ℝ) f1) u
      have hlin := congrFun (cubeNoise_add (fun u => (1/2 : ℝ) • f0 u)
        (fun u => (1/2 : ℝ) • f1 u)) u
      change A u = _ at hlin
      simp only [smul_eq_mul] at h0 h1 hlin
      linarith
    have hb (u : Cube n) : B u = (cubeNoise f0 u - cubeNoise f1 u) / 2 := by
      have h0 := congrFun (cubeNoise_smul (1/2 : ℝ) f0) u
      have h1 := congrFun (cubeNoise_smul (-1/2 : ℝ) f1) u
      have hlin := congrFun (cubeNoise_add (fun u => (1/2 : ℝ) • f0 u)
        (fun u => (-1/2 : ℝ) • f1 u)) u
      change B u = _ at hlin
      simp only [smul_eq_mul] at h0 h1 hlin
      linarith
    have hfalse (u : Cube n) : cubeNoise f (Fin.cons false u) = A u + B u / 2 := by
      rw [cubeNoise_cons_false, ha, hb]
      change (3/4 : ℝ) * cubeNoise f0 u + (1/4 : ℝ) * cubeNoise f1 u = _
      ring
    have htrue (u : Cube n) : cubeNoise f (Fin.cons true u) = A u - B u / 2 := by
      rw [cubeNoise_cons_true, ha, hb]
      change (1/4 : ℝ) * cubeNoise f0 u + (3/4 : ℝ) * cubeNoise f1 u = _
      ring
    let a2 := average (fun u => a u ^ 2)
    let b2 := average (fun u => b u ^ 2)
    let A4 := average (fun u => A u ^ 4)
    let B4 := average (fun u => B u ^ 4)
    let C := average (fun u => A u ^ 2 * B u ^ 2)
    have ha2 : 0 ≤ a2 := average_nonneg (fun u => sq_nonneg _)
    have hb2 : 0 ≤ b2 := average_nonneg (fun u => sq_nonneg _)
    have hA4 : 0 ≤ A4 := average_nonneg (fun u => by positivity)
    have hB4 : 0 ≤ B4 := average_nonneg (fun u => by positivity)
    have hA : A4 ≤ a2 ^ 2 := ih a
    have hB : B4 ≤ b2 ^ 2 := ih b
    have hC : C ^ 2 ≤ A4 * B4 := by
      have h := average_mul_sq_le (fun u => A u ^ 2) (fun u => B u ^ 2)
      have hpa : average (fun u => (A u ^ 2) ^ 2) = A4 := by
        dsimp [A4]; congr 1; funext u; ring
      have hpb : average (fun u => (B u ^ 2) ^ 2) = B4 := by
        dsimp [B4]; congr 1; funext u; ring
      rw [hpa, hpb] at h
      exact h
    have hCle : C ≤ a2 * b2 := by
      have hprod := mul_le_mul hA hB hB4 (sq_nonneg a2)
      nlinarith [mul_nonneg ha2 hb2]
    have hsum : a2 + b2 = average (fun u => f u ^ 2) := by
      rw [average_cons]
      dsimp [a2, b2, a, b, f0, f1]
      simp only [average, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u _
      ring
    have hout : average (fun u => cubeNoise f u ^ 4) = A4 + (3/2 : ℝ) * C + (1/16 : ℝ) * B4 := by
      rw [average_cons]
      simp_rw [hfalse, htrue]
      dsimp [A4, B4, C]
      simp only [average, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u _
      ring
    rw [hout, ← hsum]
    nlinarith [mul_nonneg ha2 hb2, sq_nonneg b2]

end Cotype

end

end OAI
