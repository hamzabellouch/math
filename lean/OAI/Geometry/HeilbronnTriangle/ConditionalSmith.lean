import OAI.Geometry.HeilbronnTriangle.ConditionalMatrix
import OAI.Geometry.HeilbronnTriangle.MinorInvariant
import OAI.Geometry.HeilbronnTriangle.RepeatedLabels

namespace OAI


namespace Problem355.ConditionalMatrix

open scoped BigOperators

theorem arrayMatrix_map {X : Type*} {B k j : ℕ} (hjk : j ≤ k)
    (digit : Fin 3 → Fin 3 → Fin k → X → Fin B)
    (f : Fin 3 → Fin 3 → Fin k → X) :
    (arrayMatrix digit f k).map (ZMod.castHom (Nat.pow_dvd_pow B hjk) (ZMod (B ^ j))) =
      arrayMatrix digit f j := by
  ext a c
  simp only [Matrix.map_apply, arrayMatrix, map_natCast]

theorem array_moment_le_two_of_diagonal {X : Type*} [Fintype X] [Nonempty X]
    {B k : ℕ} (hB : B.Prime) (hk : 0 < k)
    (digit : Fin 3 → Fin 3 → Fin k → X → Fin B)
    (hinj : ∀ a c v, Function.Injective (digit a c v))
    (hpos : ∀ a c v x, 0 < (digit a c v x).val)
    (b e : (Fin 3 → Fin 3 → Fin k → X) → ℕ)
    (hbe : ∀ f, b f ≤ e f) (hek : ∀ f, e f ≤ k)
    (P Q : (Fin 3 → Fin 3 → Fin k → X) →
      Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
    (hdiag : ∀ f, arrayMatrix digit f k =
      (P f : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) *
        Matrix.diagonal ![1, ((B ^ b f : ℕ) : ZMod (B ^ k)),
          ((B ^ e f : ℕ) : ZMod (B ^ k))] *
      (Q f : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))))
    (hsmall : (B : ℝ) * (1 / (Fintype.card X : ℝ)) ^ 4 ≤ 1 / 2) :
    (∑ f : Fin 3 → Fin 3 → Fin k → X,
      (1 / (Fintype.card (Fin 3 → Fin 3 → Fin k → X) : ℝ)) * (B : ℝ) ^ b f) ≤ 2 := by
  apply array_moment_le_two hB hk digit hinj hpos b
    (fun f => (hbe f).trans (hek f)) _ hsmall
  intro j hjpos hj f hbf
  have h := (UnitPivot.minorsVanish_reduce_prime_power_iff hB (hbe f) hj
    (P f) (Q f) (arrayMatrix digit f k) (hdiag f)).mpr hbf
  simpa only [arrayMatrix_map hj] using h

theorem collision_moment_le_six_div {Λ X : Type*}
    [Fintype Λ] [DecidableEq Λ] [Nonempty Λ] [Fintype X] [Nonempty X]
    {B k : ℕ} (hB : B.Prime) (hk : 0 < k)
    (digit : Λ → Λ → Λ → Fin 3 → Fin 3 → Fin k → X → Fin B)
    (hinj : ∀ a b c i l v, Function.Injective (digit a b c i l v))
    (hpos : ∀ a b c i l v x, 0 < (digit a b c i l v x).val)
    (val : Λ → Λ → Λ → (Fin 3 → Fin 3 → Fin k → X) → ℕ)
    (hval : ∀ a b c f, val a b c f ≤ k)
    (hminor : ∀ a b c j, 1 ≤ j → j ≤ k → ∀ f, j ≤ val a b c f →
      UnitPivot.MinorsVanish (arrayMatrix (digit a b c) f j))
    (hsmall : (B : ℝ) * (1 / (Fintype.card X : ℝ)) ^ 4 ≤ 1 / 2) :
    (∑ a : Λ, ∑ b : Λ, ∑ c : Λ, ∑ f : Fin 3 → Fin 3 → Fin k → X,
      (1 / (Fintype.card (Fin 3 → Fin 3 → Fin k → X) : ℝ)) *
        (if a = b ∨ a = c ∨ b = c then (B : ℝ) ^ val a b c f else 0)) /
          (Fintype.card Λ : ℝ) ^ 3 ≤ 6 / (Fintype.card Λ : ℝ) := by
  have h := Sampling.conditional_collision_moment_le
    (α := Λ) (Ω := Fin 3 → Fin 3 → Fin k → X)
    (fun _ _ _ _ => 1 / (Fintype.card (Fin 3 → Fin 3 → Fin k → X) : ℝ))
    (fun a b c f => (B : ℝ) ^ val a b c f) 2 (by norm_num)
    (fun a b c => array_moment_le_two hB hk (digit a b c) (hinj a b c)
      (hpos a b c) (val a b c) (hval a b c) (hminor a b c) hsmall)
  norm_num only [show (3 : ℝ) * 2 = 6 by norm_num] at h
  exact h

end Problem355.ConditionalMatrix

end OAI
