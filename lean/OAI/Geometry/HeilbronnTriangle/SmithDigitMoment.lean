import OAI.Geometry.HeilbronnTriangle.PrimePowerData
import OAI.Geometry.HeilbronnTriangle.ConditionalSmith

namespace OAI


namespace Problem355.PrimePowerData

open scoped BigOperators

noncomputable def ofArray {X : Type*} {B k : ℕ}
    (hB : B.Prime) (hk : 0 < k)
    (digit : Fin 3 → Fin 3 → Fin k → X → Fin B)
    (hpos : ∀ a c v x, 0 < (digit a c v x).val)
    (f : Fin 3 → Fin 3 → Fin k → X) :
    PrimePowerData B k (ConditionalMatrix.arrayMatrix digit f k) :=
  ofUnit hB (ConditionalMatrix.encoded_isUnit hB hk hk
    (fun v => digit 0 0 v (f 0 0 v)) (fun v => hpos 0 0 v (f 0 0 v)))

theorem array_moment_le_two {X : Type*} [Fintype X] [Nonempty X]
    {B k : ℕ} (hB : B.Prime) (hk : 0 < k)
    (digit : Fin 3 → Fin 3 → Fin k → X → Fin B)
    (hinj : ∀ a c v, Function.Injective (digit a c v))
    (hpos : ∀ a c v x, 0 < (digit a c v x).val)
    (d : ∀ f : Fin 3 → Fin 3 → Fin k → X,
      PrimePowerData B k (ConditionalMatrix.arrayMatrix digit f k))
    (hsmall : (B : ℝ) * (1 / (Fintype.card X : ℝ)) ^ 4 ≤ 1 / 2) :
    (∑ f : Fin 3 → Fin 3 → Fin k → X,
      (1 / (Fintype.card (Fin 3 → Fin 3 → Fin k → X) : ℝ)) *
        (B : ℝ) ^ (d f).b) ≤ 2 := by
  exact ConditionalMatrix.array_moment_le_two_of_diagonal hB hk digit hinj hpos
    (fun f => (d f).b) (fun f => (d f).e) (fun f => (d f).b_le_e)
    (fun f => (d f).e_le_k) (fun f => (d f).left) (fun f => (d f).right)
    (fun f => (d f).diagonalization) hsmall

theorem chosen_array_moment_le_two {X : Type*} [Fintype X] [Nonempty X]
    {B k : ℕ} (hB : B.Prime) (hk : 0 < k)
    (digit : Fin 3 → Fin 3 → Fin k → X → Fin B)
    (hinj : ∀ a c v, Function.Injective (digit a c v))
    (hpos : ∀ a c v x, 0 < (digit a c v x).val)
    (hsmall : (B : ℝ) * (1 / (Fintype.card X : ℝ)) ^ 4 ≤ 1 / 2) :
    (∑ f : Fin 3 → Fin 3 → Fin k → X,
      (1 / (Fintype.card (Fin 3 → Fin 3 → Fin k → X) : ℝ)) *
        (B : ℝ) ^ (ofArray hB hk digit hpos f).b) ≤ 2 :=
  array_moment_le_two hB hk digit hinj hpos (ofArray hB hk digit hpos) hsmall

theorem collision_moment_le_six_div {Λ X : Type*}
    [Fintype Λ] [DecidableEq Λ] [Nonempty Λ] [Fintype X] [Nonempty X]
    {B k : ℕ} (hB : B.Prime) (hk : 0 < k)
    (digit : Λ → Λ → Λ → Fin 3 → Fin 3 → Fin k → X → Fin B)
    (hinj : ∀ a b c i l v, Function.Injective (digit a b c i l v))
    (hpos : ∀ a b c i l v x, 0 < (digit a b c i l v x).val)
    (d : ∀ a b c : Λ, ∀ f : Fin 3 → Fin 3 → Fin k → X,
      PrimePowerData B k (ConditionalMatrix.arrayMatrix (digit a b c) f k))
    (hsmall : (B : ℝ) * (1 / (Fintype.card X : ℝ)) ^ 4 ≤ 1 / 2) :
    (∑ a : Λ, ∑ b : Λ, ∑ c : Λ, ∑ f : Fin 3 → Fin 3 → Fin k → X,
      (1 / (Fintype.card (Fin 3 → Fin 3 → Fin k → X) : ℝ)) *
        (if a = b ∨ a = c ∨ b = c then (B : ℝ) ^ (d a b c f).b else 0)) /
          (Fintype.card Λ : ℝ) ^ 3 ≤ 6 / (Fintype.card Λ : ℝ) := by
  apply ConditionalMatrix.collision_moment_le_six_div hB hk digit hinj hpos
    (fun a b c f => (d a b c f).b) (fun a b c f => (d a b c f).b_le_k) _ hsmall
  intro a b c j _ hj f hf
  have h := ((d a b c f).minors_vanish_iff hB hj).mpr hf
  rwa [ConditionalMatrix.arrayMatrix_map hj] at h

end Problem355.PrimePowerData

end OAI
