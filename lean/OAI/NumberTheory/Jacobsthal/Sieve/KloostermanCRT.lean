import OAI.NumberTheory.Jacobsthal.Harmonic.KloostermanCRTCharacter

namespace OAI

namespace Erdos970

section

namespace ErdosKloosterman

attribute [local instance] Classical.decEq

theorem sum_mulShift {R : Type*} [CommRing R] [Fintype R]
    (ψ : AddChar R ℂ) (r a b : R) :
    sum (ψ.mulShift r) a b = sum ψ (r*a) (r*b) := by
  unfold sum
  apply Finset.sum_congr rfl
  intro u _
  rw [AddChar.mulShift_apply]
  congr 1
  ring

theorem standardSum_crt (m n : ℕ) [NeZero m] [NeZero n] (hmn : m.Coprime n)
    (h k : ℤ) :
    standardSum (m*n) h k =
      standardSum m (Nat.gcdB m n * h) (Nat.gcdB m n * k) *
        standardSum n (Nat.gcdA m n * h) (Nat.gcdA m n * k) := by
  unfold standardSum
  rw [stdAddChar_crt m n hmn, sum_product_ringEquiv]
  simp only [map_intCast, Prod.fst_intCast, Prod.snd_intCast, sum_mulShift,
    Int.cast_mul]

theorem norm_standardSum_crt (m n : ℕ) [NeZero m] [NeZero n] (hmn : m.Coprime n)
    (h k : ℤ) :
    ‖standardSum (m*n) h k‖ =
      ‖standardSum m (Nat.gcdB m n * h) (Nat.gcdB m n * k)‖ *
        ‖standardSum n (Nat.gcdA m n * h) (Nat.gcdA m n * k)‖ := by
  rw [standardSum_crt m n hmn, norm_mul]

end ErdosKloosterman

end

end Erdos970

end OAI
