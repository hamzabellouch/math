import OAI.Geometry.HeilbronnTriangle.IntegralKernelMoment
import OAI.Geometry.HeilbronnTriangle.PairingDivisor

namespace OAI


namespace Problem355.LatticeMoment

open PairingDivisor

theorem pairing_divisor_moment_of_diagonal_form
    (S : Finset (Fin 3 → ℤ)) (L : AddSubgroup (Fin 3 → ℤ))
    (C : Matrix (Fin 3) (Fin 3) ℤ)
    (B R b e k : ℕ) (hB : B.Prime) (hR : B ^ e ≤ R) (hek : e ≤ k)
    (P Q : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))ˣ)
    (hC : C.map (Int.castRingHom (ZMod (B ^ k))) =
      (P : Matrix _ _ _) * Matrix.diagonal
        ![1, (B : ZMod (B ^ k)) ^ b, (B : ZMod (B ^ k)) ^ e] *
          (Q : Matrix _ _ _))
    (hbox : ∀ x ∈ S, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R)
    (hprimitive : ∀ x ∈ S, ∃ z : Fin 3 → ℤ, dotProduct x z = 1)
    (hcontain : ∀ v : Fin 3 → ℤ, (B ^ e) • v ∈ L)
    (hrows : ∀ i, C i ∈ L) :
    ∑ x ∈ S, (pairingDivisor L x : ℝ) ^ 3 ≤
      128 * (R : ℝ) ^ 3 * (B : ℝ) ^ (b + e) := by
  apply cubic_divisor_moment_of_diagonal_form S (pairingDivisor L) C
    B R b e k hB hR hek P Q hC hbox
  · intro x hx
    obtain ⟨z, hz⟩ := hprimitive x hx
    exact (pairingDivisor_pos_and_dvd L x z hz (B ^ e)
      (pow_pos hB.pos _) hcontain).2
  · intro x hx i
    simpa only [Matrix.mulVec, dotProduct_comm] using
      pairingDivisor_dvd_pairing L x (C i) (hrows i)

theorem pairing_divisor_cube_div_index_le
    (L : AddSubgroup (Fin 3 → ℤ)) (x z : Fin 3 → ℤ)
    (B b e k : ℕ) (hB : 0 < B) (hek : e ≤ k)
    (hprimitive : dotProduct x z = 1)
    (hcontain : ∀ v : Fin 3 → ℤ, (B ^ e) • v ∈ L) :
    (pairingDivisor L x : ℝ) ^ 3 / ((B : ℝ) ^ b * (B : ℝ) ^ e) ≤
      ((B : ℝ) ^ k) ^ 2 := by
  exact divisor_cube_div_index_le_modulus_sq B b e k (pairingDivisor L x) hB hek
    (pairingDivisor_pos_and_dvd L x z hprimitive (B ^ e)
      (pow_pos hB _) hcontain).2

end Problem355.LatticeMoment

end OAI
