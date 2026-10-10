import OAI.Geometry.HeilbronnTriangle.LatticeMoment
import OAI.Geometry.HeilbronnTriangle.DiagonalKernel

namespace OAI


namespace Problem355.LatticeMoment

theorem cast_mulVec_eq_zero_of_dvd_rows {m d : ℕ}
    (C : Matrix (Fin m) (Fin d) ℤ) (x : Fin d → ℤ) (g q : ℕ)
    (hqg : q ∣ g) (hrows : ∀ i, (g : ℤ) ∣ (C.mulVec x) i) :
    (C.map (Int.castRingHom (ZMod q))).mulVec (fun i => (x i : ZMod q)) = 0 := by
  ext i
  have hqgz : (q : ℤ) ∣ (g : ℤ) := by exact_mod_cast hqg
  have hz : ((C.mulVec x) i : ZMod q) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr (hqgz.trans (hrows i))
  simpa [Matrix.mulVec, dotProduct] using hz

theorem cubic_divisor_moment_of_diagonal_reductions
    (S : Finset (Fin 3 → ℤ)) (g : (Fin 3 → ℤ) → ℕ)
    (C : Matrix (Fin 3) (Fin 3) ℤ)
    (B R b e : ℕ) (hB : B.Prime) (hR : B ^ e ≤ R)
    (hbox : ∀ x ∈ S, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R)
    (hg : ∀ x ∈ S, g x ∣ B ^ e)
    (hrows : ∀ x ∈ S, ∀ i, (g x : ℤ) ∣ (C.mulVec x) i)
    (hdiag : ∀ j ≤ e,
      ∃ P Q : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ j)))ˣ,
        C.map (Int.castRingHom (ZMod (B ^ j))) =
          (P : Matrix _ _ _) * Matrix.diagonal
            ![1, (B : ZMod (B ^ j)) ^ b, (B : ZMod (B ^ j)) ^ e] *
              (Q : Matrix _ _ _)) :
    ∑ x ∈ S, (g x : ℝ) ^ 3 ≤
      128 * (R : ℝ) ^ 3 * (B : ℝ) ^ (b + e) := by
  classical
  let : NeZero B := ⟨hB.ne_zero⟩
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB.pos
  let T : ∀ j : ℕ, Finset (Fin 3 → ZMod (B ^ j)) := fun j =>
    Finset.univ.filter fun x => (C.map (Int.castRingHom (ZMod (B ^ j)))).mulVec x = 0
  apply cubic_divisor_moment_of_residue_counts S g B R b e hB hR T hbox hg
  · intro j hj x hx hjg
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      cast_mulVec_eq_zero_of_dvd_rows C x (g x) (B ^ j) hjg (hrows x hx)⟩
  · intro j hj
    obtain ⟨P, Q, hC⟩ := hdiag j hj
    have hc := DiagonalKernel.card_kernel_prime_power_density B j b e hj
      (C.map (Int.castRingHom (ZMod (B ^ j)))) P Q hC
    have htc : (T j).card = Nat.card
        (DiagonalKernel.Kernel (C.map (Int.castRingHom (ZMod (B ^ j))))) := by
      simp [T, DiagonalKernel.Kernel, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hc' : (T j).card * B ^ (j + (j - b)) = B ^ (3 * j) := by
      rw [htc]
      simpa only [← pow_mul, Nat.mul_comm j 3] using hc
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (B : ℝ) ^ (j + (j - b)))).mpr
    exact_mod_cast hc'.le

theorem divisor_cube_le_index_mul_modulus_sq
    (B b e k g : ℕ) (hB : 0 < B) (hek : e ≤ k) (hg : g ∣ B ^ e) :
    g ^ 3 ≤ (B ^ b * B ^ e) * (B ^ k) ^ 2 := by
  have hgE : g ≤ B ^ e := Nat.le_of_dvd (pow_pos hB _) hg
  have hEH : B ^ e ≤ B ^ k := Nat.pow_le_pow_right hB hek
  have hD : 1 ≤ B ^ b := pow_pos hB _
  calc
    g ^ 3 ≤ (B ^ e) ^ 3 := Nat.pow_le_pow_left hgE 3
    _ = B ^ e * (B ^ e) ^ 2 := by ring
    _ ≤ B ^ e * (B ^ k) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hEH 2)
    _ ≤ (B ^ b * B ^ e) * (B ^ k) ^ 2 := by
      apply Nat.mul_le_mul_right
      simpa using Nat.mul_le_mul_right (B ^ e) hD

theorem divisor_cube_div_index_le_modulus_sq
    (B b e k g : ℕ) (hB : 0 < B) (hek : e ≤ k) (hg : g ∣ B ^ e) :
    (g : ℝ) ^ 3 / ((B : ℝ) ^ b * (B : ℝ) ^ e) ≤ ((B : ℝ) ^ k) ^ 2 := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  apply (div_le_iff₀ (by positivity)).mpr
  have h := divisor_cube_le_index_mul_modulus_sq B b e k g hB hek hg
  have h' : (g : ℝ) ^ 3 ≤
      ((B : ℝ) ^ b * (B : ℝ) ^ e) * ((B : ℝ) ^ k) ^ 2 := by exact_mod_cast h
  simpa only [mul_comm] using h'

theorem cubic_divisor_moment_of_diagonal_form
    (S : Finset (Fin 3 → ℤ)) (g : (Fin 3 → ℤ) → ℕ)
    (C : Matrix (Fin 3) (Fin 3) ℤ)
    (B R b e k : ℕ) (hB : B.Prime) (hR : B ^ e ≤ R) (hek : e ≤ k)
    (P Q : (Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))ˣ)
    (hC : C.map (Int.castRingHom (ZMod (B ^ k))) =
      (P : Matrix _ _ _) * Matrix.diagonal
        ![1, (B : ZMod (B ^ k)) ^ b, (B : ZMod (B ^ k)) ^ e] *
          (Q : Matrix _ _ _))
    (hbox : ∀ x ∈ S, ∀ i, -(R : ℤ) ≤ x i ∧ x i ≤ R)
    (hg : ∀ x ∈ S, g x ∣ B ^ e)
    (hrows : ∀ x ∈ S, ∀ i, (g x : ℤ) ∣ (C.mulVec x) i) :
    ∑ x ∈ S, (g x : ℝ) ^ 3 ≤
      128 * (R : ℝ) ^ 3 * (B : ℝ) ^ (b + e) := by
  classical
  let : NeZero B := ⟨hB.ne_zero⟩
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB.pos
  let T : ∀ j : ℕ, Finset (Fin 3 → ZMod (B ^ j)) := fun j =>
    Finset.univ.filter fun x => (C.map (Int.castRingHom (ZMod (B ^ j)))).mulVec x = 0
  apply cubic_divisor_moment_of_residue_counts S g B R b e hB hR T hbox hg
  · intro j hj x hx hjg
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      cast_mulVec_eq_zero_of_dvd_rows C x (g x) (B ^ j) hjg (hrows x hx)⟩
  · intro j hj
    have hc := DiagonalKernel.card_kernel_reduction_density B k j b e
      (hj.trans hek) hj (C.map (Int.castRingHom (ZMod (B ^ k)))) P Q hC
    have hmap : (C.map (Int.castRingHom (ZMod (B ^ k)))).map
        (ZMod.castHom (pow_dvd_pow B (hj.trans hek)) (ZMod (B ^ j))) =
        C.map (Int.castRingHom (ZMod (B ^ j))) := by
      ext i l
      simp
    rw [hmap] at hc
    have htc : (T j).card = Nat.card
        (DiagonalKernel.Kernel (C.map (Int.castRingHom (ZMod (B ^ j))))) := by
      simp [T, DiagonalKernel.Kernel, Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hc' : (T j).card * B ^ (j + (j - b)) = B ^ (3 * j) := by
      rw [htc]
      simpa only [← pow_mul, Nat.mul_comm j 3] using hc
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (B : ℝ) ^ (j + (j - b)))).mpr
    exact_mod_cast hc'.le

end Problem355.LatticeMoment

end OAI
