import OAI.Geometry.HeilbronnTriangle.SpecialNormals
import OAI.Geometry.HeilbronnTriangle.ShortestIntegralVector

namespace OAI


namespace Problem355.SpecialNormalShell

open scoped BigOperators

def IsSpecial (q : ℕ) (x : Fin 3 → ℤ) : Prop :=
  ∃ i j : Fin 3, (fun t => (x t : ZMod q)) ∈
    Submodule.span (ZMod q) {Pi.single i (1 : ZMod q) - Pi.single j 1}

theorem card_cube_le (S : Finset (Fin 3 → ℤ)) (M q : ℕ) (hq : 0 < q)
    (hbox : ∀ x ∈ S, ∀ i, -(M : ℤ) ≤ x i ∧ x i ≤ (M : ℤ))
    (hnonzero : ∀ x ∈ S, ∀ i, x i ≠ 0)
    (hspecial : ∀ x ∈ S, IsSpecial q x) :
    (S.card : ℝ) ≤ 576 * (M : ℝ) ^ 3 / (q : ℝ) ^ 2 := by
  classical
  let T : (Fin 3 × Fin 3) → Finset (Fin 3 → ℤ) := fun p =>
    S.filter fun x => (fun t => (x t : ZMod q)) ∈
      Submodule.span (ZMod q)
        {Pi.single p.1 (1 : ZMod q) - Pi.single p.2 1}
  have hcover : S ⊆ Finset.univ.biUnion T := by
    intro x hx
    obtain ⟨i, j, hij⟩ := hspecial x hx
    exact Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_univ _,
      Finset.mem_filter.mpr ⟨hx, hij⟩⟩
  have hcard : S.card ≤ ∑ p : Fin 3 × Fin 3, (T p).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hbound (p : Fin 3 × Fin 3) :
      ((T p).card : ℝ) ≤ 64 * (M : ℝ) ^ 3 / (q : ℝ) ^ 2 := by
    obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 3, k ≠ p.1 ∧ k ≠ p.2 := by
      rcases p with ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> decide
    apply SpecialNormals.card_exceptional_normals_le (T p) M q hq p.1 p.2 k hki hkj
    · intro x hx i
      exact hbox x (Finset.mem_filter.mp hx).1 i
    · intro x hx
      exact hnonzero x (Finset.mem_filter.mp hx).1 k
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
  calc
    (S.card : ℝ) ≤ ∑ p : Fin 3 × Fin 3, ((T p).card : ℝ) := by
      exact_mod_cast hcard
    _ ≤ ∑ _p : Fin 3 × Fin 3, 64 * (M : ℝ) ^ 3 / (q : ℝ) ^ 2 :=
      Finset.sum_le_sum fun p _ => hbound p
    _ = 576 * (M : ℝ) ^ 3 / (q : ℝ) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, Nat.reduceMul, nsmul_eq_mul]
      ring

theorem card_ball_le (S : Finset (Fin 3 → ℤ)) (R : ℝ) (hR : 0 ≤ R)
    (q : ℕ) (hq : 0 < q)
    (hnorm : ∀ x ∈ S, ‖IntegralMinima.toEuclidean x‖ ≤ R)
    (hnonzero : ∀ x ∈ S, ∀ i, x i ≠ 0)
    (hspecial : ∀ x ∈ S, IsSpecial q x) :
    (S.card : ℝ) ≤ 576 * R ^ 3 / (q : ℝ) ^ 2 := by
  have hbox : ∀ x ∈ S, ∀ i, -(⌊R⌋₊ : ℤ) ≤ x i ∧ x i ≤ (⌊R⌋₊ : ℤ) := by
    intro x hx i
    have hi : |(x i : ℝ)| ≤ R := by
      have hi' : |(x i : ℝ)| ≤ ‖IntegralMinima.toEuclidean x‖ := by
        simpa [IntegralMinima.toEuclidean, Real.norm_eq_abs] using
          PiLp.norm_apply_le (IntegralMinima.toEuclidean x) i
      exact hi'.trans (hnorm x hx)
    have habs : ((x i).natAbs : ℝ) ≤ R := by
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      exact hi
    have hfloor : (x i).natAbs ≤ ⌊R⌋₊ := Nat.le_floor habs
    have hcast : |x i| ≤ (⌊R⌋₊ : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hfloor
    exact abs_le.mp hcast
  have h := card_cube_le S ⌊R⌋₊ q hq hbox hnonzero hspecial
  apply h.trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hR) 3) (by norm_num)

theorem card_shell_le (S : Finset (Fin 3 → ℤ)) (R : ℝ) (hR : 0 ≤ R)
    (q : ℕ) (hq : 0 < q)
    (hnorm : ∀ x ∈ S, ‖IntegralMinima.toEuclidean x‖ < 2 * R)
    (hnonzero : ∀ x ∈ S, ∀ i, x i ≠ 0)
    (hspecial : ∀ x ∈ S, IsSpecial q x) :
    (S.card : ℝ) ≤ 4608 * R ^ 3 / (q : ℝ) ^ 2 := by
  have h := card_ball_le S (2 * R) (by positivity) q hq
    (fun x hx => (hnorm x hx).le) hnonzero hspecial
  convert h using 1; ring

end Problem355.SpecialNormalShell

end OAI
