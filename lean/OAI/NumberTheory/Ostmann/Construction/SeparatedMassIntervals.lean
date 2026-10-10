import Mathlib.Data.Finset.Sort
import OAI.NumberTheory.Ostmann.Construction.RichGridShell

namespace OAI

/-! # Three substantial intervals with a full grid cell between them -/

namespace Ostmann

open scoped BigOperators Classical

private theorem three_separated_of_card {q : ℕ} (S : Finset (Fin q)) (hS : 5 ≤ S.card) :
    ∃ i ∈ S, ∃ j ∈ S, ∃ k ∈ S, i.val + 1 < j.val ∧ j.val + 1 < k.val := by
  let f := S.orderEmbOfFin rfl
  let i₀ : Fin S.card := ⟨0, by omega⟩
  let i₁ : Fin S.card := ⟨1, by omega⟩
  let i₂ : Fin S.card := ⟨2, by omega⟩
  let i₃ : Fin S.card := ⟨3, by omega⟩
  let i₄ : Fin S.card := ⟨4, by omega⟩
  have h01 : (f i₀).val < (f i₁).val := f.strictMono (by norm_num [i₀, i₁, i₂, i₃, i₄])
  have h12 : (f i₁).val < (f i₂).val := f.strictMono (by norm_num [i₀, i₁, i₂, i₃, i₄])
  have h23 : (f i₂).val < (f i₃).val := f.strictMono (by norm_num [i₀, i₁, i₂, i₃, i₄])
  have h34 : (f i₃).val < (f i₄).val := f.strictMono (by norm_num [i₀, i₁, i₂, i₃, i₄])
  exact ⟨f i₀, S.orderEmbOfFin_mem rfl i₀, f i₂, S.orderEmbOfFin_mem rfl i₂,
    f i₄, S.orderEmbOfFin_mem rfl i₄, by omega, by omega⟩

theorem three_large_separated_weights {q : ℕ} (hq : 0 < q)
    (w : Fin q → ℝ) (T U : ℝ) (hU : 0 < U)
    (hsum : T ≤ ∑ i, w i) (hcap : ∀ i, w i ≤ U) (hsize : 10 * U ≤ T) :
    ∃ i j k : Fin q, i.val + 1 < j.val ∧ j.val + 1 < k.val ∧
      T / (2 * q) ≤ w i ∧ T / (2 * q) ≤ w j ∧ T / (2 * q) ≤ w k := by
  let θ := T / (2 * q)
  let S := Finset.univ.filter (fun i => θ ≤ w i)
  have hT : 0 < T := lt_of_lt_of_le (by positivity) hsize
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hθ : 0 ≤ θ := by dsimp [θ]; positivity
  have hbad : (∑ i ∈ Finset.univ.filter (fun i => ¬θ ≤ w i), w i) ≤ T / 2 := by
    calc
      _ ≤ ∑ _i ∈ Finset.univ.filter (fun i => ¬θ ≤ w i), θ :=
        Finset.sum_le_sum (fun i hi => (lt_of_not_ge (Finset.mem_filter.mp hi).2).le)
      _ = ((Finset.univ.filter (fun i => ¬θ ≤ w i)).card : ℝ) * θ := by simp
      _ ≤ (q : ℝ) * θ := by
        apply mul_le_mul_of_nonneg_right _ hθ
        have hc := Finset.card_filter_le (s := Finset.univ) (p := fun i : Fin q => ¬θ ≤ w i)
        simp only [Finset.card_univ, Fintype.card_fin] at hc
        exact_mod_cast hc
      _ = T / 2 := by dsimp [θ]; field_simp
  have hgood : T / 2 ≤ ∑ i ∈ S, w i := by
    have h := Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => θ ≤ w i) w
    linarith
  have hgoodcap : (∑ i ∈ S, w i) ≤ S.card * U := by
    calc
      _ ≤ ∑ _i ∈ S, U := Finset.sum_le_sum (fun i _ => hcap i)
      _ = _ := by simp
  have hcard : 5 ≤ S.card := by
    by_contra! h
    have hc : (S.card : ℝ) ≤ 4 := by exact_mod_cast (show S.card ≤ 4 by omega)
    nlinarith
  obtain ⟨i, hi, j, hj, k, hk, hij, hjk⟩ := three_separated_of_card S hcard
  exact ⟨i, j, k, hij, hjk, (Finset.mem_filter.mp hi).2,
    (Finset.mem_filter.mp hj).2, (Finset.mem_filter.mp hk).2⟩

theorem three_separated_mass_intervals (φ : ℝ → ℝ) (q : ℕ) (hq : 0 < q)
    (a L T A : ℝ) (hL : 0 < L) (hA : 0 < A)
    (hmass : T ≤ φ (a + L) - φ a)
    (hupper : ∀ u v, a ≤ u → u ≤ v → v ≤ a + L →
      φ v - φ u ≤ A * (v - u + 1))
    (hsize : 10 * (A * (L / q + 1)) ≤ T) :
    ∃ i j k : Fin q, i.val + 1 < j.val ∧ j.val + 1 < k.val ∧
      ∀ t ∈ ({i, j, k} : Finset (Fin q)),
        T / (2 * q) ≤ φ (a + ((t.val : ℝ) + 1) * (L / q)) -
          φ (a + (t.val : ℝ) * (L / q)) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hh : 0 < L / q := div_pos hL hqR
  let w := fun i : Fin q => φ (a + ((i.val : ℝ) + 1) * (L / q)) -
    φ (a + (i.val : ℝ) * (L / q))
  have hsum : (∑ i, w i) = φ (a + L) - φ a := by
    have h := Finset.sum_range_sub (fun i : ℕ => φ (a + (i : ℝ) * (L / q))) q
    rw [Finset.sum_range] at h
    have he : (q : ℝ) * (L / q) = L := by field_simp
    simpa only [w, Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero, he] using h
  have hcap : ∀ i, w i ≤ A * (L / q + 1) := by
    intro i
    have hi : (i.val : ℝ) + 1 ≤ q := by exact_mod_cast i.isLt
    have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    have hend : a + ((i.val : ℝ) + 1) * (L / q) ≤ a + L := by
      have h := mul_le_mul_of_nonneg_right hi hh.le
      have he : (q : ℝ) * (L / q) = L := by field_simp
      rw [he] at h
      linarith
    have h := hupper (a + (i.val : ℝ) * (L / q))
      (a + ((i.val : ℝ) + 1) * (L / q))
      (le_add_of_nonneg_right (mul_nonneg hi0 hh.le))
      (by nlinarith) hend
    convert h using 1; ring
  obtain ⟨i, j, k, hij, hjk, hi, hj, hk⟩ := three_large_separated_weights hq w T
    (A * (L / q + 1)) (by positivity) (by rwa [hsum]) hcap hsize
  refine ⟨i, j, k, hij, hjk, ?_⟩
  intro t ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  · exact hi
  · exact hj
  · exact hk

end Ostmann

end OAI
