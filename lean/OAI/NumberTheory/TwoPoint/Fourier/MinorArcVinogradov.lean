import OAI.NumberTheory.TwoPoint.Fourier.MinorArcSeparatedKernel

namespace OAI

/-! The finite Vinogradov bound obtained by partitioning an integer range
into blocks shorter than half the rational denominator. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma minor_arc_nat_rational_block (S : Finset ℕ) (α : ℝ) (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hcop : IsCoprime (q : ℤ) a) (V : ℝ) (hV : 0 ≤ V)
    (hwidth : ∀ m ∈ S, ∀ n ∈ S, |(m : ℝ) - n| ≤ (q : ℝ) / 2)
    (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2) :
    (∑ n ∈ S, minorArcGeometricBound V ((n : ℝ) * α)) ≤
      2 * V + 4 * (q : ℝ) * (1 + Real.log (q : ℝ)) := by
  let e : ℕ ↪ ℤ := ⟨Nat.cast, Nat.cast_injective⟩
  have hb := minor_arc_rational_block (S.map e) α a (q : ℤ)
    (by exact_mod_cast hq) hcop V hV ?_ (by simpa using happrox)
  · simpa only [sum_map, e, Function.Embedding.coeFn_mk, Int.cast_natCast] using hb
  · intro m hm n hn
    obtain ⟨m', hm', rfl⟩ := mem_map.mp hm
    obtain ⟨n', hn', rfl⟩ := mem_map.mp hn
    simpa only [e, Function.Embedding.coeFn_mk, Int.cast_sub, Int.cast_natCast] using
      hwidth m' hm' n' hn'

theorem minor_arc_vinogradov (N q : ℕ) (α V : ℝ) (a : ℤ)
    (hq : 2 ≤ q) (hV : 0 ≤ V) (hcop : IsCoprime (q : ℤ) a)
    (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2) :
    (∑ n ∈ range N, minorArcGeometricBound V ((n : ℝ) * α)) ≤
      (3 * (N : ℝ) / q + 1) * (2 * V + 4 * (q : ℝ) * (1 + Real.log (q : ℝ))) := by
  let L := q / 2
  let J := N / L + 1
  let S := fun j : ℕ => (range N).filter (fun n => n / L = j)
  have hL : 0 < L := Nat.div_pos hq (by norm_num)
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hqr : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hLq : (L : ℝ) ≤ (q : ℝ) / 2 := by
    exact Nat.cast_div_le
  have hblock (j : ℕ) : (∑ n ∈ S j, minorArcGeometricBound V ((n : ℝ) * α)) ≤
      2 * V + 4 * (q : ℝ) * (1 + Real.log (q : ℝ)) := by
    apply minor_arc_nat_rational_block (S j) α a q (by omega) hcop V hV ?_ happrox
    intro m hm n hn
    have hmj : m / L = j := (mem_filter.mp hm).2
    have hnj : n / L = j := (mem_filter.mp hn).2
    have hmlo : j * L ≤ m := by simpa only [hmj] using Nat.div_mul_le_self m L
    have hnlo : j * L ≤ n := by simpa only [hnj] using Nat.div_mul_le_self n L
    have hmhi : m < L * (j + 1) := by simpa only [hmj] using Nat.lt_mul_div_succ m hL
    have hnhi : n < L * (j + 1) := by simpa only [hnj] using Nat.lt_mul_div_succ n hL
    have hmi : (j : ℝ) * L ≤ m := by exact_mod_cast hmlo
    have hni : (j : ℝ) * L ≤ n := by exact_mod_cast hnlo
    have hma : (m : ℝ) < L * ((j : ℝ) + 1) := by exact_mod_cast hmhi
    have hna : (n : ℝ) < L * ((j : ℝ) + 1) := by exact_mod_cast hnhi
    apply (le_of_lt (abs_lt.mpr ⟨?_, ?_⟩)).trans hLq <;> nlinarith
  have hpart : (∑ n ∈ range N, minorArcGeometricBound V ((n : ℝ) * α)) =
      ∑ j ∈ range J, ∑ n ∈ S j, minorArcGeometricBound V ((n : ℝ) * α) := by
    symm
    apply sum_fiberwise_of_maps_to
    intro n hn
    apply mem_range.mpr
    have hle : n / L ≤ N / L := Nat.div_le_div_right (mem_range.mp hn).le
    omega
  have hqL : (q : ℝ) ≤ 3 * (L : ℝ) := by
    have hmod := Nat.mod_lt q (by norm_num : 0 < 2)
    have hid := Nat.mod_add_div q 2
    have hqq : q ≤ 3 * L := by dsimp [L] at *; omega
    exact_mod_cast hqq
  have hJ : (J : ℝ) ≤ 3 * (N : ℝ) / q + 1 := by
    have hquot : (N : ℝ) / L ≤ 3 * (N : ℝ) / q := by
      apply (div_le_div_iff₀ hLr hqr).mpr
      nlinarith [mul_le_mul_of_nonneg_left hqL (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    calc
      _ = ((N / L : ℕ) : ℝ) + 1 := by simp [J]
      _ ≤ (N : ℝ) / L + 1 := add_le_add Nat.cast_div_le le_rfl
      _ ≤ _ := by linarith
  have hconstant : 0 ≤ 2 * V + 4 * (q : ℝ) * (1 + Real.log (q : ℝ)) := by
    have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
    positivity
  rw [hpart]
  calc
    _ ≤ ∑ _j ∈ range J, (2 * V + 4 * (q : ℝ) * (1 + Real.log (q : ℝ))) :=
      sum_le_sum (fun j _ => hblock j)
    _ = (J : ℝ) * (2 * V + 4 * (q : ℝ) * (1 + Real.log (q : ℝ))) := by
      simp only [sum_const, card_range, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hJ hconstant

end TwoPointCorrelations

end OAI
