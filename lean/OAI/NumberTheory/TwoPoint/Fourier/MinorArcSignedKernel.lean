import OAI.NumberTheory.TwoPoint.Fourier.MinorArcEnergyKernel
import OAI.NumberTheory.TwoPoint.Fourier.MinorArcVinogradov

namespace OAI

/-! The rational geometric-kernel bound on a symmetric integer range. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma minor_arc_natAbs_fiber (S : Finset ℤ) (k : ℕ) :
    (S.filter (fun n => n.natAbs = k)).card ≤ 2 := by
  have hs : S.filter (fun n => n.natAbs = k) ⊆ {(k : ℤ), -(k : ℤ)} := by
    intro n hn
    have ha : |n| = (k : ℤ) := by
      rw [← Int.natCast_natAbs, (mem_filter.mp hn).2]
    have he : |n| = |(k : ℤ)| := by simpa only [abs_of_nonneg (Int.natCast_nonneg k)] using ha
    rcases abs_eq_abs.mp he with he | he
    · simp only [mem_insert, mem_singleton]
      exact Or.inl he
    · simp only [mem_insert, mem_singleton]
      exact Or.inr he
  exact (card_le_card hs).trans card_le_two

theorem minor_arc_signed_kernel (N q : ℕ) (α V : ℝ) (a : ℤ)
    (hq : 2 ≤ q) (hV : 0 ≤ V) (hcop : IsCoprime (q : ℤ) a)
    (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2) :
    (∑ n ∈ Icc (-(N : ℤ)) (N : ℤ), minorArcGeometricBound V ((n : ℝ) * α)) ≤
      2 * (3 * ((N : ℝ) + 1) / q + 1) *
        (2 * V + 4 * (q : ℝ) * (1 + Real.log (q : ℝ))) := by
  let S := Icc (-(N : ℤ)) (N : ℤ)
  have hmap : ∀ n ∈ S, n.natAbs ∈ range (N + 1) := by
    intro n hn
    have hb : (n.natAbs : ℤ) ≤ (N : ℤ) := by
      rw [Int.natCast_natAbs]
      exact abs_le.mpr (mem_Icc.mp hn)
    have hbN : n.natAbs ≤ N := by exact_mod_cast hb
    exact mem_range.mpr (by omega)
  have he := minor_arc_fiber_sum S (range (N + 1)) Int.natAbs
    (fun n => minorArcGeometricBound V ((n : ℝ) * α)) 2 hmap
    (fun n _ => minor_arc_geometric_nonneg hV _)
    (fun n _ => by
      convert (Nat.cast_le (α := ℝ)).mpr (minor_arc_natAbs_fiber S n) using 1
      apply congrArg (fun T : Finset ℤ => (T.card : ℝ))
      ext z
      simp only [mem_filter])
  have hs : (∑ n ∈ S, minorArcGeometricBound V ((n.natAbs : ℝ) * α)) =
      ∑ n ∈ S, minorArcGeometricBound V ((n : ℝ) * α) :=
    sum_congr rfl (fun n _ => minor_arc_geometric_natAbs V α n)
  rw [hs] at he
  have hv := minor_arc_vinogradov (N + 1) q α V a hq hV hcop happrox
  have htwice := mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ) ≤ 2)
  simp only [Nat.cast_add, Nat.cast_one] at htwice
  exact he.trans (by nlinarith [htwice])

end TwoPointCorrelations

end OAI
