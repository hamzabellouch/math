import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import OAI.NumberTheory.Ostmann.QuadraticSieve.PublishedQuadraticSieve

namespace OAI

/-! # A concrete four-piece cover of the signed squarefree integers -/

namespace Ostmann

open scoped BigOperators Classical

def signedSquarefreeRange (M : ℕ) : Finset ℤ :=
  (Finset.Icc (-(M : ℤ)) M).filter fun u => u ≠ 0 ∧ Squarefree u.natAbs

def quadraticSigns : Finset ℤ := {1, -1, 2, -2}

theorem signedSquarefreeRange_cover {M : ℕ} {u : ℤ}
    (hu : u ∈ signedSquarefreeRange M) :
    ∃ d ∈ quadraticSigns, ∃ v ∈ oddSquarefreeRange M, d * (v : ℤ) = u := by
  obtain ⟨huI, hu0, hsf⟩ := Finset.mem_filter.mp hu
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp huI
  have hn0 : 0 < u.natAbs := Int.natAbs_pos.mpr hu0
  have hnM : u.natAbs ≤ M := by
    have : (u.natAbs : ℤ) ≤ M := by rw [Int.natCast_natAbs]; exact abs_le.mpr ⟨hlo, hhi⟩
    exact_mod_cast this
  have hsign : (u.natAbs : ℤ) = u ∨ -(u.natAbs : ℤ) = u := by
    rw [Int.natCast_natAbs]
    rcases le_total 0 u with hp | hn
    · exact Or.inl (abs_of_nonneg hp)
    · exact Or.inr (by rw [abs_of_nonpos hn, neg_neg])
  by_cases ho : Odd u.natAbs
  · have hv : u.natAbs ∈ oddSquarefreeRange M :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn0, hnM⟩, ho, hsf⟩
    rcases hsign with hp | hn
    · exact ⟨1, by simp [quadraticSigns], u.natAbs, hv, by simpa using hp⟩
    · exact ⟨-1, by simp [quadraticSigns], u.natAbs, hv, by simpa using hn⟩
  · have he : 2 ∣ u.natAbs := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp ho)
    obtain ⟨v, hv⟩ := he
    have hsfv : Squarefree (2 * v) := hv ▸ hsf
    have hov : Odd v := Nat.coprime_two_left.mp (Nat.coprime_of_squarefree_mul hsfv)
    have hvM : v ∈ oddSquarefreeRange M := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hov, hsfv.of_mul_right⟩ <;>
        omega
    have hcast : (u.natAbs : ℤ) = 2 * v := by exact_mod_cast hv
    rcases hsign with hp | hn
    · exact ⟨2, by simp [quadraticSigns], v, hvM, by rw [← hcast, hp]⟩
    · exact ⟨-2, by simp [quadraticSigns], v, hvM, by rw [show (-2 : ℤ) * v = -(2 * v) by ring, ← hcast, hn]⟩

theorem sum_signedSquarefreeRange_le (M : ℕ) (f : ℤ → ℝ) (hf : ∀ u, 0 ≤ f u) :
    (∑ u ∈ signedSquarefreeRange M, f u) ≤
      ∑ d ∈ quadraticSigns, ∑ v ∈ oddSquarefreeRange M, f (d * v) := by
  let S := quadraticSigns.product (oddSquarefreeRange M)
  let g : ℤ × ℕ → ℤ := fun z => z.1 * z.2
  have hsub : signedSquarefreeRange M ⊆ S.image g := by
    intro u hu
    obtain ⟨d, hd, v, hv, h⟩ := signedSquarefreeRange_cover hu
    exact Finset.mem_image.mpr ⟨(d, v), Finset.mem_product.mpr ⟨hd, hv⟩, h⟩
  calc
    _ ≤ ∑ u ∈ S.image g, f u := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun u _ _ => hf u)
    _ ≤ ∑ z ∈ S, f (g z) := Finset.sum_image_le_of_nonneg (fun z _ => hf z)
    _ = _ := by simp [S, g, Finset.sum_product]

end Ostmann

end OAI
