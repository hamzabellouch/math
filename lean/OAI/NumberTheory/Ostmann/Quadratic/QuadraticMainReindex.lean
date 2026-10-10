import OAI.NumberTheory.Ostmann.Quadratic.QuadraticMainExpansion
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallKernels

namespace OAI

/-! # Reindexing the main-term difference by its square part -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadraticMainGamma_reindex {D K : ℕ} (hD : Squarefree D) (hDo : Odd D)
    (F : ℕ → ℂ) :
    (∑ w ∈ Finset.Icc 1 (K * D ^ 2), (quadraticMainGamma D K w : ℂ) * F w) =
      ∑ s ∈ D.divisors, ∑ r ∈ oddSquarefreeRange (K * D ^ 2),
        (quadraticMainGamma D K (s ^ 2 * r) : ℂ) * F (s ^ 2 * r) := by
  let H := K * D ^ 2
  let W := (Finset.Icc 1 H).filter (fun w => quadraticMainGamma D K w ≠ 0)
  let P := (D.divisors.product (oddSquarefreeRange H)).filter
    (fun z => quadraticMainGamma D K (z.1 ^ 2 * z.2) ≠ 0)
  have hleft : (∑ w ∈ Finset.Icc 1 H, (quadraticMainGamma D K w : ℂ) * F w) =
      ∑ w ∈ W, (quadraticMainGamma D K w : ℂ) * F w := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro w hw hn
    have hz : quadraticMainGamma D K w = 0 := by
      by_contra hz
      exact hn (Finset.mem_filter.mpr ⟨hw, hz⟩)
    simp [hz]
  have hright : (∑ z ∈ P, (quadraticMainGamma D K (z.1 ^ 2 * z.2) : ℂ) *
      F (z.1 ^ 2 * z.2)) =
      ∑ s ∈ D.divisors, ∑ r ∈ oddSquarefreeRange H,
        (quadraticMainGamma D K (s ^ 2 * r) : ℂ) * F (s ^ 2 * r) := by
    calc
      _ = ∑ z ∈ D.divisors.product (oddSquarefreeRange H),
          (quadraticMainGamma D K (z.1 ^ 2 * z.2) : ℂ) * F (z.1 ^ 2 * z.2) := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro z hz hn
        have hzero : quadraticMainGamma D K (z.1 ^ 2 * z.2) = 0 := by
          by_contra hzero
          exact hn (Finset.mem_filter.mpr ⟨hz, hzero⟩)
        simp [hzero]
      _ = _ := Finset.sum_product _ _ _
  change (∑ w ∈ Finset.Icc 1 H, _) = _
  rw [hleft, ← hright]
  symm
  apply Finset.sum_bij (fun z _ => z.1 ^ 2 * z.2)
  · intro z hz
    obtain ⟨hz, hnonzero⟩ := Finset.mem_filter.mp hz
    obtain ⟨hbig, hbound, _, _⟩ := quadraticMainGamma_support hD hDo hnonzero
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hbound⟩, hnonzero⟩
  · intro z hz y hy heq
    obtain ⟨hz, _⟩ := Finset.mem_filter.mp hz
    obtain ⟨hy, _⟩ := Finset.mem_filter.mp hy
    obtain ⟨hzs, hzr⟩ := Finset.mem_product.mp hz
    obtain ⟨hys, hyr⟩ := Finset.mem_product.mp hy
    have hh := quadratic_squarefree_factor_unique (Nat.pos_of_mem_divisors hzs).ne'
      (Nat.pos_of_mem_divisors hys).ne' (Finset.mem_filter.mp hzr).2.2
      (Finset.mem_filter.mp hyr).2.2 heq
    exact Prod.ext hh.1 hh.2
  · intro w hw
    obtain ⟨hwr, hnonzero⟩ := Finset.mem_filter.mp hw
    obtain ⟨_, _, hodd, hroot⟩ := quadraticMainGamma_support hD hDo hnonzero
    have hwpos := (Finset.mem_Icc.mp hwr).1
    refine ⟨(quadraticSquarePart w, quadraticSquarefreePart w), ?_, quadraticSquarePart_factor w⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Nat.mem_divisors.mpr ⟨hroot, hD.ne_zero⟩, ?_⟩, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_Icc.mpr ⟨quadraticSquarefreePart_pos w, ?_⟩,
        hodd.of_dvd_nat (quadraticSquarefreePart_dvd w), quadraticSquarefreePart_squarefree w⟩
      exact (Nat.le_of_dvd hwpos (quadraticSquarefreePart_dvd w)).trans
        (Finset.mem_Icc.mp hwr).2
    · simpa only [quadraticSquarePart_factor] using hnonzero
  · intro _ _
    rfl

end Ostmann

end OAI
