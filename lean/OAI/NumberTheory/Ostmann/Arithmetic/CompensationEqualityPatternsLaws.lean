import OAI.NumberTheory.Ostmann.Arithmetic.CompensationEqualityPatternsSources

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.CompensationEqualityPatterns
open Construction
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem source_block_mass_nonneg (sources : SourceFamily) (origin τ : ι → ℕ)
    (p : Pattern τ) (b : BlockDraw p (CommonSample sources origin)) :
    0 ≤ ∏ q : Block p, blockWeight p (sourceWeight sources origin) q (b.val q) := by
  apply Finset.prod_nonneg
  intro q _
  apply Finset.prod_nonneg
  intro i _
  exact sourceWeight_nonneg sources origin i.val (b.val q)

theorem source_block_mass_total (sources : SourceFamily) (origin τ : ι → ℕ) :
    (∑ p : Pattern τ, ∑ b : BlockDraw p (CommonSample sources origin),
      ∏ q : Block p, blockWeight p (sourceWeight sources origin) q (b.val q)) = 1 := by
  have h := source_cmean_eq_patterns sources origin τ (fun _ => (1 : ℂ))
  have hleft : (dependentProductPrior (fun i => (sources (origin i)).law)).cmean
      (fun _ => (1 : ℂ)) = 1 := by
    simp only [FinitePrior.cmean, mul_one, ← Complex.ofReal_sum,
      FinitePrior.mass_total, Complex.ofReal_one]
  rw [hleft] at h
  simpa [← Complex.ofReal_prod] using congrArg Complex.re h.symm

omit [DecidableEq ι] in
theorem source_supported_of_product_ne_zero (sources : SourceFamily) (origin : ι → ℕ)
    (w : ι → CommonSample sources origin)
    (hw : (∏ i, sourceWeight sources origin i (w i)) ≠ 0) :
    ∀ i, (w i).val ∈ (sources (origin i)).candidates := by
  intro i
  by_contra hi
  exact hw (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [sourceWeight, hi]))

omit [DecidableEq ι] in
theorem source_block_values_injective (sources : SourceFamily) (origin τ : ι → ℕ)
    (hdisjoint : ∀ i j, τ i ≠ τ j →
      Disjoint (sources (origin i)).candidates (sources (origin j)).candidates)
    (p : Pattern τ) (b : BlockDraw p (CommonSample sources origin))
    (hb : (∏ q : Block p, blockWeight p (sourceWeight sources origin) q (b.val q)) ≠ 0) :
    Function.Injective (fun q : Block p => (b.val q).val) := by
  have he := product_weights_by_blocks p (sourceWeight sources origin) b
  have hs := source_supported_of_product_ne_zero sources origin (expand p b)
    (fun hz => hb (he.symm.trans hz))
  intro q r h
  obtain ⟨i, rfl⟩ := label_surjective p q
  obtain ⟨j, rfl⟩ := label_surjective p r
  apply b.property
  apply Prod.ext
  · change τ i = τ j
    by_contra ht
    apply Finset.disjoint_left.mp (hdisjoint i j ht) (hs i)
    change (b.val (label p i)).val ∈ (sources (origin j)).candidates
    exact (congrArg (fun n : ℕ => n ∈ (sources (origin j)).candidates) h).mpr (hs j)
  · exact Subtype.ext h

end Ostmann.Arithmetic.CompensationEqualityPatterns

end

end OAI
