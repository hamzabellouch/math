import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseMatchingGraph
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseTerminal

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
open ParityActions Construction Preliminaries
attribute [local instance] Classical.propDecidable

theorem matching_anchor_bulk_edge (k n : ℕ) (hn : n+1 ≤ k) (width : Role → ℕ)
    (hw : ∀j : Fin (n+1), ∀big, 0 < width (.anchor j big))
    (σ ρ : Equiv.Perm (BulkSlot k n (width .word)))
    (big : Bool) (j : Fin (n+1)) (b : Bool) (z : BulkSlot k n (width .word)) :
    differenceGraph k (n+1) width (matchingPermutation k n width σ) (matchingPermutation k n width ρ)
      (anchorConstituent k n hn width hw big j b) (bulkEmbedding k n width z) =
    graph k (n+1) (retiredAnchors k (n+1) hn big j b).val (σ z).1.val -
      graph k (n+1) (retiredAnchors k (n+1) hn big j b).val (ρ z).1.val := by
  simp only [differenceGraph,permutedGraph]
  simp only [matchingPermutation_anchor k n hn width hw σ big j b,
    matchingPermutation_anchor k n hn width hw ρ big j b,
    matchingPermutation_bulk k n width σ z,matchingPermutation_bulk k n width ρ z]
  rw [constituentGraph_of_fst_ne _ _ _ _ _ (anchorConstituent_fst_ne_bulk k n hn width hw big j b _),
    constituentGraph_of_fst_ne _ _ _ _ _ (anchorConstituent_fst_ne_bulk k n hn width hw big j b _)]
  rfl

theorem matching_bulk_anchor_edge (k n : ℕ) (hn : n+1 ≤ k) (width : Role → ℕ)
    (hw : ∀j : Fin (n+1), ∀big, 0 < width (.anchor j big))
    (σ ρ : Equiv.Perm (BulkSlot k n (width .word)))
    (big : Bool) (j : Fin (n+1)) (b : Bool) (z : BulkSlot k n (width .word)) :
    differenceGraph k (n+1) width (matchingPermutation k n width σ) (matchingPermutation k n width ρ)
      (bulkEmbedding k n width z) (anchorConstituent k n hn width hw big j b) =
    graph k (n+1) (σ z).1.val (retiredAnchors k (n+1) hn big j b).val -
      graph k (n+1) (ρ z).1.val (retiredAnchors k (n+1) hn big j b).val := by
  simp only [differenceGraph,permutedGraph]
  simp only [matchingPermutation_anchor k n hn width hw σ big j b,
    matchingPermutation_anchor k n hn width hw ρ big j b,
    matchingPermutation_bulk k n width σ z,matchingPermutation_bulk k n width ρ z]
  rw [constituentGraph_of_fst_ne _ _ _ _ _ (anchorConstituent_fst_ne_bulk k n hn width hw big j b _).symm,
    constituentGraph_of_fst_ne _ _ _ _ _ (anchorConstituent_fst_ne_bulk k n hn width hw big j b _).symm]
  rfl

theorem matching_squarePhase (k n : ℕ) (hn : n+1 ≤ k) (width : Role → ℕ)
    (hw : ∀j : Fin (n+1), ∀big, 0 < width (.anchor j big))
    (σ ρ : Equiv.Perm (BulkSlot k n (width .word))) (z : BulkSlot k n (width .word))
    (hcode : TemplateDiagonalMatching.bulkCode k (n+1) (width .word) (σ z) ≠
      TemplateDiagonalMatching.bulkCode k (n+1) (width .word) (ρ z))
    (p : (schedule k (n+1)).Constituent width → ℕ) [∀i,Fact (p i).Prime]
    (hc : Pairwise (fun i h => (p i).Coprime (p h)))
    (χ : (q : ℕ) → MulChar (ZMod q) ℂ) (hχ : ∀i,2 < orderOf (χ (p i)))
    (a : (q : ℕ) → ZMod q) (s : ℤ) (t u : HistoryReconstruction.Tree (n+1))
    (ht : ∀i,HistoryFrequencyUnits (p i) (n+1) s t)
    (hu : ∀i,HistoryFrequencyUnits (p i) (n+1) s u) :
    ∃j : Fin (n+1), ∃b : Bool,
      SquarePhase k (n+1) width (matchingPermutation k n width σ) (matchingPermutation k n width ρ)
        p χ a s t u (bulkEmbedding k n width z) (anchorConstituent k n hn width hw false j b) ∨
      SquarePhase k (n+1) width (matchingPermutation k n width σ) (matchingPermutation k n width ρ)
        p χ a s t u (anchorConstituent k n hn width hw true j b) (bulkEmbedding k n width z) := by
  obtain ⟨j,b,h | h⟩ := changed_word_code_edge k (n+1) hn (σ z).1 (ρ z).1 hcode
  · refine ⟨j,b,Or.inl ?_⟩
    apply phasePair_square k (n+1) width _ _ p hc χ hχ a s t u ht hu
    · exact fun he => anchorConstituent_fst_ne_bulk k n hn width hw false j b z (congrArg Sigma.fst he.symm)
    · simpa only [matching_anchor_bulk_edge k n hn width hw σ ρ false j b z] using h.1
    · simpa only [matching_bulk_anchor_edge k n hn width hw σ ρ false j b z] using h.2
  · refine ⟨j,b,Or.inr ?_⟩
    apply phasePair_square k (n+1) width _ _ p hc χ hχ a s t u ht hu
    · exact fun he => anchorConstituent_fst_ne_bulk k n hn width hw true j b z (congrArg Sigma.fst he)
    · simpa only [matching_bulk_anchor_edge k n hn width hw σ ρ true j b z] using h.1
    · simpa only [matching_anchor_bulk_edge k n hn width hw σ ρ true j b z] using h.2

theorem matching_squarePhase_of_original_prior (k n : ℕ) (hn : n+1 ≤ k) (width : Role → ℕ)
    (hw : ∀j : Fin (n+1), ∀big, 0 < width (.anchor j big))
    (σ ρ : Equiv.Perm (BulkSlot k n (width .word))) (z : BulkSlot k n (width .word))
    (hcode : TemplateDiagonalMatching.bulkCode k (n+1) (width .word) (σ z) ≠
      TemplateDiagonalMatching.bulkCode k (n+1) (width .word) (ρ z)) {Q V : ℕ}
    (E : (schedule k (n+1)).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀i,0 < primeShellMass (E i))
    (hV : ∀i p,p ∈ E i → V < p.val)
    (χ : (q : ℕ) → MulChar (ZMod q) ℂ)
    (hχ : ∀i p,p ∈ E i → 2 < orderOf (χ p.val)) (a : (q : ℕ) → ZMod q)
    (x : (schedule k (n+1)).Constituent width → PrimeUpTo Q)
    (hx : (constituentPrimePrior (schedule k (n+1)) width E hE).mass x ≠ 0)
    (hsupport : samplePrimeSupport (schedule k (n+1)) width x)
    (ranges : List Bool → Finset ℤ)
    (hrange : ∀path f,f ∈ ranges path → f ≠ 0 ∧ f.natAbs ≤ V)
    (t u : HistoryFrequencyLabels.SupportedHistory ranges (n+1) []) (hroot : t.val.1 = u.val.1) :
    letI : ∀i,Fact (x i).val.Prime := fun i => ⟨primeUpTo_prime (x i)⟩
    ∃j : Fin (n+1), ∃b : Bool,
      SquarePhase k (n+1) width (matchingPermutation k n width σ) (matchingPermutation k n width ρ)
        (fun i => (x i).val) χ a t.val.1 t.val.2 u.val.2
        (bulkEmbedding k n width z) (anchorConstituent k n hn width hw false j b) ∨
      SquarePhase k (n+1) width (matchingPermutation k n width σ) (matchingPermutation k n width ρ)
        (fun i => (x i).val) χ a t.val.1 t.val.2 u.val.2
        (anchorConstituent k n hn width hw true j b) (bulkEmbedding k n width z) := by
  let : ∀i,Fact (x i).val.Prime := fun i => ⟨primeUpTo_prime (x i)⟩
  refine matching_squarePhase k n hn width hw σ ρ z hcode (fun i => (x i).val) hsupport χ ?_ a
    t.val.1 t.val.2 u.val.2 ?_ ?_
  · intro i
    exact hχ i (x i) (primeProductPrior_mem_of_mass_ne_zero E hE x hx i)
  · intro i
    exact constituentPrimePrior_historyFrequencyUnits (schedule k (n+1)) width E hE hV x hx ranges hrange [] t i
  · intro i
    rw [hroot]
    exact constituentPrimePrior_historyFrequencyUnits (schedule k (n+1)) width E hE hV x hx ranges hrange [] u i

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
