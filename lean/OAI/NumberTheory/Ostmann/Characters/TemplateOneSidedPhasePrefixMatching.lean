import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseMatching
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePrefix

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
open ParityActions Construction Preliminaries
attribute [local instance] Classical.propDecidable

def wordPrefixEmbedding (k n : ℕ) (width : Role → ℕ) (m : ℕ) (hm : m ≤ width .word) :
    BulkSlot k n m ↪ BulkSlot k n (width .word) where
  toFun z := (z.1,z.2.castLE hm)
  inj' := by
    intro z w h
    apply Prod.ext
    · exact congrArg (fun a : BulkSlot k n (width .word) => a.1) h
    · exact Fin.ext (congrArg (fun a : BulkSlot k n (width .word) => a.2.val) h)

def prefixWordPermutation (k n : ℕ) (width : Role → ℕ) (m : ℕ) (hm : m ≤ width .word)
    (σ : Equiv.Perm (BulkSlot k n m)) : Equiv.Perm (BulkSlot k n (width .word)) :=
  σ.viaEmbedding (wordPrefixEmbedding k n width m hm)

@[simp] theorem prefixWordPermutation_apply (k n : ℕ) (width : Role → ℕ)
    (m : ℕ) (hm : m ≤ width .word) (σ : Equiv.Perm (BulkSlot k n m)) (z : BulkSlot k n m) :
    prefixWordPermutation k n width m hm σ (wordPrefixEmbedding k n width m hm z) =
      wordPrefixEmbedding k n width m hm (σ z) := Equiv.Perm.viaEmbedding_apply _ _ _

theorem prefixWordPermutation_tail (k n : ℕ) (width : Role → ℕ)
    (m : ℕ) (hm : m ≤ width .word) (σ : Equiv.Perm (BulkSlot k n m))
    (z : BulkSlot k n (width .word)) (hz : m ≤ z.2.val) :
    prefixWordPermutation k n width m hm σ z = z := by
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨w,hw⟩
  have he := congrArg (fun a : BulkSlot k n (width .word) => a.2.val) hw
  change w.2.val = z.2.val at he
  exact (not_lt_of_ge hz) (he ▸ w.2.isLt)

def prefixMatchingPermutation (k n : ℕ) (width : Role → ℕ) (m : ℕ) (hm : m ≤ width .word)
    (σ : Equiv.Perm (BulkSlot k n m)) : Equiv.Perm ((schedule k (n+1)).Constituent width) :=
  matchingPermutation k n width (prefixWordPermutation k n width m hm σ)

@[simp] theorem prefixMatchingPermutation_bulk (k n : ℕ) (width : Role → ℕ)
    (m : ℕ) (hm : m ≤ width .word) (σ : Equiv.Perm (BulkSlot k n m)) (z : BulkSlot k n m) :
    prefixMatchingPermutation k n width m hm σ (prefixBulkEmbedding k n width m hm z) =
      prefixBulkEmbedding k n width m hm (σ z) := by
  change matchingPermutation k n width (prefixWordPermutation k n width m hm σ)
    (bulkEmbedding k n width (wordPrefixEmbedding k n width m hm z)) = _
  rw [matchingPermutation_bulk,prefixWordPermutation_apply]
  rfl

theorem prefixMatchingPermutation_tail (k n : ℕ) (width : Role → ℕ)
    (m : ℕ) (hm : m ≤ width .word) (σ : Equiv.Perm (BulkSlot k n m))
    (z : BulkSlot k n (width .word)) (hz : m ≤ z.2.val) :
    prefixMatchingPermutation k n width m hm σ (bulkEmbedding k n width z) = bulkEmbedding k n width z := by
  rw [prefixMatchingPermutation,matchingPermutation_bulk,prefixWordPermutation_tail k n width m hm σ z hz]

theorem prefix_matching_squarePhase_of_original_prior (k n : ℕ) (hn : n+1 ≤ k) (width : Role → ℕ)
    (hw : ∀j : Fin (n+1), ∀big, 0 < width (.anchor j big)) (m : ℕ) (hm : m ≤ width .word)
    (σ ρ : Equiv.Perm (BulkSlot k n m)) (z : BulkSlot k n m)
    (hcode : TemplateDiagonalMatching.bulkCode k (n+1) m (σ z) ≠
      TemplateDiagonalMatching.bulkCode k (n+1) m (ρ z)) {Q V : ℕ}
    (E : (schedule k (n+1)).Constituent width → Finset (PrimeUpTo Q))
    (hE : ∀i,0 < primeShellMass (E i)) (hV : ∀i p,p ∈ E i → V < p.val)
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
      SquarePhase k (n+1) width (prefixMatchingPermutation k n width m hm σ)
        (prefixMatchingPermutation k n width m hm ρ) (fun i => (x i).val) χ a t.val.1 t.val.2 u.val.2
        (prefixBulkEmbedding k n width m hm z) (anchorConstituent k n hn width hw false j b) ∨
      SquarePhase k (n+1) width (prefixMatchingPermutation k n width m hm σ)
        (prefixMatchingPermutation k n width m hm ρ) (fun i => (x i).val) χ a t.val.1 t.val.2 u.val.2
        (anchorConstituent k n hn width hw true j b) (prefixBulkEmbedding k n width m hm z) := by
  apply matching_squarePhase_of_original_prior k n hn width hw
    (prefixWordPermutation k n width m hm σ) (prefixWordPermutation k n width m hm ρ)
    (wordPrefixEmbedding k n width m hm z) _ E hE hV χ hχ a x hx hsupport ranges hrange t u hroot
  rw [prefixWordPermutation_apply k n width m hm σ z,
    prefixWordPermutation_apply k n width m hm ρ z]
  exact hcode

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
