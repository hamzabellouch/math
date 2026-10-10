import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedAdditiveBudget
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedPreparedBounds
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedStructuralBounds
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedFiniteBounds
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedFamilyBounds
import OAI.Combinatorics.LowSpaceSubsetSum.Word.WordSeedBucketExecution

namespace OAI

/-! # Resource bounds for the complete executed word history

The seven stages add their retained seed buffers. Exponents are bounded
only after this addition, so repeated preparation cannot hide storage.
-/

noncomputable section
namespace LowSpaceSubsetSum.WordSeedHistoryBounds

open WordSeedMeasured

variable {n : ℕ}

def workBudget (I : Instance n) := inputScale I^10*2^((n+1)/2)
def liveBudget (I : Instance n) := 3*inputScale I^10*(compressionDictionaryCapacity n+1)

private theorem polynomial_stage {α : Type} [Fintype α] {w N : ℕ}
    {S : SamplerCoupling α} {X : WordSeedRealization.Realization w N S}
    (I : Instance n) (E : Execution X) (k : ℕ) (hk : k ≤ 10)
    (hE : E.Bounded (inputScale I^k) (inputScale I^k) (inputScale I^k)) :
    E.Bounded (workBudget I) (liveBudget I) (liveBudget I) := by
  have hu : 0 < inputScale I := by unfold inputScale; omega
  have hp : inputScale I^k ≤ inputScale I^10 := Nat.pow_le_pow_right hu hk
  have hW := hp.trans (Nat.le_mul_of_pos_right _ (Nat.one_le_two_pow (n := (n+1)/2)))
  have hC := hp.trans (Nat.le_mul_of_pos_right _ (show 0 < compressionDictionaryCapacity n+1 by omega))
  apply bounded_mono E hE hW
  · unfold liveBudget
    exact hC.trans (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (by decide : 0 < 3)))
  · unfold liveBudget
    exact hC.trans (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (by decide : 0 < 3)))

private theorem prepared_stage {α : Type} [Fintype α] {w N : ℕ}
    {S : SamplerCoupling α} {X : WordSeedRealization.Realization w N S}
    (I : Instance n) (E : Execution X)
    (hE : E.Bounded (inputScale I^8*2^((n+1)/2))
      (2*inputScale I^10*(compressionDictionaryCapacity n+1))
      (2*inputScale I^10*(compressionDictionaryCapacity n+1))) :
    E.Bounded (workBudget I) (liveBudget I) (liveBudget I) := by
  apply bounded_mono E hE
  · exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by unfold inputScale; omega) (by decide : 8 ≤ 10))
  · unfold liveBudget
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide : 2 ≤ 3))
  · unfold liveBudget
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide : 2 ≤ 3))

private theorem family_stage {α : Type} [Fintype α] {w N : ℕ}
    {S : SamplerCoupling α} {X : WordSeedRealization.Realization w N S}
    (I : Instance n) (E : Execution X)
    (hE : E.Bounded (inputScale I^9*2^((n+1)/2))
      (inputScale I^9*(compressionDictionaryCapacity n+1))
      (inputScale I^9*(compressionDictionaryCapacity n+1))) :
    E.Bounded (workBudget I) (liveBudget I) (liveBudget I) := by
  have hp : inputScale I^9 ≤ inputScale I^10 := Nat.pow_le_pow_right (by unfold inputScale; omega) (by decide)
  have hc := Nat.mul_le_mul_right (compressionDictionaryCapacity n+1) hp
  apply bounded_mono E hE (Nat.mul_le_mul_right _ hp)
  · unfold liveBudget
    exact hc.trans (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (by decide : 0 < 3)))
  · unfold liveBudget
    exact hc.trans (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (by decide : 0 < 3)))

theorem residues_bounded_scale (I : Instance n) (hn : 10000 ≤ n)
    (R : RepresentationSetup n) {z : RepresentationSetup.Layout n} (p : R.PrimeSpace z)
    (w : ℕ) (hw : 3*n ≤ w) :
    (residues R (by omega) p w hw).Bounded (inputScale I^6) (inputScale I^6) (inputScale I^6) := by
  let : NeZero (prefixModulus p.val 0) := ⟨(prefixModulus_pos p 0).ne'⟩
  let : NeZero (prefixModulus p.val 1) := ⟨(prefixModulus_pos p 1).ne'⟩
  let : NeZero (prefixModulus p.val 2) := ⟨(prefixModulus_pos p 2).ne'⟩
  have h (i : Fin 3) : Nat.clog 2 (prefixModulus p.val i) ≤ 3*n :=
    Nat.clog_le_of_le_pow (RepresentationScalarBounds.prefix_bound R (by omega) z p i)
  have hi (i : Fin 3) := by
    letI : NeZero (prefixModulus p.val i) := ⟨(prefixModulus_pos p i).ne'⟩
    exact WordSeedScalarBounds.fin_bounded_scale I hn (prefixModulus p.val i)
      (h i) w ((h i).trans hw)
  have h12 := prod_bounded _ _ _ _ _ _ _ _ (hi 1) (hi 2)
  have h012 := prod_bounded _ _ _ _ _ _ _ _ (hi 0) h12
  have hall := prepareThen_bounded (fun _ => (((),6),8)) _ _ _ _ _ _
    (le_refl 6) (le_refl 8) (fun _ => h012)
  let u := inputScale I
  have hu : 10000 ≤ u := by unfold u inputScale; omega
  have hup : u ≤ u^5 := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < u) (by decide : 1 ≤ 5)
  have hs : 10*u^5 ≤ u^6 := by
    calc
      _ ≤ u*u^5 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  intro stream cursor
  have ht := hall stream cursor
  dsimp only [u] at hs hup hu
  change _ ≤ inputScale I^6 ∧ _ ≤ inputScale I^6 ∧ _ ≤ inputScale I^6
  exact ⟨ht.1.trans (by omega),ht.2.1.trans (by omega),ht.2.2.trans (by omega)⟩

theorem guessHistory_budget (I : Instance n) (hn : 10000 ≤ n) (w : ℕ) (hw : n+1 ≤ w) :
    Budgeted (guessHistory I w hw) (workBudget I) (liveBudget I) 2 := by
  unfold guessHistory
  apply budgeted_bind
  · apply budgeted_one
    exact polynomial_stage I _ 6 (by decide)
      (WordSeedStructuralBounds.layout_bounded_scale I hn _ _ _ _)
  · intro a
    exact polynomial_stage I _ 6 (by decide)
      (WordSeedStructuralBounds.guesses_bounded_scale I hn _ _ _)

theorem partitionHistory_budget (I : Instance n) (hn : 10000 ≤ n) (w : ℕ) (hw : n+1 ≤ w) :
    Budgeted (partitionHistory I w hw) (workBudget I) (liveBudget I) 3 := by
  unfold partitionHistory
  apply budgeted_bind
  · exact guessHistory_budget I hn w hw
  · intro a
    exact polynomial_stage I _ 7 (by decide)
      (WordSeedStructuralBounds.partitions_bounded_scale I hn _ _ _ _)

theorem primeHistory_budget (I : Instance n) (hn : 10000 ≤ n) (w : ℕ) (hw : n+1 ≤ w) :
    Budgeted (primeHistory I w hw) (workBudget I) (liveBudget I) 4 := by
  unfold primeHistory
  apply budgeted_bindSeed
  · exact partitionHistory_budget I hn w hw
  · intro a
    exact prepared_stage I _ (nestedPrepared_bounded I hn _ _ _)

theorem trialHistory_budget (I : Instance n) (hn : 10000 ≤ n) (w : ℕ) (hw : 3*n+1 ≤ w) :
    Budgeted (trialHistory I (by omega) w hw) (workBudget I) (liveBudget I) 5 := by
  unfold trialHistory
  apply budgeted_bind
  · exact primeHistory_budget I hn w (by omega)
  · intro a
    exact polynomial_stage I _ 6 (by decide) (residues_bounded_scale I hn _ _ _ _)

theorem extraHistory_budget (I : Instance n) (hn : 10000 ≤ n) (w : ℕ) (hw : 3*n+1 ≤ w) :
    Budgeted (extraHistory I (by omega) w hw) (workBudget I) (liveBudget I) 6 := by
  unfold extraHistory
  apply budgeted_bindSeed
  · exact trialHistory_budget I hn w hw
  · intro a
    exact prepared_stage I _ (extraPrepared_bounded I hn _ _ _)

theorem separatorDraws_stage (I : Instance n) (hn : 10000 ≤ n) (R : RepresentationSetup n)
    (h : R.PrimeHistory) (w : ℕ) (hw : Nat.clog 2 (2*RepresentationSetup.blockHalf n 0) ≤ w) :
    (separatorDraws R h (by omega) w hw).Bounded (workBudget I) (liveBudget I) (liveBudget I) := by
  unfold separatorDraws
  apply family_stage
  exact WordSeedFamilyBounds.familiesPrepared_application I hn _ _ _
    (WordSamplingBounds.family_width n) _ _ _ _ w hw
    (WordSeedFamilyBounds.canonical_family_codes n) (WordSeedFamilyBounds.canonical_family_half n)

theorem bucketHistory_budget (I : Instance n) (hn : 10000 ≤ n) (w : ℕ) (hw : 3*n+1 ≤ w) :
    Budgeted (bucketHistory I hn w hw) (workBudget I) (liveBudget I) 7 := by
  unfold bucketHistory
  apply budgeted_bind
  · exact extraHistory_budget I hn w hw
  · intro a
    exact separatorDraws_stage I hn _ _ _ _

theorem bucketHistory_bounded (I : Instance n) (hn : 10000 ≤ n) (w : ℕ) (hw : 3*n+1 ≤ w) :
    (bucketHistory I hn w hw).Bounded (inputScale I^11*2^((n+1)/2))
      (inputScale I^11*(compressionDictionaryCapacity n+1))
      (inputScale I^11*(compressionDictionaryCapacity n+1)) := by
  have h := bucketHistory_budget I hn w hw
  let u := inputScale I
  let C := compressionDictionaryCapacity n+1
  let H := 2^((n+1)/2)
  have hu : 10000 ≤ u := by unfold u inputScale; omega
  have hC : 1 ≤ C := by unfold C; omega
  have hH : 1 ≤ H := Nat.one_le_two_pow
  have hp : u ≤ u^10 := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < u) (by decide : 1 ≤ 10)
  have hmc := Nat.le_mul_of_pos_right (u^10) hC
  have hmh := Nat.le_mul_of_pos_right (u^10) hH
  have hc : 22*u^10*C ≤ u^11*C := by
    calc
      _ ≤ u*u^10*C := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
      _ = _ := by ring
  have ht : 8*u^10*H ≤ u^11*H := by
    calc
      _ ≤ u*u^10*H := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
      _ = _ := by ring
  apply bounded_mono _ h
  · change 7*(u^10*H+2) ≤ u^11*H
    nlinarith only [ht,hmh,hp,hu]
  · change 7*(3*u^10*C+8) ≤ u^11*C
    nlinarith only [hc,hmc,hp,hu]
  · change 7*(3*u^10*C+8) ≤ u^11*C
    nlinarith only [hc,hmc,hp,hu]

end LowSpaceSubsetSum.WordSeedHistoryBounds

end

end OAI
