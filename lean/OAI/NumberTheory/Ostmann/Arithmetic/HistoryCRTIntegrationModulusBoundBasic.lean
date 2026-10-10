import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTIntegrationModuli
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulusBoundSize
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulusCost

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators Classical
namespace Ostmann.Arithmetic.HistoryCRTIntegration
open Construction HistorySignedResidues HistoryOccurrenceVariables HistoryPairRows
open HistoryPairRepresentatives

lemma factorBound_root {N : ℕ} {B : ℝ} {l : ℕ} (h : History l)
    (hb : factorBound N B h) :
    h.root.small.length≤N ∧ ∀q∈h.root.small,(q.value:ℝ)≤B := by
  cases h with
  | leaf a => exact hb.2
  | node a p u hp hm left right => exact ⟨hb.2.1,hb.2.2.1⟩

lemma factorBound_internalSlot {N : ℕ} {B : ℝ} {l : ℕ} (h : History l)
    (hb : factorBound N B h) : ∀i : InternalKey h,(internalSlot h i).value≤B := by
  induction h with
  | leaf a => exact fun i => isEmptyElim i
  | node a p u hp hm left right il ir =>
    intro i
    rcases i with i | i
    · exact hb.2.2.2.2.1 _ (List.get_mem u i)
    · rcases i with i | i
      · exact il hb.2.2.2.2.2.1 i
      · exact ir hb.2.2.2.2.2.2 i

lemma internal_card_le_divisorCost {l : ℕ} (h : History l) :
    Fintype.card (InternalKey h)≤divisorCost h := by
  induction h with
  | leaf a => simp [InternalKey,divisorCost]
  | node a p u hp hm left right il ir =>
    simp only [InternalKey,Fintype.card_sum,Fintype.card_fin,divisorCost]
    omega

lemma representative_card_le {level : ℕ} (h g : History level) :
    Fintype.card (Representative h g)≤divisorCost h+divisorCost g := by
  have hc := Fintype.card_le_of_surjective (label h g) (label_surjective h g)
  have hi := Nat.add_le_add (internal_card_le_divisorCost h) (internal_card_le_divisorCost g)
  exact hc.trans (by simpa only [Occurrences,Fintype.card_sum] using hi)

lemma representative_prime_le {N : ℕ} {B : ℝ} {level : ℕ} (h g : History level)
    (hh : factorBound N B h) (hg : factorBound N B g) (r : Representative h g) :
    (prime h g r:ℝ)≤B := by
  obtain ⟨i,rfl⟩ := label_surjective h g r
  rw [prime_label]
  rcases i with i | i
  · exact factorBound_internalSlot h hh i
  · exact factorBound_internalSlot g hg i

lemma rootModulus_le {N : ℕ} {B : ℝ} {level : ℕ} (hB : 1≤B) (h : History level)
    (hh : factorBound N B h) : (rootModulus h:ℝ)≤B^N := by
  have hr := factorBound_root h hh
  have hp := smallProduct_intSize_le (le_trans (by norm_num) hB) h.root.small hr.2
  have hp' : (rootModulus h:ℝ)≤B^h.root.small.length := by
    change |(rootModulus h:ℝ)|≤B^h.root.small.length at hp
    exact (abs_le.mp hp).2
  exact hp'.trans (pow_le_pow_right₀ hB hr.1)

lemma outsideModulus_le {N : ℕ} {B : ℝ} (hB : 1≤B) (outside : List ℕ)
    (hlen : outside.length≤N) (hout : ∀q∈outside,(q:ℝ)≤B) :
    (outsideModulus outside:ℝ)≤B^N := by
  have hp := natProduct_intSize_le (le_trans (by norm_num) hB) outside hout
  have hp' : (outsideModulus outside:ℝ)≤B^outside.length := by
    change |(outsideModulus outside:ℝ)|≤B^outside.length at hp
    exact (abs_le.mp hp).2
  exact hp'.trans (pow_le_pow_right₀ hB hlen)

lemma representativeModulus_le {N : ℕ} {B : ℝ} {level : ℕ} (hB : 1≤B) (h g : History level)
    (hh : factorBound N B h) (hg : factorBound N B g) :
    (representativeModulus h g:ℝ)≤B^(2*(divisorCost h+divisorCost g)) := by
  have hb : 0≤B := le_trans (by norm_num) hB
  calc
    _ = ∏r : Representative h g,(prime h g r:ℝ)^2 := by
      simp only [representativeModulus,Nat.cast_prod,Nat.cast_pow]
    _ ≤ ∏_r : Representative h g,B^2 := by
      apply Finset.prod_le_prod₀
      · intro r hr; positivity
      · intro r hr
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) (representative_prime_le h g hh hg r) 2
    _ = B^(2*Fintype.card (Representative h g)) := by simp [pow_mul]
    _ ≤ _ := pow_le_pow_right₀ hB (Nat.mul_le_mul_left 2 (representative_card_le h g))

end Ostmann.Arithmetic.HistoryCRTIntegration

end

end OAI
