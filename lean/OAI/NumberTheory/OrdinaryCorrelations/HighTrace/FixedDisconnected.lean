import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SpecPrimeSlot
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ActiveComponents

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

def fixedDisconnected (w : ClosedLine h ℓ) (hh : 0 < h) (a : S.FixedResidues w)
    (p : S.Index) : Prop :=
  (treeOccurrences w p).Nonempty ∧ ∃ hp : S.IsFixed w p, ¬ ActiveConnected w hh p (a ⟨p,hp⟩)

def fixedUnlitCount (w : ClosedLine h ℓ) (a : S.FixedResidues w) (p : S.Index) : ℕ :=
  if hp : S.IsFixed w p then (unlitOccurrences w p (a ⟨p,hp⟩)).card else 0

def totalUnlitCount (w : ClosedLine h ℓ) (a : S.FixedResidues w) : ℕ :=
  ∑ p : S.Index, fixedUnlitCount w a p

def disconnectedCount (w : ClosedLine h ℓ) (hh : 0 < h) (a : S.FixedResidues w) : ℕ :=
  (univ.filter (fixedDisconnected w hh a)).card

def corruptedCount (S : PrimeSystem) (w : ClosedLine h ℓ) : ℕ := (univ.filter (freeCorrupted (S:=S) w)).card

lemma tagged_local_card_bound (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (K : ℕ)
    (hK : ∀ p : S.FixedIndex w, (treeOccurrences w p.val).Nonempty →
      (activeComponents w hh p.val (a p)).card ≤ K) (p : S.Index) :
    (taggedTokens w hh 𝔏 (recordAt w hh 𝔏 a) p).card ≤
      (if fixedDisconnected w hh a p then K else 0) + 2*fixedUnlitCount w a p +
      (if freeCorrupted w p then 1 else 0) +
      (if (p:ℕ) ∈ listSupport w 𝔏 then 1 else 0) := by
  by_cases hf : S.IsFixed w p
  · by_cases ho : (treeOccurrences w p).Nonempty
    · have he : fixedDisconnected w hh a p ↔ ¬ActiveConnected w hh p (a ⟨p,hf⟩) := by
        simp only [fixedDisconnected,ho,true_and]
        exact ⟨fun h => h.choose_spec,fun h => ⟨hf,h⟩⟩
      have hcor : ¬freeCorrupted w p := fun h => h.1 hf
      simpa only [he,hcor,ite_false,add_zero,fixedUnlitCount,dite_eq_left hf] using
        tagged_fixed_card w hh 𝔏 a ⟨p,hf⟩ K (hK ⟨p,hf⟩)
    · simp only [taggedTokens,recordTokens,ho,ite_false,filter_empty,card_empty]
      exact Nat.zero_le _
  · have hd : ¬fixedDisconnected w hh a p := fun h => hf h.2.choose
    simpa only [hd,ite_false,fixedUnlitCount,dite_eq_right hf,mul_zero,zero_add] using
      tagged_free_card w hh 𝔏 a p hf

lemma listed_prime_count (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L)) :
    (univ.filter (fun p : S.Index => (p:ℕ) ∈ listSupport w 𝔏)).card ≤
      Fintype.card (ListPrimeSlot w 𝔏) := by
  have he : univ.filter (fun p : S.Index => (p:ℕ) ∈ listSupport w 𝔏) =
      univ.image (listSlotPrime w 𝔏) := by
    ext p
    simp only [mem_filter,mem_univ,true_and,mem_image]
    exact (listSupport_iff_slot w 𝔏 p).trans (by simp)
  rw [he]
  exact card_image_le.trans (by rw [card_univ])

theorem retained_tag_count (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (a : S.FixedResidues w) (K : ℕ)
    (hK : ∀ p : S.FixedIndex w, (treeOccurrences w p.val).Nonempty →
      (activeComponents w hh p.val (a p)).card ≤ K) :
    Fintype.card (TaggedSlot w hh 𝔏 a) ≤
      disconnectedCount w hh a*K + 2*totalUnlitCount w a + corruptedCount S w +
      Fintype.card (ListPrimeSlot w 𝔏) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_coe]
  have hs := sum_le_sum (fun p (_ : p ∈ (univ : Finset S.Index)) =>
    tagged_local_card_bound w hh 𝔏 a K hK p)
  simp only [sum_add_distrib,← mul_sum] at hs
  have hk : (∑ p : S.Index, if fixedDisconnected w hh a p then K else 0) =
      disconnectedCount w hh a*K := by simp [←sum_filter,disconnectedCount]
  have hc : (∑ p : S.Index, if freeCorrupted w p then 1 else 0) = corruptedCount S w := by
    simp [corruptedCount]
  have hl : (∑ p : S.Index, if (p:ℕ) ∈ listSupport w 𝔏 then 1 else 0) ≤
      Fintype.card (ListPrimeSlot w 𝔏) := by
    simpa [← sum_filter] using listed_prime_count w 𝔏
  rw [hk,hc] at hs
  exact hs.trans (Nat.add_le_add_left hl _)

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
