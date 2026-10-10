import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.FiniteNodeCost
import OAI.Combinatorics.RamseyFive.Geometry.AmbientOriginalDomination
import OAI.Combinatorics.RamseyFive.Entropy.OptionEventBounds

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence

section
open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem producedPair_original (hd : finrank K V=5) (hq : 3≤Nat.card K)
    (A A₀ UA : Finset (ℙ K V)) (hA : A.Nonempty) (hAA₀ : A⊆A₀) (hAU : A⊆UA)
    (B B₀ UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty) (hBB₀ : B⊆B₀) (hBU : B⊆UB)
    (c δ M : ℝ) (hc : 0<c) (hc9 : c≤9/10) (hδ : 0<δ)
    (htrimA : δ*A₀.card≤A.card) (htrimB : δ*B₀.card≤B.card)
    (W : Finset (ℙ K V)) (hcap : CaptureBound A UA c M W)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences A B≤c*A.card*B.card) :
    (∀b,eventMass (producedPairLaw A UA B UB hB c (some W))
      (Finset.univ.filter fun out=>Excludes b (out.map Prod.fst))≤
        (50*(Nat.card K:ℝ)/(9*(c*δ)))*(((A₀.filter fun a=>Incident a b).card:ℝ)/A₀.card)) ∧
    (∀a,eventMass (producedPairLaw A UA B UB hB c (some W))
      (Finset.univ.filter fun out=>Excludes a (out.map Prod.snd))≤
        (50*(Nat.card K:ℝ)/(9*((9:ℝ)/10*δ)))*(((B₀.filter (Incident a)).card:ℝ)/B₀.card)) := by
  have hW : W.Nonempty := (hcap.nonempty hA hc).mono Finset.inter_subset_right
  have hq1 : (1:ℝ)≤Nat.card K := by exact_mod_cast (by omega : 1≤Nat.card K)
  have hlenA := reverseLength_spec (Nat.card K) (Real.log ((UA.card:ℝ)/A.card)) hq1
    (Real.log_nonneg ((le_div_iff₀ (by exact_mod_cast hA.card_pos)).mpr
      (by simpa only [one_mul] using (show (A.card:ℝ)≤UA.card from by exact_mod_cast Finset.card_le_card hAU))))
  have hlenB := reverseLength_spec (Nat.card K) (Real.log ((UB.card:ℝ)/B.card)) hq1
    (Real.log_nonneg ((le_div_iff₀ (by exact_mod_cast hB.card_pos)).mpr
      (by simpa only [one_mul] using (show (B.card:ℝ)≤UB.card from by exact_mod_cast Finset.card_le_card hBU))))
  have hsparse' : 1000*(Nat.card K:ℝ)*incidences A B≤(9:ℝ)/10*A.card*B.card := by
    have hh := mul_le_mul_of_nonneg_right hc9 (mul_nonneg (Nat.cast_nonneg A.card) (Nat.cast_nonneg B.card))
    nlinarith only [hh,hsparse]
  let nA := reverseLength (Nat.card K) (Real.log ((UA.card:ℝ)/A.card))
  let nB := reverseLength (Nat.card K) (Real.log ((UB.card:ℝ)/B.card))
  let MA := (320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/B.card
  let MB := (320/c+320)*(Nat.card K:ℝ)^5/A.card
  let firstCap := ambientCapLaw (fun b a=>Incident a b) B UB (A∩W) W hW nB (Nat.card K) MB
  let next := nextAmbientCapLaw A UA B UB hB nA (Nat.card K) MA MB
  have he : producedPairLaw A UA B UB hB c (some W)=map (adaptiveLaw firstCap next) pairOptions := by
    simp only [producedPairLaw,dite_eq_left hW]
    rfl
  rw [he]
  constructor
  · intro b
    have hm := pairOptions_event_left (adaptiveLaw firstCap next) (Excludes b) (by simp [Excludes])
    rw [adaptive_event_first] at hm
    exact hm.trans (firstAmbient_original hd (by norm_num) hq A A₀ hA hAA₀ B UB hB hBU W hW
      c δ hc (by linarith only [hc9]) hδ htrimA hcap.2.2 hsparse nB hlenB.1 hlenB.2.1 b)
  · intro a
    have hm := pairOptions_event_right (adaptiveLaw firstCap next) (Excludes a) (by simp [Excludes])
    apply hm.trans
    apply adaptive_event_second_le
    intro Y
    exact secondAmbient_original hd (by norm_num) hq A UA hA hAU B B₀ UB hB hBB₀ δ hδ htrimB hsparse'
      nA hlenA.1 hlenA.2.1 MB Y a
end

open Module FiniteEntropy ReverseCap ScoreGeometry
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]

theorem finiteNode_original (pred : FinitePredictor (ℙ K V) (ℙ K (Dual K V)))
    (hd : finrank K V=5) (hq : 3≤Nat.card K)
    (A A₀ UA : Finset (ℙ K V)) (hA : A.Nonempty) (hAA₀ : A⊆A₀) (hAU : A⊆UA)
    (B B₀ UB : Finset (ℙ K (Dual K V))) (hB : B.Nonempty) (hBB₀ : B⊆B₀) (hBU : B⊆UB)
    (c δ M : ℝ) (hc : 0<c) (hc9 : c≤9/10) (hδ : 0<δ)
    (htrimA : δ*A₀.card≤A.card) (htrimB : δ*B₀.card≤B.card)
    (hsparse : 1000*(Nat.card K:ℝ)*incidences A B≤c*A.card*B.card)
    (H : ℕ)
    (hnA : reverseLength (Nat.card K) (Real.log ((UA.card:ℝ)/A.card))<H+1)
    (hnB : reverseLength (Nat.card K) (Real.log ((UB.card:ℝ)/B.card))<H+1) :
    (∀b,eventMass (finiteNodeOutput pred A UA B UB H ⟨_,hnA⟩ ⟨_,hnB⟩ (Nat.card K)
      ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/B.card)
      ((320/c+320)*(Nat.card K:ℝ)^5/A.card) c M)
      (Finset.univ.filter fun out=>Excludes b (out.map Prod.fst))≤
        (50*(Nat.card K:ℝ)/(9*(c*δ)))*(((A₀.filter fun a=>Incident a b).card:ℝ)/A₀.card)) ∧
    (∀a,eventMass (finiteNodeOutput pred A UA B UB H ⟨_,hnA⟩ ⟨_,hnB⟩ (Nat.card K)
      ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/B.card)
      ((320/c+320)*(Nat.card K:ℝ)^5/A.card) c M)
      (Finset.univ.filter fun out=>Excludes a (out.map Prod.snd))≤
        (50*(Nat.card K:ℝ)/(9*((9:ℝ)/10*δ)))*(((B₀.filter (Incident a)).card:ℝ)/B₀.card)) := by
  rw [finiteNode_law]
  have hn (W : Finset (ℙ K V)) (hW : ¬CaptureBound A UA c M W) :
      finiteNodeNextLaw A UA B UB H ⟨_,hnA⟩ ⟨_,hnB⟩ (Nat.card K)
        ((320/((9:ℝ)/10)+320)*(Nat.card K:ℝ)^5/B.card)
        ((320/c+320)*(Nat.card K:ℝ)^5/A.card) c M (some W)=pureLaw none := by
    unfold finiteNodeNextLaw finiteNodeNextOut
    simp only [Option.bind_some,dite_eq_right hW]
    exact map_const _ none
  constructor
  · intro b
    have hnon : 0≤(50*(Nat.card K:ℝ)/(9*(c*δ)))*(((A₀.filter fun a=>Incident a b).card:ℝ)/A₀.card) := by positivity
    apply optionCompose_event_le _ _ _ (by simp [Excludes]) _ hnon
    intro W _
    by_cases hW : CaptureBound A UA c M W
    · rw [finiteNodeNextLaw_produced A UA B UB hA hB c M hc W hW H hnA hnB]
      exact (producedPair_original hd hq A A₀ UA hA hAA₀ hAU B B₀ UB hB hBB₀ hBU
        c δ M hc hc9 hδ htrimA htrimB W hW hsparse).1 b
    · rw [hn W hW]
      have he : eventMass (pureLaw (none : Option (Finset (ℙ K (Dual K V))×Finset (ℙ K V))))
          (Finset.univ.filter fun out=>Excludes b (out.map Prod.fst))=0 := by
        unfold eventMass
        apply Finset.sum_eq_zero
        intro out hout
        have hp := (Finset.mem_filter.mp hout).2
        cases out <;> simp_all [pureLaw,Excludes]
      rw [he]
      exact hnon
  · intro a
    have hnon : 0≤(50*(Nat.card K:ℝ)/(9*((9:ℝ)/10*δ)))*(((B₀.filter (Incident a)).card:ℝ)/B₀.card) := by positivity
    apply optionCompose_event_le _ _ _ (by simp [Excludes]) _ hnon
    intro W _
    by_cases hW : CaptureBound A UA c M W
    · rw [finiteNodeNextLaw_produced A UA B UB hA hB c M hc W hW H hnA hnB]
      exact (producedPair_original hd hq A A₀ UA hA hAA₀ hAU B B₀ UB hB hBB₀ hBU
        c δ M hc hc9 hδ htrimA htrimB W hW hsparse).2 a
    · rw [hn W hW]
      have he : eventMass (pureLaw (none : Option (Finset (ℙ K (Dual K V))×Finset (ℙ K V))))
          (Finset.univ.filter fun out=>Excludes a (out.map Prod.snd))=0 := by
        unfold eventMass
        apply Finset.sum_eq_zero
        intro out hout
        have hp := (Finset.mem_filter.mp hout).2
        cases out <;> simp_all [pureLaw,Excludes]
      rw [he]
      exact hnon

end SharpRamseyFive.ProjectiveIncidence

end OAI
