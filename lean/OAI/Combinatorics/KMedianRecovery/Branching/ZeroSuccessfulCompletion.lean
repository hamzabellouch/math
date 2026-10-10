import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.ZeroObjective

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open Completion Categorical FiniteSampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

theorem zero_successful_completion
    (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (s : State V) (hs : C.Correct hD (1/1000000) s) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (hI : C.removalTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    (hN : C.nearTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    (F : Finset V) (hSF : S ⊆ F) (hOF : O ⊆ F) (hS : S.Nonempty)
    (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ)
    (colors : V → Fin 3)
    (hcolors : ∀ u ∈ (C.nonproxy \ s.deleted) ∪
        designatedProxies (C.nonproxy \ s.deleted) (C.designatedDestination hD s (19/50)),
      colors u = requiredColors (C.nonproxy \ s.deleted)
        (C.designatedDestination hD s (19/50)) u)
    (hBlue : designatedBlue (C.nonproxy \ s.deleted)
      (C.designatedDestination hD s (19/50)) = ∅) :
    let q := (designatedRed (C.nonproxy \ s.deleted)
      (C.designatedDestination hD s (19/50))).card
    average (fun bits => realCost D
      (zeroOutput D F S hSF hS Δ hΔ hbound s colors q bits)) ≤
        (240258179/125000000:ℝ)*comparisonCost D C.assign := by
  classical
  dsimp only
  let dest := C.designatedDestination hD s (19/50)
  let Rstar := C.nonproxy \ s.deleted
  let redD := designatedRed Rstar dest
  let red := colorClass (S \ s.deleted) colors 1
  let G := colorClass (S \ s.deleted) colors 0
  have hcolorSub := (C.favorable_color_subsets hD s (19/50) colors hcolors).1
  obtain ⟨T,hTimage,hTcard⟩ := subset_subtype_representative red redD hcolorSub
  let q := redD.card
  have hq : q ≤ (colorClass (S \ s.deleted) colors 1).card := Finset.card_le_card hcolorSub
  have hcount : s.leaves.length+0 ≤ s.deleted.card+q+0 := by
    have hh := C.favorable_counter_bound hD s hs (19/50)
    dsimp only at hh
    simp only [hBlue,Finset.image_empty,Finset.card_empty,add_zero] at hh
    exact hh
  obtain ⟨hballs,X,hX,_,hcenter⟩ := copied_comparison F (leafCenter s)
    (C.coveredCenter s) (leafRadius s)
    (C.coveredCenter_facility hD (1/1000000) s hs F hOF)
    (C.coveredCenter_ball hD (1/1000000) s hs)
  have hr : ∀ i, 0 ≤ leafRadius s i := fun i =>
    (hs.2.2 s.leaves[i.val] (List.getElem_mem i.isLt)).2.2.2.1.le
  have hQ : s.deleted ⊆ S := by
    intro u hu
    exact (Finset.mem_sdiff.mp (hs.1 hu)).1
  have hready : BranchReady F S s colors q 0 0 := ⟨hQ,hballs,hr,hq,hcount⟩
  have heq : zeroOutput D F S hSF hS Δ hΔ hbound s colors q =
      zeroAccepted D F S hSF hS Δ hΔ hbound s colors q hready := by
    simp only [zeroOutput,dite_eq_left hready]
  change average (fun bits => realCost D
    (zeroOutput D F S hSF hS Δ hΔ hbound s colors q bits)) ≤ _
  rw [heq]
  apply ((zeroAccepted_spec D F S hSF hS Δ hΔ hbound s colors q hready).2 X hX).trans
  have hdisj : Disjoint (T.image Subtype.val) (∅ : Finset V) := Finset.disjoint_empty_right _
  have hcover : T.image Subtype.val ∪ ∅ = C.nonproxy \ s.deleted := by
    rw [hTimage]
    have hb : designatedBlue Rstar dest = ∅ := hBlue
    simpa only [hb, redD, Rstar] using (designated_partition Rstar dest).2
  change (19/50:ℝ) * _ + (1-19/50:ℝ) * _ ≤ _
  apply C.surrogate_success hD Δ s hs hΔ hP hm hI hN
    (copiedLoc F (leafCenter s) (leafRadius s)) X hcenter G ∅
    (fun r : ↥red => (r:V)) Subtype.val_injective q T hTcard hdisj hcover
    _ 0 (by simp)
  intro r hrT
  have hrD : (r:V) ∈ redD := by
    rw [← hTimage]
    exact Finset.mem_image.mpr ⟨r,hrT,rfl⟩
  have hh := C.favorable_red_rule hD (1/1000000) (19/50) s hs colors hcolors r hrD
  cases hd : selectedDestination (19/50) (C.coveredCenter s) (leafCenter s)
      (leafRadius s) (C.destinations s) (C.destinations_nonempty hD s) (r:V) with
  | proxy v => simpa only [designatedDestination,hd] using hh
  | covered i => trivial
  | uncovered v => simp only [designatedDestination,hd] at hh

theorem zero_successful_probability
    (C : Comparison D S O) (hD : D.Nonempty)
    (Δ : ℝ) (s : State V) (hs : C.Correct hD (1/1000000) s) (hΔ : 0 ≤ Δ)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (hI : C.removalTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    (hN : C.nearTotal Δ s ≤ (1/1000000:ℝ)*comparisonCost D C.assign)
    (F : Finset V) (hSF : S ⊆ F) (hOF : O ⊆ F) (hS : S.Nonempty)
    (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ)
    (colors : V → Fin 3)
    (hcolors : ∀ u ∈ (C.nonproxy \ s.deleted) ∪
        designatedProxies (C.nonproxy \ s.deleted) (C.designatedDestination hD s (19/50)),
      colors u = requiredColors (C.nonproxy \ s.deleted)
        (C.designatedDestination hD s (19/50)) u)
    (hBlue : designatedBlue (C.nonproxy \ s.deleted)
      (C.designatedDestination hD s (19/50)) = ∅) :
    let q := (designatedRed (C.nonproxy \ s.deleted)
      (C.designatedDestination hD s (19/50))).card
    (3/197:ℝ) ≤ probability (fun bits => realCost D
      (zeroOutput D F S hSF hS Δ hΔ hbound s colors q bits) ≤
        (197/100:ℝ)*comparisonCost D C.assign) := by
  dsimp only
  apply completion_constant_success _ (comparisonCost D C.assign) hP
  · intro bits
    unfold realCost
    rw [dite_eq_left (zeroOutput_feasible D F S hSF hS Δ hΔ hbound s colors _ bits).2.2]
    exact Finset.sum_nonneg (fun p _ => distanceTo_nonneg _ _ _)
  · exact (C.zero_successful_completion hD Δ s hs hΔ hP hm hI hN
      F hSF hOF hS hbound colors hcolors hBlue).trans
        (mul_le_mul_of_nonneg_right (by norm_num :
          (240258179/125000000:ℝ) ≤ 97/50) hP.le)

end MetricKMedianRecovery.Sampling.Comparison

end OAI
