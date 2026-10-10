import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.BranchObjective
import OAI.Combinatorics.KMedianRecovery.Encoding.SortedRepresentative

namespace OAI

namespace MetricKMedianRecovery.Completion.CopyGround
variable {n a : ℕ}
noncomputable def transversal (H : Fin a→Finset (Fin n)) (v : Fin a→Fin n) (hv : ∀ i,v i∈H i) : Finset (Fin (a*n)) :=
  Finset.univ.image (fun i=>embed H ⟨i,⟨v i,hv i⟩⟩)
lemma transversal_feasible (H : Fin a→Finset (Fin n)) (v : Fin a→Fin n) (hv : ∀ i,v i∈H i) :
    Categorical.PartitionFeasible part (transversal H v hv) := by
  apply partition_image id part (fun i=>embed H ⟨i,⟨v i,hv i⟩⟩) (fun i=>part_embed H _) Finset.univ
  intro i
  simp only [id_eq,Finset.filter_eq',Finset.mem_univ,ite_true,Finset.card_singleton,le_refl]
lemma transversal_center (H : Fin a→Finset (Fin n)) (v : Fin a→Fin n) (hv : ∀ i,v i∈H i)
    (hH : ∀ i,(H i).Nonempty) (i : Fin a) : ∃ e∈transversal H v hv,location H hH e=v i :=
  ⟨embed H ⟨i,⟨v i,hv i⟩⟩,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,location_embed H hH _⟩
end MetricKMedianRecovery.Completion.CopyGround
namespace MetricKMedianRecovery.BitMachine.BinaryBranchContext
open Completion
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
lemma balls_eq_source (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (F : Finset (Fin n)) (s : RationalSampling.State n) (i : Fin s.real.leaves.length) :
    balls δ F s (Fin.cast s.real_length i)=ballSet F (Sampling.leafCenter s.real) (Sampling.leafRadius s.real) i := by
  have hil : i.val<s.leaves.length := by simpa only [s.real_length] using i.isLt
  ext f
  simp only [balls,ballSet,Finset.mem_filter]
  apply and_congr_right
  intro _
  have hw:=s.center_cast i
  have hr:=s.radius_cast i
  change s.leaves[i.val].1=Sampling.leafCenter s.real i at hw
  change (s.leaves[i.val].2:ℝ)=Sampling.leafRadius s.real i at hr
  rw [←hw,←hr,←hδ,Rat.cast_le]
  rfl
lemma padded_comparison (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (F : Finset (Fin n)) (s : RationalSampling.State n) (center : Fin s.real.leaves.length→Fin n)
    (hF : ∀ i,center i∈F) (hball : ∀ i,dist (Sampling.leafCenter s.real i) (center i)≤Sampling.leafRadius s.real i) :
    ∃ hH : ∀ i,(balls δ F s i).Nonempty, ∃ X : Finset (Fin (s.leaves.length*n)),
      Categorical.PartitionFeasible CopyGround.part X ∧
      ∀ i,∃ e∈X,CopyGround.location (balls δ F s) hH e=center i := by
  let v : Fin s.leaves.length→Fin n := fun i=>center (Fin.cast s.real_length.symm i)
  have hv (i : Fin s.leaves.length) : v i∈balls δ F s i := by
    have he : i=Fin.cast s.real_length (Fin.cast s.real_length.symm i) := by ext;rfl
    rw [he,balls_eq_source δ hδ]
    exact Finset.mem_filter.mpr ⟨hF _,hball _⟩
  have hH (i : Fin s.leaves.length) : (balls δ F s i).Nonempty := ⟨v i,hv i⟩
  refine ⟨hH,CopyGround.transversal (balls δ F s) v hv,CopyGround.transversal_feasible _ _ _,?_⟩
  intro i
  have he : Fin.cast s.real_length.symm (Fin.cast s.real_length i)=i := by ext;rfl
  simpa only [v,he] using CopyGround.transversal_center (balls δ F s) v hv hH (Fin.cast s.real_length i)
end MetricKMedianRecovery.BitMachine.BinaryBranchContext

namespace MetricKMedianRecovery.BitMachine.BinaryBranchProgram
open Completion Categorical FiniteSampling BinaryBranchContext Sampling
variable {n m : ℕ} [PseudoMetricSpace (Fin n)]
lemma planned_successful_completion
    (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (hD : D.Nonempty)
    (hSF : S⊆F) (hOF : O⊆F) (hS : S.Nonempty)
    (Δ : ℚ) (hΔ : 0≤Δ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (s : RationalSampling.State n) (hs : C.Correct hD (1/1000000) s.real)
    (hP : 0<comparisonCost D C.assign) (hm : 0<C.bad.card)
    (hI : C.removalTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign)
    (hN : C.nearTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign)
    (colors : Fin n→Fin 3)
    (hcolors : ∀ u∈(C.nonproxy\s.real.deleted)∪designatedProxies (C.nonproxy\s.real.deleted)
      (C.designatedDestination hD s.real (19/50)),colors u=requiredColors (C.nonproxy\s.real.deleted)
      (C.designatedDestination hD s.real (19/50)) u)
    (label : Fin n→Fin m)
    (hcard : (designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card=m)
    (P : BlueSubsetDP.Plan ((S\s.deleted).filter (fun i=>colors i=2)) F label
      (fun u v=>(rationalScore δ D S Δ s u v:ℝ))
      (((designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).image
        (C.blueDestination hD s.real (19/50))).card))
    (hvalue : (∑ l,branchScore D S (Δ:ℝ) s.real (P.sel l) (P.dst l))≤
      ∑ u∈designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50)),
        assignmentWeight D (completionAssignment S (Δ:ℝ) s.real) u*
          minimumMixed (19/50) (C.coveredCenter s.real) (leafCenter s.real) (leafRadius s.real)
            (C.destinations s.real) (C.destinations_nonempty hD s.real) u) :
    ∃ hH : ∀ i,(balls δ F s i).Nonempty,
      (∀ bits,result δ D F S Δ s colors hH P.sel P.dst
          (designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card bits⊆F ∧
        (result δ D F S Δ s colors hH P.sel P.dst
          (designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card bits).card=S.card ∧
        (result δ D F S Δ s colors hH P.sel P.dst
          (designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card bits).Nonempty) ∧
      average (fun bits=>realCost D (result δ D F S Δ s colors hH P.sel P.dst
        (designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card bits))≤
          (240258179/125000000:ℝ)*comparisonCost D C.assign := by
  classical
  let dest:=C.designatedDestination hD s.real (19/50)
  let Rstar:=C.nonproxy\s.real.deleted
  let rd:=designatedRed Rstar dest
  let bd:=designatedBlue Rstar dest
  let red:=(S\s.deleted).filter (fun i=>colors i=1)
  let green:=(S\s.deleted).filter (fun i=>colors i=0)
  let Y:=bd.image (C.blueDestination hD s.real (19/50))
  have hc:=C.favorable_color_subsets hD s.real (19/50) colors hcolors
  have hrd : rd⊆red := hc.1
  let T:=SortedIndex.representative red rd
  have hTim : T.image (SortedIndex.enum red)=rd := SortedIndex.representative_image red rd hrd
  have hT : T.card=rd.card := SortedIndex.representative_card red rd hrd
  have hq : rd.card≤red.card := Finset.card_le_card hrd
  have hcount : s.leaves.length+Y.card≤ s.deleted.card+rd.card+m := by
    have hh:=C.favorable_counter_bound hD s.real hs (19/50)
    dsimp only at hh
    change s.real.leaves.length+Y.card≤ s.deleted.card+rd.card+bd.card at hh
    rw [s.real_length,show bd.card=m from hcard] at hh
    exact hh
  have hdel : s.deleted⊆S := by
    intro u hu
    exact (Finset.mem_sdiff.mp (hs.1 hu)).1
  have hr : ∀ i,0≤ s.radius i := by
    intro i
    let j:=Fin.cast s.real_length.symm i
    have hj : Fin.cast s.real_length j=i := by ext;rfl
    rw [←hj,s.radius_cast]
    exact (hs.2.2 _ (List.getElem_mem j.isLt)).2.2.2.1.le
  obtain ⟨hH,X,hX,hcenter⟩:=padded_comparison δ hδ F s (C.coveredCenter s.real)
    (C.coveredCenter_facility hD (1/1000000) s.real hs F hOF)
    (C.coveredCenter_ball hD (1/1000000) s.real hs)
  have hh:=result_guarantee δ hδ D F S hSF hS Δ hΔ hbound s hdel colors hH hr P.sel P.dst Y.card rd.card
    P.selected_injective (fun j=>(P.selection j).1) (fun j=>(P.selection j).2.2) P.destination_count hcount hq
  refine ⟨hH,hh.1,(hh.2 X hX).trans ?_⟩
  rw [objective_eq_source δ hδ,objective_eq_source δ hδ]
  have hdisj : Disjoint (T.image (SortedIndex.enum red)) bd := by
    rw [hTim];exact (designated_partition Rstar dest).1
  have hcover : T.image (SortedIndex.enum red)∪bd=C.nonproxy\s.real.deleted := by
    rw [hTim];exact (designated_partition Rstar dest).2
  have hredDest : ∀ r∈T,
      match selectedDestination (19/50) (C.coveredCenter s.real) (leafCenter s.real) (leafRadius s.real)
          (C.destinations s.real) (C.destinations_nonempty hD s.real) (SortedIndex.enum red r) with
      | .proxy φ=>φ∈green | .covered _=>True | .uncovered _=>False := by
    intro r hrT
    have hrD : SortedIndex.enum red r∈rd := by
      rw [←hTim];exact Finset.mem_image.mpr ⟨r,hrT,rfl⟩
    have hh:=C.favorable_red_rule hD (1/1000000) (19/50) s.real hs colors hcolors _ hrD
    simp only [Comparison.designatedDestination] at hh
    cases hd : selectedDestination (19/50) (C.coveredCenter s.real) (leafCenter s.real)
        (leafRadius s.real) (C.destinations s.real) (C.destinations_nonempty hD s.real) (SortedIndex.enum red r) with
    | proxy v=>
      simp only [hd] at hh
      simpa only [Comparison.colorClass,green,RationalSampling.State.real] using hh
    | covered i=>trivial
    | uncovered v=>simp only [hd] at hh
  have hss:=C.surrogate_success hD (Δ:ℝ) s.real hs (Rat.cast_nonneg.mpr hΔ) hP hm hI hN
    (CopyGround.location (balls δ F s) hH) X hcenter green bd (SortedIndex.enum red) (SortedIndex.enum_injective red)
    rd.card T hT hdisj hcover (fun r hrT=>by
      have hh:=hredDest r hrT
      cases hd : selectedDestination (19/50) (C.coveredCenter s.real) (leafCenter s.real)
          (leafRadius s.real) (C.destinations s.real) (C.destinations_nonempty hD s.real) (SortedIndex.enum red r) with
      | proxy v=>simpa only [hd] using hh
      | covered i=>trivial
      | uncovered v=>simp only [hd] at hh) _ hvalue
  norm_num at hss ⊢
  exact hss
end MetricKMedianRecovery.BitMachine.BinaryBranchProgram

end OAI
