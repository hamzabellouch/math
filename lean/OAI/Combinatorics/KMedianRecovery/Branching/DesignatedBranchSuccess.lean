import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.ObservableCapacity

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchProgram
open Completion Categorical FiniteSampling BinaryBranchContext Sampling
variable {n m : ℕ} [PseudoMetricSpace (Fin n)]
lemma designated_successful_completion
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
    (sel dst : Fin m→Fin n)
    (hcard : (designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card=m)
    (hinj : Function.Injective sel)
    (hsel : ∀ j,sel j∈(S\s.deleted).filter (fun i=>colors i=2))
    (hdst : ∀ j,dst j∈F)
    (hdcount : (Finset.univ.image dst).card≤
      ((designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).image
        (C.blueDestination hD s.real (19/50))).card)
    (hvalue : (∑ l,branchScore D S (Δ:ℝ) s.real (sel l) (dst l))≤
      ∑ u∈designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50)),
        assignmentWeight D (completionAssignment S (Δ:ℝ) s.real) u*
          minimumMixed (19/50) (C.coveredCenter s.real) (leafCenter s.real) (leafRadius s.real)
            (C.destinations s.real) (C.destinations_nonempty hD s.real) u) :
    ∃ hH : ∀ i,(balls δ F s i).Nonempty,
      (∀ bits,result δ D F S Δ s colors hH sel dst
          (designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card bits⊆F ∧
        (result δ D F S Δ s colors hH sel dst
          (designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card bits).card=S.card ∧
        (result δ D F S Δ s colors hH sel dst
          (designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card bits).Nonempty) ∧
      average (fun bits=>realCost D (result δ D F S Δ s colors hH sel dst
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
  have hh:=result_guarantee δ hδ D F S hSF hS Δ hΔ hbound s hdel colors hH hr sel dst Y.card rd.card
    hinj hsel hdst hdcount hcount hq
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

namespace MetricKMedianRecovery.BitMachine.BinaryZeroBranch
open Completion Categorical FiniteSampling BinaryBranchContext Sampling BinaryBranchProgram
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
lemma output_feasible (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S : Finset (Fin n)) (hSF : S⊆F) (hS : S.Nonempty) (Δ : ℚ) (hΔ : 0≤Δ)
    (hbound : ∀ x,∀ f∈F,δ x f≤Δ) (s : RationalSampling.State n) (colors : Fin n→Fin 3)
    (q : ℕ) (bits) :
    output δ D F S Δ s colors q bits⊆F ∧
      (output δ D F S Δ s colors q bits).card=S.card ∧
      (output δ D F S Δ s colors q bits).Nonempty := by
  classical
  unfold output
  split_ifs with hr
  · have hradius (i : Fin s.leaves.length) : 0≤ s.radius i := by
      change (0:ℝ)≤(s.leaves[i.val].2:ℝ)
      exact_mod_cast hr.2.2.1 _ (List.getElem_mem i.isLt)
    exact (result_guarantee δ hδ D F S hSF hS Δ hΔ hbound s hr.1 colors hr.2.1 hradius
      (Fin.elim0 : Fin 0→Fin n) Fin.elim0 0 q (fun i=>Fin.elim0 i) (fun i=>Fin.elim0 i)
      (fun i=>Fin.elim0 i) (by simp) hr.2.2.2.2 hr.2.2.2.1).1 bits
  · exact ⟨hSF,rfl,hS⟩
lemma successful_completion
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
    (hcard : (designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card=0) :
    let q:=(designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card
    average (fun bits=>realCost D (output δ D F S Δ s colors q bits))≤
      (240258179/125000000:ℝ)*comparisonCost D C.assign := by
  classical
  dsimp only
  have hbd : designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))=∅ :=
    Finset.card_eq_zero.mp hcard
  have hcount : (Finset.univ.image (Fin.elim0 : Fin 0→Fin n)).card≤
      ((designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).image
        (C.blueDestination hD s.real (19/50))).card := by simp
  have hval : (∑ l : Fin 0,branchScore D S (Δ:ℝ) s.real (Fin.elim0 l) (Fin.elim0 l))≤
      ∑ u∈designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50)),
        assignmentWeight D (completionAssignment S (Δ:ℝ) s.real) u*
          minimumMixed (19/50) (C.coveredCenter s.real) (leafCenter s.real) (leafRadius s.real)
            (C.destinations s.real) (C.destinations_nonempty hD s.real) u := by simp [hbd]
  obtain ⟨hH,_,havg⟩:=designated_successful_completion δ hδ D F S O C hD hSF hOF hS Δ hΔ hbound s hs hP hm hI hN
    colors hcolors (Fin.elim0 : Fin 0→Fin n) Fin.elim0 hcard (fun i=>Fin.elim0 i)
      (fun i=>Fin.elim0 i) (fun i=>Fin.elim0 i) hcount hval
  have hr:=BinaryBranchCheck.favorable_ready δ hδ D F S O C hD hOF s hs colors hcolors hcard
  simp only [hbd,Finset.image_empty,Finset.card_empty] at hr
  simp only [output,dite_eq_left hr]
  exact havg
lemma successful_probability
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
    (hcard : (designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card=0) :
    let q:=(designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card
    (3/197:ℝ)≤probability (fun bits=>realCost D (output δ D F S Δ s colors q bits)≤
      (197/100:ℝ)*comparisonCost D C.assign) := by
  dsimp only
  apply completion_constant_success _ (comparisonCost D C.assign) hP
  · intro bits
    unfold realCost
    rw [dite_eq_left (output_feasible δ hδ D F S hSF hS Δ hΔ hbound s colors _ bits).2.2]
    exact Finset.sum_nonneg (fun p _=>distanceTo_nonneg _ _ _)
  · exact (successful_completion δ hδ D F S O C hD hSF hOF hS Δ hΔ hbound s hs hP hm hI hN
      colors hcolors hcard).trans
        (mul_le_mul_of_nonneg_right (by norm_num : (240258179/125000000:ℝ)≤97/50) hP.le)
end MetricKMedianRecovery.BitMachine.BinaryZeroBranch

end OAI
