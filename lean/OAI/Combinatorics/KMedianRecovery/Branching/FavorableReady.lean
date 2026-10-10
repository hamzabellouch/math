import Mathlib
import OAI.Combinatorics.KMedianRecovery.Branching.CopyComparison

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchCheck
open Completion Sampling BinaryBranchContext
variable {n m : ℕ} [PseudoMetricSpace (Fin n)]
lemma favorable_ready (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (hD : D.Nonempty) (hOF : O⊆F)
    (s : RationalSampling.State n) (hs : C.Correct hD (1/1000000) s.real)
    (colors : Fin n→Fin 3)
    (hcolors : ∀ u∈(C.nonproxy\s.real.deleted)∪designatedProxies (C.nonproxy\s.real.deleted)
      (C.designatedDestination hD s.real (19/50)),colors u=requiredColors (C.nonproxy\s.real.deleted)
      (C.designatedDestination hD s.real (19/50)) u)
    (hcard : (designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card=m) :
    Ready δ F S s colors
      (designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card
      (((designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).image
        (C.blueDestination hD s.real (19/50))).card) m := by
  classical
  have hball:=padded_comparison δ hδ F s (C.coveredCenter s.real)
    (C.coveredCenter_facility hD (1/1000000) s.real hs F hOF)
    (C.coveredCenter_ball hD (1/1000000) s.real hs)
  refine ⟨?_,hball.choose,?_,?_,?_⟩
  · intro u hu
    exact (Finset.mem_sdiff.mp (hs.1 hu)).1
  · intro z hz
    have hh:= (hs.2.2 (z.1,(z.2:ℝ)) (List.mem_map.mpr ⟨z,hz,rfl⟩)).2.2.2.1.le
    change (0:ℝ)≤(z.2:ℝ) at hh
    exact Rat.cast_nonneg.mp hh
  · exact Finset.card_le_card (C.favorable_color_subsets hD s.real (19/50) colors hcolors).1
  · have hh:=C.favorable_counter_bound hD s.real hs (19/50)
    dsimp only at hh
    rw [hcard] at hh
    change s.real.leaves.length+_≤ s.deleted.card+_+m at hh
    have hl:=s.real_length
    omega
end MetricKMedianRecovery.BitMachine.BinaryBranchCheck

namespace MetricKMedianRecovery.BitMachine.BinaryObservableBranch
open Completion Categorical FiniteSampling BinaryBranchContext Sampling BinaryBranchProgram
variable {n m : ℕ} [PseudoMetricSpace (Fin n)]
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
    (label : Fin n→Fin m)
    (hcard : (designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card=m)
    (hinj : Set.InjOn label (↑(designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50)))))
    (r0 y0 : Fin n) :
    let q:=(designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card
    let c:=((designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).image
      (C.blueDestination hD s.real (19/50))).card
    average (fun bits=>realCost D (output δ D F S Δ s colors label q c r0 y0 bits))≤
      (240258179/125000000:ℝ)*comparisonCost D C.assign := by
  classical
  let : Nonempty (Fin n) := ⟨hS.choose⟩
  dsimp only
  obtain ⟨v,xs,h,hvalue⟩:=favorable_literal_plan δ hδ D F S O C hD hOF Δ s colors hcolors label hcard hinj r0 y0
  let P:=BlueDP.makePlan ((S\s.deleted).filter (fun i=>colors i=2)) F label (rationalScore δ D S Δ s) _ r0 y0 v xs h
  obtain ⟨hH,_,havg⟩:=planned_successful_completion δ hδ D F S O C hD hSF hOF hS Δ hΔ hbound s hs hP hm hI hN
    colors hcolors label hcard P hvalue
  have hr:=BinaryBranchCheck.favorable_ready δ hδ D F S O C hD hOF s hs colors hcolors hcard
  have he (bits) := output_some δ D F S Δ s colors label _ _ r0 y0 hr v xs h bits
  simp_rw [he]
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
    (label : Fin n→Fin m)
    (hcard : (designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card=m)
    (hinj : Set.InjOn label (↑(designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50)))))
    (r0 y0 : Fin n) :
    let q:=(designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card
    let c:=((designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).image
      (C.blueDestination hD s.real (19/50))).card
    (3/197:ℝ)≤probability (fun bits=>realCost D (output δ D F S Δ s colors label q c r0 y0 bits)≤
      (197/100:ℝ)*comparisonCost D C.assign) := by
  dsimp only
  apply completion_constant_success _ (comparisonCost D C.assign) hP
  · intro bits
    unfold realCost
    rw [dite_eq_left (output_feasible δ hδ D F S hSF hS Δ hΔ hbound s colors label _ _ r0 y0 bits).2.2]
    exact Finset.sum_nonneg (fun p _=>distanceTo_nonneg _ _ _)
  · exact (successful_completion δ hδ D F S O C hD hSF hOF hS Δ hΔ hbound s hs hP hm hI hN
      colors hcolors label hcard hinj r0 y0).trans
        (mul_le_mul_of_nonneg_right (by norm_num : (240258179/125000000:ℝ)≤97/50) hP.le)
end MetricKMedianRecovery.BitMachine.BinaryObservableBranch

namespace MetricKMedianRecovery.BitMachine.BinaryObservableBranch
open Completion Categorical FiniteSampling BinaryBranchContext Sampling BinaryBranchProgram
variable {n : ℕ} [PseudoMetricSpace (Fin n)]
abbrev Bits (n p : ℕ) := Categorical.BinaryOracleIndex (Fin (p*n)) p (Categorical.Explicit.exponent p)
  (Categorical.Explicit.samples (p*n) p)→Bool
lemma fair_color_label_completion
    (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (hD : D.Nonempty)
    (hSF : S⊆F) (hOF : O⊆F) (hS : S.Nonempty)
    (Δ : ℚ) (hΔ : 0≤Δ) (hbound : ∀ x,∀ f∈F,δ x f≤Δ)
    (s : RationalSampling.State n) (hs : C.Correct hD (1/1000000) s.real)
    (hP : 0<comparisonCost D C.assign) (hm : 0<C.bad.card)
    (hI : C.removalTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign)
    (hN : C.nearTotal (Δ:ℝ) s.real≤(1/1000000:ℝ)*comparisonCost D C.assign)
    (b : ℕ) (hb : 0<b)
    (hcard : (designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card=b)
    (r0 y0 : Fin n) :
    let q:=(designatedRed (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card
    let c:=((designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).image
      (C.blueDestination hD s.real (19/50))).card
    (1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ)≤
      probability (fun seed : ((Fin n→Fin 4) × (Fin n→Fin (ColorLabel.labelRange b))) × Bits n s.leaves.length=>
        realCost D (output δ D F S Δ s (fun u=>ColorLabel.color (seed.1.1 u))
          (fun u=>ColorLabel.label b hb (seed.1.2 u)) q c r0 y0 seed.2)≤
            (197/100:ℝ)*comparisonCost D C.assign) := by
  classical
  dsimp only
  let R := C.nonproxy \ s.real.deleted
  let dest := C.designatedDestination hD s.real (19/50)
  let Q := R ∪ designatedProxies R dest
  let B := designatedBlue R dest
  let PC : (Fin n → Fin 4) → Prop := fun seed =>
    ∀ i ∈ Q, ColorLabel.color (seed i) = requiredColors R dest i
  let PL : (Fin n → Fin (ColorLabel.labelRange b)) → Prop := fun seed =>
    Set.InjOn (fun i => ColorLabel.label b hb (seed i)) (↑B)
  have hR : R.card ≤ C.bad.card := by
    rw [← C.nonproxy_card]
    exact Finset.card_le_card Finset.sdiff_subset
  have hQ : Q.card ≤ 2*C.bad.card := color_requirement_count R dest C.bad.card hR
  have hB : b ≤ C.bad.card := by
    rw [← hcard]
    exact (Finset.card_filter_le _ _).trans hR
  have hc : (1/4:ℝ)^Q.card ≤ probability PC :=
    ColorLabel.color_event_probability Q (requiredColors R dest)
  have hl : (1/(2*Real.exp 1))^b ≤ probability PL :=
    ColorLabel.label_event_probability B b hb hcard
  have hexp : 1 ≤ Real.exp (1:ℝ) := Real.one_le_exp (by norm_num)
  have hbase : 0 ≤ 1/(2*Real.exp (1:ℝ)) := by positivity
  have hbase1 : 1/(2*Real.exp (1:ℝ)) ≤ 1 := by
    rw [div_le_iff₀ (by positivity : 0 < 2*Real.exp (1:ℝ))]
    linarith
  have hc' : (1/4:ℝ)^(2*C.bad.card) ≤ probability PC :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hQ).trans hc
  have hl' : (1/(2*Real.exp 1))^C.bad.card ≤ probability PL :=
    (pow_le_pow_of_le_one hbase hbase1 hB).trans hl
  have hp : (1/(32*Real.exp 1))^C.bad.card ≤ probability (fun seed : (Fin n → Fin 4) × (Fin n → Fin (ColorLabel.labelRange b)) => PC seed.1 ∧ PL seed.2) := by
    rw [probability_prod_conj]
    calc
      _ = (1/4:ℝ)^(2*C.bad.card)*(1/(2*Real.exp 1))^C.bad.card := by
        rw [pow_mul,← mul_pow]
        congr 1
        ring
      _ ≤ probability PC * probability PL :=
        mul_le_mul hc' hl' (by positivity) (probability_nonneg PC)
  apply (mul_le_mul_of_nonneg_right hp (by norm_num : (0:ℝ) ≤ 3/197)).trans
  refine probability_prod_lower
    (fun seed : (Fin n → Fin 4) × (Fin n → Fin (ColorLabel.labelRange b)) => PC seed.1 ∧ PL seed.2)
    (fun seed bits => realCost D (output δ D F S Δ s
      (fun u => ColorLabel.color (seed.1 u))
      (fun u => ColorLabel.label b hb (seed.2 u))
      (designatedRed R dest).card (B.image (C.blueDestination hD s.real (19/50))).card r0 y0 bits) ≤
        (197/100:ℝ)*comparisonCost D C.assign) ?_
  intro seed hseed
  exact successful_probability δ hδ D F S O C hD hSF hOF hS Δ hΔ hbound s hs hP hm hI hN
    (fun u=>ColorLabel.color (seed.1 u)) hseed.1
    (fun u=>ColorLabel.label b hb (seed.2 u)) hcard hseed.2 r0 y0
end MetricKMedianRecovery.BitMachine.BinaryObservableBranch

end OAI
