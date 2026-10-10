import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Candidates.Candidates
import OAI.Combinatorics.BalancedRyser.Local.Local

namespace OAI

namespace Balanced.Local.KernelBridge

open scoped BigOperators ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*}

def encodeTuple (T : FourTuple F) : TupleCode F := (T.generator, T.side)
def encodeChoice (C : SplitChoice F) : ChoiceCode F := (C.line, encodeTuple C.tuple)

@[simp] theorem decode_encode_tuple (T : FourTuple F) :
    decodeTuple (encodeTuple T) = T := by cases T; rfl

@[simp] theorem decode_encode_choice (C : SplitChoice F) :
    decodeChoice (encodeChoice C) = C := by cases C; rfl

@[simp] theorem encode_decode_tuple (t : TupleCode F) :
    encodeTuple (decodeTuple t) = t := by cases t; rfl

@[simp] theorem encode_decode_choice (c : ChoiceCode F) :
    encodeChoice (decodeChoice c) = c := by cases c; rfl

variable [Field F] [Fintype F] [DecidableEq F]

def canonicalRetention : RetentionRule F where
  candidates M g :=
    (Finset.univ.filter (fun l : Line F => l.1 = g ∧ SupportsValidTuple M l)).image
      (fun l => encodeChoice (retainedChoice M l))
  valid := by
    classical
    intro M g c hc
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hc
    have hl' := (Finset.mem_filter.mp hl).2
    simp only [decode_encode_choice]
    rcases hl' with ⟨rfl, hs⟩
    simpa only [retainedChoice, dite_eq_left hs] using Classical.choose_spec hs
  uniqueLine := by
    classical
    intro M g c d hc hd hline
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hd
    change l = m at hline
    subst m
    rfl
  complete := by
    classical
    intro M g c hc
    have hdir : c.1.1 = g := hc.1
    have hs : SupportsValidTuple M c.1 := by
      refine ⟨decodeTuple c.2, ?_⟩
      simpa only [hdir, decodeChoice] using hc
    refine ⟨encodeChoice (retainedChoice M c.1), ?_, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨c.1, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdir, hs⟩

theorem retained_tuple_injective (Q : RetentionRule F) (M : MergedPairs F)
    (g : Direction F) :
    Set.InjOn (fun c : ChoiceCode F => c.2) (↑(Q.candidates M g) : Set (ChoiceCode F)) := by
  intro c hc d hd htuple
  have vc := Q.valid M g c hc
  have vd := Q.valid M g d hd
  apply Q.uniqueLine M g c d hc hd
  apply Prod.ext (vc.1.trans vd.1.symm)
  have hp := vc.2.2.2.2.2.1 (0 : Fin 4)
  have hq := vd.2.2.2.2.2.1 (0 : Fin 4)
  change lineEval c.1.1 (tuplePoint M (decodeTuple c.2) 0) = c.1.2 at hp
  change lineEval d.1.1 (tuplePoint M (decodeTuple d.2) 0) = d.1.2 at hq
  have hcdir : c.1.1 = g := vc.1
  have hddir : d.1.1 = g := vd.1
  change c.2 = d.2 at htuple
  rw [hcdir, htuple] at hp
  rw [hddir] at hq
  exact hp.symm.trans hq

omit [Field F] in
theorem offsetProbability_eq_card (E : MergedPairs F → Prop) :
    offsetProbability E =
      ((Finset.univ.filter E).card : ℝ) / Fintype.card (MergedPairs F) := by
  classical
  simp [offsetProbability]

theorem offsetProbability_eq_canonical (E : MergedPairs F → Prop) :
    offsetProbability E = offsetEventProbability {M | E M} := by
  rw [offsetProbability_eq_card]
  have hLaw : (offsetLaw F).toOuterMeasure {M | E M} =
      (Fintype.card {M // E M} : ℝ≥0∞) / Fintype.card (MergedPairs F) := by
    convert PMF.toOuterMeasure_uniformOfFintype_apply
      (α := MergedPairs F) {M | E M} using 1
    · unfold offsetLaw
      congr
      exact Subsingleton.elim _ _
    · congr
  unfold offsetEventProbability
  rw [hLaw]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, Fintype.card_subtype]

theorem offsetProbability_nonneg (E : MergedPairs F → Prop) :
    0 ≤ offsetProbability E := by
  classical
  rw [offsetProbability_eq_card]
  positivity

theorem offsetProbability_le_one (E : MergedPairs F → Prop) :
    offsetProbability E ≤ 1 := by
  classical
  rw [offsetProbability_eq_card]
  have hpos : (0 : ℝ) < Fintype.card (MergedPairs F) := by positivity
  apply (div_le_one hpos).mpr
  exact_mod_cast Finset.card_filter_le (Finset.univ : Finset (MergedPairs F)) E

theorem offsetProbability_mono {E G : MergedPairs F → Prop}
    (h : ∀ M, E M → G M) : offsetProbability E ≤ offsetProbability G := by
  classical
  rw [offsetProbability_eq_card, offsetProbability_eq_card]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hc : (Finset.univ.filter E).card ≤ (Finset.univ.filter G).card := by
    apply Finset.card_le_card
    intro M hM
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h M (Finset.mem_filter.mp hM).2⟩
  exact_mod_cast hc

theorem selectedProbability_nonneg (w : Kernel F)
    (hw : ∀ M v, 0 ≤ w M v) (E : Configuration F → Prop) :
    0 ≤ selectedProbability w E := by
  unfold selectedProbability
  apply div_nonneg _ (by positivity)
  apply Finset.sum_nonneg
  intro M _
  apply Finset.sum_nonneg
  intro v _
  split_ifs
  · exact hw M v
  · exact le_rfl

theorem selectedProbability_le_of_fixed_offset (w : Kernel F)
    (E : Configuration F → Prop) (r : ℝ)
    (h : ∀ M, (∑ v, if E (configuration M v) then w M v else 0) ≤ r) :
    selectedProbability w E ≤ r := by
  unfold selectedProbability
  have hpos : (0 : ℝ) < Fintype.card (MergedPairs F) := by positivity
  apply (div_le_iff₀ hpos).mpr
  calc
    (∑ M, ∑ v, if E (configuration M v) then w M v else 0) ≤
        ∑ _M : MergedPairs F, r := Finset.sum_le_sum (fun M _ => h M)
    _ = r * Fintype.card (MergedPairs F) := by simp [mul_comm]

theorem selectedProbability_le_one (Q : RetentionRule F) (w : Kernel F) (K : ℝ)
    (hw : KernelConditions Q w K) (E : Configuration F → Prop) :
    selectedProbability w E ≤ 1 := by
  apply selectedProbability_le_of_fixed_offset w E 1
  intro M
  calc
    (∑ v, if E (configuration M v) then w M v else 0) ≤ ∑ v, w M v := by
      apply Finset.sum_le_sum
      intro v _
      split_ifs
      · exact le_rfl
      · exact hw.1 M v
    _ ≤ 1 := hw.2.1 M

theorem selectedProbability_mono (w : Kernel F) (hw : ∀ M v, 0 ≤ w M v)
    {E G : Configuration F → Prop} (h : ∀ C, E C → G C) :
    selectedProbability w E ≤ selectedProbability w G := by
  unfold selectedProbability
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.sum_le_sum
  intro M _
  apply Finset.sum_le_sum
  intro v _
  by_cases hE : E (configuration M v)
  · simp only [hE, h _ hE, ite_true]
    exact le_rfl
  · simp only [hE, ite_false]
    split_ifs
    · exact hw M v
    · exact le_rfl

theorem selected_prescription_and_offset_le
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ)
    (hw : KernelConditions Q w K) (S : Finset (Slot F))
    (t : MergedPairs F → Slot F → TupleCode F) (E : MergedPairs F → Prop) :
    selectedProbability w (fun C => E C.merged ∧
      ∀ s ∈ S, encodeTuple (C.choice s).tuple = t C.merged s) ≤
      (K / Fintype.card F) ^ S.card * offsetProbability E := by
  let r : ℝ := (K / Fintype.card F) ^ S.card
  have hpoint : ∀ M : MergedPairs F,
      (∑ v : Output F, if E M ∧ (∀ s ∈ S, (v s).2 = t M s)
        then w M v else 0) ≤ if E M then r else 0 := by
    intro M
    by_cases hE : E M
    · simpa only [hE, true_and, ite_true] using hw.2.2.2 M S (t M)
    · simp [hE]
  have hsum : (∑ M : MergedPairs F, if E M then r else 0) =
      r * ∑ M : MergedPairs F, if E M then (1 : ℝ) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro M _
    split_ifs <;> simp
  have hform : selectedProbability w (fun C => E C.merged ∧
      ∀ s ∈ S, encodeTuple (C.choice s).tuple = t C.merged s) =
      (∑ M : MergedPairs F, ∑ v : Output F,
        if E M ∧ (∀ s ∈ S, (v s).2 = t M s) then w M v else 0) /
          Fintype.card (MergedPairs F) := by
    unfold selectedProbability
    congr 1
    apply Finset.sum_congr rfl
    intro M _
    apply Finset.sum_congr rfl
    intro v _
    simp [configuration, decodeChoice, encodeTuple, decodeTuple]
  rw [hform]
  calc
    _ ≤ (∑ M : MergedPairs F, if E M then r else 0) /
        Fintype.card (MergedPairs F) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun M _ => hpoint M)) (by positivity)
    _ = r * offsetProbability E := by rw [hsum]; simp [offsetProbability, div_eq_mul_inv, mul_assoc]

theorem selected_prescription_le
    (Q : RetentionRule F) (w : Kernel F) (K : ℝ)
    (hw : KernelConditions Q w K) (S : Finset (Slot F))
    (t : MergedPairs F → Slot F → TupleCode F) :
    selectedProbability w (fun C =>
      ∀ s ∈ S, encodeTuple (C.choice s).tuple = t C.merged s) ≤
      (K / Fintype.card F) ^ S.card := by
  have h := selected_prescription_and_offset_le Q w K hw S t (fun _ => True)
  have hprob : offsetProbability (F := F) (fun _ => True) = 1 := by
    simp [offsetProbability, Fintype.card_ne_zero]
  simpa only [true_and, hprob, mul_one] using h

end
end Balanced.Local.KernelBridge

end OAI
