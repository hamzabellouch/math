import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.TwoAnchorCrossCost

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
namespace SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.StaticCertificates
open SharpRamseyFive.CertificateEnumeration
open scoped BigOperators NNReal
variable {V H D B : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B]
variable (lines : H → Finset D)
def newEvents (K : ℕ) (s : State V H D B) : Action lines K s → Finset (B × D)
  | .inl _ => ∅
  | .inr (.inl c) => c.2.2.1.requirements
  | .inr (.inr (.inl c)) => c.2.2.2.1.requirements ∪ c.2.2.2.2.1.requirements
  | .inr (.inr (.inr c)) => witnessRequirements c.2.2.2.2.1.val
      (PairDirections lines s c.2.2.1 c.2.2.2.1.val) c.2.2.2.2.2

def newValues (K : ℕ) (s : State V H D B) : Action lines K s → V → H
  | .inl c => Function.update s.1 c.1 c.2
  | .inr (.inl c) => Function.update s.1 c.1 c.2.2.2.val
  | .inr (.inr (.inl c)) => Function.update s.1 c.1 c.2.2.2.2.2.val
  | .inr (.inr (.inr c)) =>
      Function.update (Function.update s.1 c.1 c.2.2.1) c.2.1 c.2.2.2.1.val

def advance (K : ℕ) (s : State V H D B) (a : Action lines K s) : State V H D B :=
  (newValues lines K s a, s.2 ∪ newEvents lines K s a)

def degree (K : ℕ) (s : State V H D B) : Action lines K s → ℕ
  | .inr (.inr (.inr _)) => 2
  | _ => 1

def actionCharge (K : ℕ) (s : State V H D B) : Action lines K s → ℤ
  | .inl _ => -8
  | .inr (.inr (.inl _)) => 1
  | _ => 0

noncomputable def rawCost (rate : D → ℝ≥0) (denom : ℝ) (K : ℕ) (low : Bool)
    (s : State V H D B) : Action lines K s → ℝ
  | .inl _ => 1 / denom
  | .inr (.inl c) => if low then oneCost lines rate denom s c else 0
  | .inr (.inr (.inl c)) => twoCost lines rate denom s c
  | .inr (.inr (.inr c)) => pairCost lines rate denom K s c

noncomputable def programCost (rate : D → ℝ≥0) (denom : ℝ) (K : ℕ) (low : Bool)
    (s : State V H D B) (a : Action lines K s) : ℝ :=
  if s.2.card ≤ K * Fintype.card V then rawCost lines rate denom K low s a else 0

omit [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] in
omit [Fintype D] in
lemma newEvents_fresh (K : ℕ) (s : State V H D B) (a : Action lines K s) :
    Disjoint s.2 (newEvents lines K s a) := by
  rcases a with a | a
  · exact Finset.disjoint_empty_right _
  rcases a with a | a
  · exact a.2.2.1.fresh
  rcases a with a | a
  · exact Finset.disjoint_union_right.mpr ⟨a.2.2.2.1.fresh, a.2.2.2.2.1.fresh⟩
  · apply witnessRequirements_disjoint
    apply Finset.disjoint_left.mpr
    intro d hd hdC
    exact (Finset.mem_sdiff.mp hd).2 hdC

omit [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] in
omit [Fintype D] in
lemma rawCost_nonneg (rate : D → ℝ≥0) (denom : ℝ) (hd : 0 ≤ denom)
    (K : ℕ) (low : Bool) (s : State V H D B) (a : Action lines K s) :
    0 ≤ rawCost lines rate denom K low s a := by
  rcases a with a | a
  · exact div_nonneg zero_le_one hd
  rcases a with a | a
  · change 0 ≤ if low then _ else 0
    split_ifs
    · exact div_nonneg (a.2.2.1.cost_nonneg rate) hd
    · exact le_rfl
  rcases a with a | a
  · exact div_nonneg (mul_nonneg (a.2.2.2.1.cost_nonneg rate)
      (a.2.2.2.2.1.cost_nonneg rate)) hd
  · exact div_nonneg (weight_nonneg _ _) (sq_nonneg _)
omit [DecidableEq V] [Fintype H] [DecidableEq H] in
omit [Fintype D] in

lemma programCost_nonneg (rate : D → ℝ≥0) (denom : ℝ) (hd : 0 ≤ denom)
    (K : ℕ) (low : Bool) (s : State V H D B) (a : Action lines K s) :
    0 ≤ programCost lines rate denom K low s a := by
  unfold programCost
  split_ifs
  · exact rawCost_nonneg lines rate denom hd K low s a
  · exact le_rfl

noncomputable def uniformAnchorBudget (K : ℕ) (mass : ℝ) : ℝ :=
  K * Fintype.card V + Fintype.card B * mass

noncomputable def branchingBound (rate : D → ℝ≥0) (denom b mass : ℝ)
    (K N₁ N₂ : ℕ) (low : Bool) : ℝ :=
  ((Fintype.card V : ℝ) * Fintype.card H / denom) / b ^ 8 +
    (if low then Fintype.card V ^ 2 * (N₁ : ℝ) *
      uniformAnchorBudget (V := V) (B := B) K mass / denom else 0) +
    (Fintype.card V ^ 3 * (N₂ : ℝ) *
      uniformAnchorBudget (V := V) (B := B) K mass ^ 2 / denom) * b +
    Fintype.card V ^ 2 * pairMoment (B := B) lines rate K / denom ^ 2

omit [DecidableEq V] in
omit [Fintype D] [DecidableEq B] in
lemma branchingBound_nonneg (rate : D → ℝ≥0) (denom b mass : ℝ)
    (hd : 0 ≤ denom) (hb : 0 ≤ b) (hm : 0 ≤ mass)
    (K N₁ N₂ : ℕ) (low : Bool) :
    0 ≤ branchingBound (V := V) (B := B) lines rate denom b mass K N₁ N₂ low := by
  unfold branchingBound uniformAnchorBudget
  have hp := pairMoment_nonneg (B := B) lines rate K
  split_ifs <;> positivity

omit [DecidableEq V] [Fintype D] in
lemma discounted_raw_sum (rate : D → ℝ≥0) (denom b : ℝ)
    (K : ℕ) (low : Bool) (s : State V H D B) :
    (∑ a : Action lines K s, rawCost lines rate denom K low s a * b ^ actionCharge lines K s a) =
      ((Fintype.card V : ℝ) * Fintype.card H / denom) / b ^ 8 +
      (if low then ∑ c : OneChoice lines s, oneCost lines rate denom s c else 0) +
      (∑ c : TwoChoice lines s, twoCost lines rate denom s c) * b +
      ∑ c : PairChoice lines K s, pairCost lines rate denom K s c := by
  classical
  change (∑ a : RootChoice (V := V) (H := H) ⊕
      OneChoice lines s ⊕ TwoChoice lines s ⊕ PairChoice lines K s, _) = _
  simp only [Fintype.sum_sum_type, rawCost, actionCharge]
  cases low <;>
    simp only [Bool.false_eq_true, ↓reduceIte,
      zpow_neg, zpow_ofNat, ← Finset.sum_mul, Finset.sum_const,
      Finset.card_univ, Fintype.card_prod, nsmul_eq_mul, RootChoice, Nat.cast_mul] <;> ring

omit [DecidableEq V] in
omit [Fintype D] in

theorem discounted_row_bound (rate : D → ℝ≥0) (denom b mass : ℝ)
    (hd : 0 ≤ denom) (hb : 0 ≤ b) (hm : 0 ≤ mass)
    (hmass : ∀ h, ∑ d ∈ lines h, (rate d : ℝ) ≤ mass)
    (K N₁ N₂ : ℕ) (low : Bool)
    (hN₁ : ∀ d, (Finset.univ.filter (fun h => d ∈ lines h)).card ≤ N₁)
    (hN₂ : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun h => d ∈ lines h ∧ e ∈ lines h)).card ≤ N₂)
    (s : State V H D B) :
    (∑ a : Action lines K s,
      programCost lines rate denom K low s a * b ^ actionCharge lines K s a) ≤
      branchingBound (V := V) (B := B) lines rate denom b mass K N₁ N₂ low := by
  classical
  by_cases hs : s.2.card ≤ K * Fintype.card V
  · simp only [programCost, ite_eq_left hs]
    rw [discounted_raw_sum]
    have hA : anchorBudget rate s mass ≤ uniformAnchorBudget (V := V) (B := B) K mass := by
      unfold anchorBudget uniformAnchorBudget
      apply add_le_add _ le_rfl
      exact_mod_cast hs
    have h1 := sum_oneCost_le lines rate denom hd s mass hmass N₁ hN₁
    have h2 := sum_twoCost_le lines rate denom hd s mass hm hmass N₂ hN₂
    have h3 := sum_pairCost_le lines rate denom K s
    unfold branchingBound
    apply add_le_add
    · apply add_le_add
      · apply add_le_add le_rfl
        split_ifs with hl
        · apply h1.trans
          apply div_le_div_of_nonneg_right _ hd
          exact mul_le_mul_of_nonneg_left hA (by positivity)
        · exact le_rfl
      · apply mul_le_mul_of_nonneg_right _ hb
        apply h2.trans
        apply div_le_div_of_nonneg_right _ hd
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (anchorBudget_nonneg rate s mass hm) hA 2
    · exact h3
  · simp only [programCost, ite_eq_right hs, zero_mul, Finset.sum_const_zero]
    exact branchingBound_nonneg (V := V) lines rate denom b mass hd hb hm K N₁ N₂ low

omit [Fintype D] in

theorem program_enumeration (rate : D → ℝ≥0) (denom b mass : ℝ)
    (hd : 0 ≤ denom) (hb : 1 ≤ b) (hm : 0 ≤ mass)
    (hmass : ∀ h, ∑ d ∈ lines h, (rate d : ℝ) ≤ mass)
    (K N₁ N₂ : ℕ) (low : Bool)
    (hN₁ : ∀ d, (Finset.univ.filter (fun h => d ∈ lines h)).card ≤ N₁)
    (hN₂ : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun h => d ∈ lines h ∧ e ∈ lines h)).card ≤ N₂)
    (n : ℕ) (s : State V H D B) :
    (∑ w : DWord (Action lines K) (advance lines K) n s,
      if 0 ≤ dCharge (Action lines K) (advance lines K) (actionCharge lines K) s w
      then dWeight (Action lines K) (advance lines K) (programCost lines rate denom K low) s w
      else 0) ≤
      branchingBound (V := V) (B := B) lines rate denom b mass K N₁ N₂ low ^ n := by
  classical
  exact constrained_dSum_le (Action lines K) (advance lines K)
    (programCost lines rate denom K low) (programCost_nonneg lines rate denom hd K low)
    (actionCharge lines K) b _ hb
    (branchingBound_nonneg (V := V) lines rate denom b mass hd (by linarith) hm K N₁ N₂ low)
    (discounted_row_bound lines rate denom b mass hd (by linarith) hm hmass K N₁ N₂ low hN₁ hN₂)
    n s _ (fun _ h => h)

end SharpRamseyFive.WeightedPrograms

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace SharpRamseyFive.ResidualCertificate

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def rootProbability : unitInterval := ⟨1 / 20, by norm_num⟩

noncomputable def rootMeasure : Measure (V → Bool) :=
  Measure.pi (fun _ => bernoulliMeasure true false rootProbability)

instance flat_HighMomentRecovered_6 : IsProbabilityMeasure (rootMeasure (V := V)) := by
  unfold rootMeasure
  infer_instance

noncomputable def selected (ω : V → Bool) : Finset V :=
  Finset.univ.filter (fun v => ω v = true)

def voidEvent (W : Finset V) : Set (V → Bool) :=
  (W : Set V).pi (fun _ => {false})

noncomputable def voidIndicator (W : Finset V) (ω : V → Bool) : ℝ :=
  (voidEvent W).indicator (fun _ => 1) ω

noncomputable def badIndicator (W : Finset V) (ω : V → Bool) : ℝ :=
  if (W ∩ selected ω).card < 2 then 1 else 0

omit [DecidableEq V] in
lemma integrable_bounded (f : (V → Bool) → ℝ) (C : ℝ) (hf : ∀ ω, |f ω| ≤ C) :
    Integrable f rootMeasure := by
  apply Integrable.of_bound (measurable_of_countable f).aestronglyMeasurable C
  exact Filter.Eventually.of_forall (by intro ω; simpa only [Real.norm_eq_abs] using hf ω)
omit [DecidableEq V] in

lemma integrable_voidIndicator (W : Finset V) : Integrable (voidIndicator W) rootMeasure := by
  apply integrable_bounded _ 1
  intro ω
  by_cases h : ω ∈ voidEvent W <;> simp [voidIndicator, h]

lemma integrable_badIndicator (W : Finset V) : Integrable (badIndicator W) rootMeasure := by
  apply integrable_bounded _ 1
  intro ω
  simp only [badIndicator]
  split_ifs <;> norm_num

omit [Fintype V] [DecidableEq V] in
lemma voidIndicator_nonneg (W : Finset V) (ω : V → Bool) : 0 ≤ voidIndicator W ω := by
  by_cases h : ω ∈ voidEvent W <;> simp [voidIndicator, h]

lemma badIndicator_nonneg (W : Finset V) (ω : V → Bool) : 0 ≤ badIndicator W ω := by
  simp only [badIndicator]
  split_ifs <;> norm_num

omit [DecidableEq V] in
lemma integral_voidIndicator (W : Finset V) :
    ∫ ω, voidIndicator W ω ∂rootMeasure = (19 / 20 : ℝ) ^ W.card := by
  have hm : MeasurableSet (voidEvent W) := MeasurableSet.pi W.finite_toSet.countable
    (fun _ _ => measurableSet_singleton false)
  have hprob : rootMeasure (voidEvent W) = ENNReal.ofReal ((19 / 20 : ℝ) ^ W.card) := by
    rw [rootMeasure, voidEvent, Measure.pi_pi_finset]
    simp only [bernoulliMeasure_apply rootProbability (measurableSet_singleton false)]
    norm_num [rootProbability, unitInterval.toNNReal, unitInterval.symm]
    congr 1
    exact ENNReal.ofReal_coe_nnreal.symm
  simp only [voidIndicator]
  rw [ integral_indicator_const _ hm, Measure.real, hprob,
    ENNReal.toReal_ofReal (by positivity)]
  simp

lemma erase_void_witness (W : Finset V) (hW : W.Nonempty) (ω : V → Bool)
    (hbad : (W ∩ selected ω).card < 2) :
    ∃ j ∈ W, ω ∈ voidEvent (W.erase j) := by
  have hsmall : (W ∩ selected ω).card ≤ 1 := by omega
  have hc := Finset.card_le_one.mp hsmall
  by_cases he : (W ∩ selected ω).Nonempty
  · obtain ⟨j, hj⟩ := he
    refine ⟨j, (Finset.mem_inter.mp hj).1, ?_⟩
    intro k hk
    apply Set.mem_singleton_iff.mpr
    apply Bool.eq_false_of_not_eq_true
    intro hkt
    have hkm : k ∈ W ∩ selected ω := by
      simp only [Finset.mem_inter, selected, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨(Finset.mem_erase.mp hk).2, hkt⟩
    exact (Finset.mem_erase.mp hk).1 (hc k hkm j hj)
  · obtain ⟨j, hj⟩ := hW
    refine ⟨j, hj, ?_⟩
    intro k hk
    apply Set.mem_singleton_iff.mpr
    apply Bool.eq_false_of_not_eq_true
    intro hkt
    apply he
    refine ⟨k, ?_⟩
    simp only [Finset.mem_inter, selected, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨(Finset.mem_erase.mp hk).2, hkt⟩

lemma badIndicator_le_erase_void (W : Finset V) (hW : W.Nonempty) (ω : V → Bool) :
    badIndicator W ω ≤ ∑ j ∈ W, voidIndicator (W.erase j) ω := by
  unfold badIndicator
  split_ifs with hb
  · obtain ⟨j, hj, hv⟩ := erase_void_witness W hW ω hb
    have hle := Finset.single_le_sum (f := fun j => voidIndicator (W.erase j) ω)
      (fun j _ => voidIndicator_nonneg _ _) hj
    simpa only [voidIndicator, Set.indicator_of_mem hv] using hle
  · exact Finset.sum_nonneg (fun j _ => voidIndicator_nonneg _ _)

lemma integral_badIndicator_le (W : Finset V) (hW : W.Nonempty) :
    ∫ ω, badIndicator W ω ∂rootMeasure ≤
      W.card * (19 / 20 : ℝ) ^ (W.card - 1) := by
  calc
    _ ≤ ∫ ω, ∑ j ∈ W, voidIndicator (W.erase j) ω ∂rootMeasure :=
      integral_mono (integrable_badIndicator W)
        (integrable_finsetSum _ (fun j _ => integrable_voidIndicator _))
        (badIndicator_le_erase_void W hW)
    _ = ∑ j ∈ W, (19 / 20 : ℝ) ^ (W.card - 1) := by
      rw [integral_finsetSum _ (fun j _ => integrable_voidIndicator _)]
      apply Finset.sum_congr rfl
      intro j hj
      rw [integral_voidIndicator, Finset.card_erase_of_mem hj]
    _ = _ := by simp

omit [DecidableEq V] in
lemma indicator_selected (ω : V → Bool) :
    ((selected ω).card : ℝ) = ∑ v : V, if ω v = true then (1 : ℝ) else 0 := by
  symm
  exact Finset.sum_boole _ _
omit [DecidableEq V] in

lemma integrable_selected_card :
    Integrable (fun ω : V → Bool => ((selected ω).card : ℝ)) rootMeasure := by
  simp_rw [indicator_selected]
  apply integrable_finsetSum
  intro v hv
  apply integrable_bounded _ 1
  intro ω
  split_ifs <;> norm_num
omit [DecidableEq V] in

lemma integral_selected_card :
    ∫ ω : V → Bool, ((selected ω).card : ℝ) ∂rootMeasure = (Fintype.card V : ℝ) / 20 := by
  simp_rw [indicator_selected]
  rw [integral_finsetSum]
  · have hv (v : V) :
        (∫ ω : V → Bool, if ω v = true then (1 : ℝ) else 0 ∂rootMeasure) = 1 / 20 := by
      rw [rootMeasure, integral_comp_eval (μ := fun _ : V => bernoulliMeasure true false rootProbability) (i := v) (f := fun a : Bool => if a = true then (1 : ℝ) else 0)
        (measurable_of_countable _).aestronglyMeasurable,
        integral_bernoulliMeasure]
      norm_num [rootProbability]
    simp_rw [hv]
    simp [div_eq_mul_inv]
  · intro v hv
    apply integrable_bounded _ 1
    intro ω
    split_ifs <;> norm_num

theorem exists_small_root_set (W : V → Finset V) {k : ℕ} (hk : 0 < k)
    (hW : ∀ v, (W v).card = k)
    (herr : (Fintype.card V : ℝ) * k * (19 / 20 : ℝ) ^ (k - 1) < 1 / 2) :
    ∃ roots : Finset V, 10 * roots.card ≤ Fintype.card V ∧
      ∀ v, 2 ≤ (W v ∩ roots).card := by
  classical
  by_cases hn : Fintype.card V = 0
  · have : IsEmpty V := Fintype.card_eq_zero_iff.mp hn
    exact ⟨∅, by simp [], fun v => isEmptyElim v⟩
  have hnpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast (Nat.pos_of_ne_zero hn)
  let F : (V → Bool) → ℝ := fun ω =>
    (10 / Fintype.card V : ℝ) * (selected ω).card + ∑ v, badIndicator (W v) ω
  have hFi : Integrable F rootMeasure :=
    (integrable_selected_card.const_mul _).add
      (integrable_finsetSum _ (fun v _ => integrable_badIndicator (W v)))
  have hFint : ∫ ω, F ω ∂rootMeasure < 1 := by
    have he (v : V) : ∫ ω, badIndicator (W v) ω ∂rootMeasure ≤
        k * (19 / 20 : ℝ) ^ (k - 1) := by
      simpa only [hW] using integral_badIndicator_le (W v) (Finset.card_pos.mp (by rw [hW v]; exact hk))
    have sumle : ∑ v : V, (∫ ω, badIndicator (W v) ω ∂rootMeasure) ≤
        (Fintype.card V : ℝ) * k * (19 / 20 : ℝ) ^ (k - 1) := by
      calc
        _ ≤ ∑ _v : V, (k : ℝ) * (19 / 20 : ℝ) ^ (k - 1) := Finset.sum_le_sum (fun v _ => he v)
        _ = _ := by simp; ring
    have hc : (10 / Fintype.card V : ℝ) * ((Fintype.card V : ℝ) / 20) = 1 / 2 := by
      field_simp
      ; ring
    dsimp [F]
    rw [integral_add (integrable_selected_card.const_mul _)
      (integrable_finsetSum _ (fun v _ => integrable_badIndicator (W v))),
      integral_const_mul, integral_selected_card, integral_finsetSum _
        (fun v _ => integrable_badIndicator (W v)), hc]
    linarith
  have hex : ∃ ω, F ω < 1 := by
    by_contra h
    push Not at h
    have hle := integral_mono (integrable_const (1 : ℝ)) hFi h
    simp only [integral_const] at hle
    simp at hle
    linarith
  obtain ⟨ω, hω⟩ := hex
  have hsum : 0 ≤ ∑ v : V, badIndicator (W v) ω :=
    Finset.sum_nonneg (fun v _ => badIndicator_nonneg _ _)
  have hcost : 0 ≤ (10 / Fintype.card V : ℝ) * (selected ω).card := by positivity
  refine ⟨selected ω, ?_, ?_⟩
  · have ht : (10 / Fintype.card V : ℝ) * (selected ω).card < 1 := by dsimp [F] at hω; linarith
    have hcard : (10 : ℝ) * (selected ω).card ≤ Fintype.card V := by
      have := (mul_lt_mul_iff_right₀ hnpos).mpr ht
      field_simp at this
      nlinarith
    exact_mod_cast hcard
  · intro v
    by_contra hv
    have hbad : badIndicator (W v) ω = 1 := by simp [badIndicator, show (W v ∩ selected ω).card < 2 by omega]
    have hle := Finset.single_le_sum (f := fun v => badIndicator (W v) ω)
      (fun v _ => badIndicator_nonneg _ _) (Finset.mem_univ v)
    rw [hbad] at hle
    dsimp [F] at hω
    linarith

section WitnessMatching

variable {E N D : Type*} [DecidableEq E] [DecidableEq N] [DecidableEq D]

theorem exists_distinct_witnesses (s : Finset E) (neighbor : E → N) (direction : E → D)
    (K : ℕ) (hn : ∀ n, (s.filter (fun e => neighbor e = n)).card ≤ K)
    (hd : ∀ d, (s.filter (fun e => direction e = d)).card ≤ K) :
    ∃ t ⊆ s, Set.InjOn neighbor (t : Set E) ∧ Set.InjOn direction (t : Set E) ∧
      s.card ≤ 2 * K * t.card := by
  classical
  let family : Finset (Finset E) := s.powerset.filter (fun t =>
    Set.InjOn neighbor (t : Set E) ∧ Set.InjOn direction (t : Set E))
  have hempty : ∅ ∈ family := by simp [family, Set.injOn_empty]
  obtain ⟨t, htf, hmax⟩ := Finset.exists_max_image family Finset.card ⟨∅, hempty⟩
  have ht : t ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp htf).1
  have hinj := (Finset.mem_filter.mp htf).2
  have hcover (e : E) (he : e ∈ s) :
      ∃ a ∈ t, neighbor e = neighbor a ∨ direction e = direction a := by
    by_contra h
    push Not at h
    have hen : e ∉ t := by
      intro het
      exact (h e het).1 rfl
    have hnnew : Set.InjOn neighbor (↑(insert e t) : Set E) := by
      rw [Finset.coe_insert, Set.injOn_insert hen]
      refine ⟨hinj.1, ?_⟩
      rintro ⟨a, ha, hea⟩
      exact (h a ha).1 hea.symm
    have hdnew : Set.InjOn direction (↑(insert e t) : Set E) := by
      rw [Finset.coe_insert, Set.injOn_insert hen]
      refine ⟨hinj.2, ?_⟩
      rintro ⟨a, ha, hea⟩
      exact (h a ha).2 hea.symm
    have hnew : insert e t ∈ family := by
      simp only [family, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.insert_subset he ht, hnnew, hdnew⟩
    have := hmax _ hnew
    rw [Finset.card_insert_of_notMem hen] at this
    omega
  refine ⟨t, ht, hinj.1, hinj.2, ?_⟩
  have hsub : s ⊆ t.biUnion (fun a =>
      (s.filter (fun e => neighbor e = neighbor a)) ∪
      (s.filter (fun e => direction e = direction a))) := by
    intro e he
    obtain ⟨a, ha, hor⟩ := hcover e he
    apply Finset.mem_biUnion.mpr
    refine ⟨a, ha, ?_⟩
    simpa only [Finset.mem_union, Finset.mem_filter, and_or_left] using
      And.intro he hor
  calc
    s.card ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ a ∈ t, ((s.filter (fun e => neighbor e = neighbor a)) ∪
        (s.filter (fun e => direction e = direction a))).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ t, 2 * K := by
      apply Finset.sum_le_sum
      intro a ha
      exact (Finset.card_union_le _ _).trans (by have := hn (neighbor a); have := hd (direction a); omega)
    _ = 2 * K * t.card := by simp [Nat.mul_comm]

end WitnessMatching
end SharpRamseyFive.ResidualCertificate
end

end OAI
