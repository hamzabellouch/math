import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.TruncatedTupleIntegrable
import OAI.Combinatorics.SharpRamsey.Entropy.MakePair

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.CertificateCover
open SharpRamseyFive.StaticCertificates
open SharpRamseyFive.CertificateEnumeration
open SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.ResidualCertificate
open scoped BigOperators
variable {V H D B : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B]
variable (lines : H → Finset D)
omit [Fintype H] [DecidableEq H] [Fintype D] in
lemma complete_program_weight (rate : D → ℝ≥0) (denom : ℝ) (hd : denom ≠ 0)
    (K : ℕ) (low : Bool) (E : Finset V) (s : State V H D B)
    (c : completePrograms lines K low E s) :
    weight (fun p : B × D => rate p.2) (finish lines K s c.val.2).2 =
      (weight (fun p : B × D => rate p.2) s.2 * denom ^ (Fintype.card V - E.card)) *
        dWeight (Action lines K) (advance lines K) (programCost lines rate denom K low) s c.val.2 := by
  rw [trace_weight lines rate denom hd K low s c.val.2 c.property.1,
    c.property.2.2]
  ring
omit [Fintype D] in

lemma complete_program_sum (rate : D → ℝ≥0) (denom b mass : ℝ)
    (hd : 0 < denom) (hb : 1 ≤ b) (hm : 0 ≤ mass)
    (hmass : ∀ h, ∑ d ∈ lines h, (rate d : ℝ) ≤ mass)
    (K N₁ N₂ : ℕ) (low : Bool)
    (hN₁ : ∀ d, (Finset.univ.filter (fun h => d ∈ lines h)).card ≤ N₁)
    (hN₂ : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun h => d ∈ lines h ∧ e ∈ lines h)).card ≤ N₂)
    (E : Finset V) (s : State V H D B) :
    (∑ c : completePrograms lines K low E s,
      weight (fun p : B × D => rate p.2) (finish lines K s c.val.2).2) ≤
      (weight (fun p : B × D => rate p.2) s.2 * denom ^ (Fintype.card V - E.card)) *
        ∑ n : Fin (Fintype.card V - E.card + 1),
          branchingBound (V := V) (B := B) lines rate denom b mass K N₁ N₂ low ^ n.val := by
  classical
  simp_rw [complete_program_weight lines rate denom hd.ne' K low E s]
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (weight_nonneg _ _) (pow_nonneg hd.le _))
  change (∑ c : {c : AllPrograms lines K E s // CompleteProgram lines K low E s c},
    dWeight (Action lines K) (advance lines K) (programCost lines rate denom K low) s c.val.2) ≤ _
  have hsub := Finset.sum_subtype (p := CompleteProgram lines K low E s)
    (F := completePrograms_fintype lines K low E s)
    (Finset.univ.filter (CompleteProgram lines K low E s)) (fun _ => by simp)
    (fun c : AllPrograms lines K E s => dWeight (Action lines K) (advance lines K)
      (programCost lines rate denom K low) s c.2)
  rw [← hsub, Finset.sum_filter]
  change (∑ c : AllPrograms lines K E s,
    if CompleteProgram lines K low E s c then
      dWeight (Action lines K) (advance lines K) (programCost lines rate denom K low) s c.2
    else 0) ≤ _
  rw [Fintype.sum_sigma]
  apply Finset.sum_le_sum
  intro n _
  apply le_trans _ (program_enumeration lines rate denom b mass hd.le hb hm hmass
    K N₁ N₂ low hN₁ hN₂ n.val s)
  apply Finset.sum_le_sum
  intro w _
  by_cases hc : CompleteProgram lines K low E s ⟨n, w⟩
  · simp only [ite_eq_left hc, ite_eq_left hc.2.1]
    exact le_rfl
  · simp only [ite_eq_right hc]
    split_ifs
    · exact dWeight_nonneg (Action lines K) (advance lines K) _
        (programCost_nonneg lines rate denom hd.le K low) s w
    · exact le_rfl

def badEvent (K J : ℕ) (low : Bool) (E : Finset V) (s : State V H D B)
    (f : V → H) : Set ((B × D) → ℕ) :=
  {ω | Function.Injective f ∧ Coherent lines f (fun r d => ω (r, d) ≠ 0) K E s ∧
    (∀ v ∉ E, Fintype.card B / 2 ≤
      (touchedBatches (fun v => lines (f v)) (fun r d => ω (r, d) ≠ 0) v).card) ∧
    (low = false → ∀ d, (Finset.univ.filter (fun r => ω (r, d) ≠ 0)).card ≤ J)}
omit [Fintype H] [DecidableEq H] in
omit [Fintype D] in

lemma bad_event_cover (K J h : ℕ) (hK : 2 ≤ K) (hh : 0 < h) (low : Bool)
    (hsize : h ≤ (Fintype.card B / 2 - if low then 0 else J) / (2 * K))
    (herr : (Fintype.card V : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2)
    (E : Finset V) (s : State V H D B) (f : V → H) (ω : (B × D) → ℕ)
    (hω : ω ∈ badEvent lines K J low E s f) :
    ∃ c : completePrograms lines K low E s,
      (finish lines K s c.val.2).1 = f ∧ ω ∈ positiveEvent (finish lines K s c.val.2).2 := by
  classical
  have hex : ∃ n, ∃ w : Word lines K n s,
      Segment lines f (fun r d => ω (r, d) ≠ 0) K low E Finset.univ s w ∧
        0 ≤ charge lines K s w ∧ n ≤ Fintype.card V - E.card := by
    cases low with
    | false =>
      exact bad_program_high lines f hω.1 (fun r d => ω (r, d) ≠ 0) K J h hK hh
        hsize E s hω.2.1 hω.2.2.1 (hω.2.2.2 rfl) herr
    | true =>
      apply bad_program_low lines f hω.1 (fun r d => ω (r, d) ≠ 0) K h hK hh
        _ E s hω.2.1 hω.2.2.1 herr
      simpa using hsize
  obtain ⟨n, w, hw, hq, hn⟩ := hex
  have hc : CompleteProgram lines K low E s ⟨⟨n, by omega⟩, w⟩ := by
    refine ⟨hw.2.2, hq, ?_⟩
    change degreeSum lines K s w = Fintype.card V - E.card
    have he := hw.2.1
    simp only [Finset.card_univ] at he
    omega
  refine ⟨⟨⟨⟨n, by omega⟩, w⟩, hc⟩, ?_, ?_⟩
  · funext v
    exact hw.1.1 v (Finset.mem_univ _)
  · intro p hp
    exact hw.1.2.2.1 p hp

theorem bad_completion_bound (rate : D → ℝ≥0) (denom b mass : ℝ)
    (hd : 0 < denom) (hb : 1 ≤ b) (hm : 0 ≤ mass)
    (hmass : ∀ h, ∑ d ∈ lines h, (rate d : ℝ) ≤ mass)
    (K J h N₁ N₂ : ℕ) (hK : 2 ≤ K) (hh : 0 < h) (low : Bool)
    (hsize : h ≤ (Fintype.card B / 2 - if low then 0 else J) / (2 * K))
    (herr : (Fintype.card V : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2)
    (hN₁ : ∀ d, (Finset.univ.filter (fun h => d ∈ lines h)).card ≤ N₁)
    (hN₂ : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun h => d ∈ lines h ∧ e ∈ lines h)).card ≤ N₂)
    (E : Finset V) (s : State V H D B) :
    (∑ f : V → H, (poissonLaw (fun p : B × D => rate p.2)).real
      (badEvent lines K J low E s f)) ≤
      (weight (fun p : B × D => rate p.2) s.2 * denom ^ (Fintype.card V - E.card)) *
        ∑ n : Fin (Fintype.card V - E.card + 1),
          branchingBound (V := V) (B := B) lines rate denom b mass K N₁ N₂ low ^ n.val := by
  classical
  apply le_trans _ (complete_program_sum lines rate denom b mass hd hb hm hmass
    K N₁ N₂ low hN₁ hN₂ E s)
  apply decoded_static_union_bound rate
    (fun c : completePrograms lines K low E s => (finish lines K s c.val.2).2)
    (fun c => (finish lines K s c.val.2).1) (badEvent lines K J low E s)
  · intro f
    exact (Set.to_countable _).measurableSet
  · intro f ω hω
    exact bad_event_cover lines K J h hK hh low hsize herr E s f ω hω

def selectedBadEvent (K J : ℕ) (low : Bool) (E : Finset V) (s : State V H D B)
    (f : V → H) : Set ((B × D) → ℕ) := by
  classical
  exact {ω | Function.Injective f ∧ ∃ hit : B → D → Prop,
    (∀ r d, hit r d → ω (r, d) ≠ 0) ∧ Coherent lines f hit K E s ∧
    (∀ v ∉ E, Fintype.card B / 2 ≤ (touchedBatches (fun v => lines (f v)) hit v).card) ∧
    (low = false → ∀ d, (Finset.univ.filter (fun r => hit r d)).card ≤ J)}
omit [Fintype H] [DecidableEq H] in
omit [Fintype D] in

lemma selected_bad_event_cover (K J h : ℕ) (hK : 2 ≤ K) (hh : 0 < h) (low : Bool)
    (hsize : h ≤ (Fintype.card B / 2 - if low then 0 else J) / (2 * K))
    (herr : (Fintype.card V : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2)
    (E : Finset V) (s : State V H D B) (f : V → H) (ω : (B × D) → ℕ)
    (hω : ω ∈ selectedBadEvent lines K J low E s f) :
    ∃ c : completePrograms lines K low E s,
      (finish lines K s c.val.2).1 = f ∧ ω ∈ positiveEvent (finish lines K s c.val.2).2 := by
  classical
  obtain ⟨hfi, hit, hpos, hco, hbad, htr⟩ := hω
  have hex : ∃ n, ∃ w : Word lines K n s,
      Segment lines f hit K low E Finset.univ s w ∧
        0 ≤ charge lines K s w ∧ n ≤ Fintype.card V - E.card := by
    cases low with
    | false =>
      exact bad_program_high lines f hfi hit K J h hK hh
        hsize E s hco hbad (htr rfl) herr
    | true =>
      apply bad_program_low lines f hfi hit K h hK hh _ E s hco hbad herr
      simpa using hsize
  obtain ⟨n, w, hw, hq, hn⟩ := hex
  have hc : CompleteProgram lines K low E s ⟨⟨n, by omega⟩, w⟩ := by
    refine ⟨hw.2.2, hq, ?_⟩
    change degreeSum lines K s w = Fintype.card V - E.card
    have he := hw.2.1
    simp only [Finset.card_univ] at he
    omega
  refine ⟨⟨⟨⟨n, by omega⟩, w⟩, hc⟩, ?_, ?_⟩
  · funext v
    exact hw.1.1 v (Finset.mem_univ _)
  · intro p hp
    exact hpos p.1 p.2 (hw.1.2.2.1 p hp)

theorem selected_bad_completion_bound (rate : D → ℝ≥0) (denom b mass : ℝ)
    (hd : 0 < denom) (hb : 1 ≤ b) (hm : 0 ≤ mass)
    (hmass : ∀ h, ∑ d ∈ lines h, (rate d : ℝ) ≤ mass)
    (K J h N₁ N₂ : ℕ) (hK : 2 ≤ K) (hh : 0 < h) (low : Bool)
    (hsize : h ≤ (Fintype.card B / 2 - if low then 0 else J) / (2 * K))
    (herr : (Fintype.card V : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2)
    (hN₁ : ∀ d, (Finset.univ.filter (fun h => d ∈ lines h)).card ≤ N₁)
    (hN₂ : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun h => d ∈ lines h ∧ e ∈ lines h)).card ≤ N₂)
    (E : Finset V) (s : State V H D B) :
    (∑ f : V → H, (poissonLaw (fun p : B × D => rate p.2)).real
      (selectedBadEvent lines K J low E s f)) ≤
      (weight (fun p : B × D => rate p.2) s.2 * denom ^ (Fintype.card V - E.card)) *
        ∑ n : Fin (Fintype.card V - E.card + 1),
          branchingBound (V := V) (B := B) lines rate denom b mass K N₁ N₂ low ^ n.val := by
  classical
  apply le_trans _ (complete_program_sum lines rate denom b mass hd hb hm hmass
    K N₁ N₂ low hN₁ hN₂ E s)
  apply decoded_static_union_bound rate
    (fun c : completePrograms lines K low E s => (finish lines K s c.val.2).2)
    (fun c => (finish lines K s c.val.2).1) (selectedBadEvent lines K J low E s)
  · intro f
    exact (Set.to_countable _).measurableSet
  · intro f ω hω
    exact selected_bad_event_cover lines K J h hK hh low hsize herr E s f ω hω

end SharpRamseyFive.CertificateCover

namespace SharpRamseyFive.SelectionBridge
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations SharpRamseyFive.AmbientDesignations
open SharpRamseyFive.CertificateCover SharpRamseyFive.WeightedPrograms
open Classical
variable {D V H C : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype C] [DecidableEq C]
omit [DecidableEq D] in

lemma restriction_preserving (rate : D → ℝ≥0) (lab : D → Option C) (R : ℕ) :
    MeasurePreserving (fun ω : Fin R × D → ℕ => fun i : Block lab R none => ω i)
      (batchMeasure (fun i : Fin R × D => rate i.2))
      (batchMeasure (fun i : Block lab R none => rate i.1.2)) := by
  exact (measurePreserving_eval (fun c : Option C => batchMeasure
    (fun i : Block lab R c => rate i.1.2)) none).comp
      (measurePreserving_partition (fun i : Fin R × D => rate i.2) (fun i => lab i.2))
omit [DecidableEq D] in

lemma integral_restriction (rate : D → ℝ≥0) (lab : D → Option C) (R : ℕ)
    (F : (Block lab R none → ℕ) → ℝ) :
    (∫ z, F z ∂batchMeasure (fun i : Block lab R none => rate i.1.2)) =
      ∫ ω, F (fun i => ω i) ∂batchMeasure (fun i : Fin R × D => rate i.2) := by
  have h := restriction_preserving rate lab R
  rw [← h.map_eq]
  exact integral_map h.measurable.aemeasurable (measurable_of_countable F).aestronglyMeasurable
omit [Fintype D] [DecidableEq V] in

lemma label_none_external (weight : D → ℝ≥0) (s : V → Finset D) (t : ℝ)
    {v : V} {d : D} (hd : d ∈ s v) (he : componentLabel weight s t d = none) :
    External weight s t d := by
  by_contra hn
  have hi := componentLabel_internal weight s t (Finset.mem_filter.mpr ⟨hd,hn⟩)
  rw [he] at hi
  cases hi

noncomputable def selectedHit (weight : D → ℝ≥0) (s : V → Finset D) (t : ℝ)
    {R : ℕ} (ω : Fin R × D → ℕ) (r : Fin R) (d : D) : Prop :=
  componentLabel weight s t d = none ∧ ω (r,d) ≠ 0

lemma touched_equals_shared (weight : D → ℝ≥0) (s : V → Finset D) (t : ℝ)
    (R : ℕ) (ω : Fin R × D → ℕ) (v : V) :
    TupleComponents.hitBatches (touched (componentLabel weight s t) R
      ((strongGraph weight s t).connectedComponentMk v) (s v) (fun i => ω i)) =
      ResidualCertificate.touchedBatches s (selectedHit weight s t ω) v := by
  ext r
  simp only [TupleComponents.hitBatches, touched, Finset.mem_filter, Finset.mem_univ, true_and,
    decide_eq_true_eq, ResidualCertificate.touchedBatches,
    ResidualCertificate.sharedBatches, Finset.mem_inter]
  constructor
  · rintro ⟨d,hd,hpos⟩
    obtain ⟨u,hu,hdiff⟩ := (external_iff_other weight s t hd).mp
      (label_none_external weight s t hd d.property)
    refine ⟨u, ?_, d, ⟨hd,hu⟩, d.property,hpos⟩
    intro he
    subst u
    exact hdiff rfl
  · rintro ⟨u,_,d,⟨hd,_⟩,he,hpos⟩
    exact ⟨⟨d,he⟩,hd,hpos⟩

omit [DecidableEq V] in
lemma selected_trunc (weight : D → ℝ≥0) (s : V → Finset D) (t : ℝ)
    (R J : ℕ) (ω : Fin R × D → ℕ)
    (htr : blockTrunc (componentLabel weight s t) R J none (fun i => ω i) ≠ 0) :
    ∀ d, (Finset.univ.filter (fun r => selectedHit weight s t ω r d)).card ≤ J := by
  intro d
  by_cases hd : componentLabel weight s t d = none
  · have hp : lineTrunc R J (fun r => ω (r,d)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mp htr ⟨d,hd⟩ (Finset.mem_univ _)
    have hh : (Finset.univ.filter (fun r => ω (r,d) ≠ 0)).card < J := by
      by_contra hn
      exact hp (ite_eq_right hn)
    simpa only [selectedHit, hd, true_and] using hh.le
  · simp only [selectedHit, hd, false_and, Finset.filter_false, Finset.card_empty]
    exact Nat.zero_le _

noncomputable def vertexBadMass (weight rate : D → ℝ≥0) (s : V → Finset D) (t : ℝ)
    (R J : ℕ) (A : Finset V) : ℝ :=
  badMass (batchMeasure (fun i : Block (componentLabel weight s t) R none => rate i.1.2))
    (blockTrunc (componentLabel weight s t) R J none)
    (fun v z => BAD (touched (componentLabel weight s t) R
      ((strongGraph weight s t).connectedComponentMk v) (s v) z)) A

omit [Fintype D] [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] in
lemma empty_coherent (lines : H → Finset D) (f g : V → H) (R K : ℕ)
    (E : Finset V) (hit : Fin R → D → Prop) (he : ∀ v ∈ E, g v = f v) :
    Coherent lines f hit K E (g,∅) := by
  refine ⟨he, ?_, ?_, ?_⟩
  · simp [ResidualCertificate.DictionaryInvariant, ResidualCertificate.paidDirections]
  · intro p hp
    exact False.elim (Finset.notMem_empty p hp)
  · simp
omit [Fintype H] [DecidableEq H] in

lemma bad_mass_le_selected_event (weight rate : D → ℝ≥0) (lines : H → Finset D)
    (f g : V → H) (hf : Function.Injective f) (R J K : ℕ) (t : ℝ) (low : Bool)
    (A : Finset V) (he : ∀ v ∈ Finset.univ \ A, g v = f v) :
    vertexBadMass weight rate (lines ∘ f) t R J A ≤
      (StaticCertificates.poissonLaw (fun i : Fin R × D => rate i.2)).real
        (selectedBadEvent lines K J low (Finset.univ \ A) (g,∅) f) := by
  let lab := componentLabel weight (lines ∘ f) t
  let bad := fun v z => BAD (touched lab R
    ((strongGraph weight (lines ∘ f) t).connectedComponentMk v) (lines (f v)) z)
  let T := blockTrunc lab R J none
  let E : Set ((Fin R × D) → ℕ) := selectedBadEvent lines K J low (Finset.univ \ A) (g,∅) f
  have hE : MeasurableSet E := (Set.to_countable _).measurableSet
  change (∫ z, T z * ∏ v ∈ A, badIndicator bad v z
    ∂batchMeasure (fun i : Block lab R none => rate i.1.2)) ≤ _
  rw [integral_restriction rate lab R]
  have hi : Integrable (fun ω : Fin R × D → ℕ =>
      T (fun i => ω i) * ∏ v ∈ A, badIndicator bad v (fun i => ω i))
      (batchMeasure (fun i : Fin R × D => rate i.2)) := by
    apply Integrable.of_bound (measurable_of_countable _).aestronglyMeasurable 1
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs, abs_of_nonneg (badTerm_range T (blockTrunc_range lab R J none)
      bad A (fun i => ω i)).1]
    exact (badTerm_range T (blockTrunc_range lab R J none) bad A (fun i => ω i)).2
  change _ ≤ (batchMeasure (fun i : Fin R × D => rate i.2)).real E
  rw [← integral_indicator_one hE]
  apply integral_mono hi ((integrable_const (1 : ℝ)).indicator hE)
  intro ω
  dsimp only
  by_cases hz : T (fun i => ω i) * ∏ v ∈ A, badIndicator bad v (fun i => ω i) = 0
  · rw [hz]
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  · have ht : T (fun i => ω i) ≠ 0 := (mul_ne_zero_iff.mp hz).1
    have hb : ∀ v ∈ A, bad v (fun i => ω i) := by
      intro v hv
      have hn := Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hz).2 v hv
      by_contra hn'
      exact hn (ite_eq_right hn')
    have hmem : ω ∈ E := by
      refine ⟨hf, selectedHit weight (lines ∘ f) t ω, ?_, ?_, ?_, ?_⟩
      · intro r d hd
        exact hd.2
      · exact empty_coherent lines f g R K (Finset.univ \ A) _ he
      · intro v hv
        have hvA : v ∈ A := by simpa using hv
        have hvb := hb v hvA
        change R / 2 ≤ (TupleComponents.hitBatches (touched lab R
          ((strongGraph weight (lines ∘ f) t).connectedComponentMk v) (lines (f v))
          (fun i => ω i))).card at hvb
        change R / 2 ≤ (TupleComponents.hitBatches (touched
          (componentLabel weight (lines ∘ f) t) R
          ((strongGraph weight (lines ∘ f) t).connectedComponentMk v)
          ((lines ∘ f) v) (fun i => ω i))).card at hvb
        rw [touched_equals_shared weight (lines ∘ f) t R ω v] at hvb
        simpa only [Fintype.card_fin, Function.comp_def] using hvb
      · intro _
        exact selected_trunc weight (lines ∘ f) t R J ω ht
    rw [Set.indicator_of_mem hmem]
    exact (badTerm_range T (blockTrunc_range lab R J none) bad A (fun i => ω i)).2
omit [Fintype D] [Fintype V] [DecidableEq V] in

lemma vertex_injective (weight : D → ℝ≥0) (s : V → Finset D) (t : ℝ) : Function.Injective (vertex weight s t) := by
  intro c d he
  have h := congrArg (strongGraph weight s t).connectedComponentMk he
  simpa only [vertex_color] using h

lemma component_bad_mass_eq_vertex (weight rate : D → ℝ≥0) (s : V → Finset D)
    (t : ℝ) (R J : ℕ) (U : Finset (Components weight s t)) :
    badMass (batchMeasure (fun i : Block (componentLabel weight s t) R none => rate i.1.2))
      (blockTrunc (componentLabel weight s t) R J none)
      (isBad weight s t R) U =
      vertexBadMass weight rate s t R J (U.image (vertex weight s t)) := by
  unfold badMass vertexBadMass
  congr 1
  funext z
  congr 1
  rw [Finset.prod_image (fun _ _ _ _ he => vertex_injective weight s t he)]
  apply Finset.prod_congr rfl
  intro c hc
  simp only [badIndicator, isBad, vertex_color]
  split_ifs with h <;> simp only [h, ite_true, ite_false]

theorem bad_residual_sum_le (weight rate : D → ℝ≥0) (lines : H → Finset D)
    (t : ℝ) (R : ℕ) (denom b mass : ℝ)
    (hd : 0 < denom) (hb : 1 ≤ b) (hm : 0 ≤ mass)
    (hmass : ∀ u, ∑ d ∈ lines u, (rate d : ℝ) ≤ mass)
    (K J h N₁ N₂ : ℕ) (hK : 2 ≤ K) (hh : 0 < h) (low : Bool)
    (hsize : h ≤ (R / 2 - if low then 0 else J) / (2 * K))
    (herr : (Fintype.card V : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2)
    (hN₁ : ∀ d, (Finset.univ.filter (fun u => d ∈ lines u)).card ≤ N₁)
    (hN₂ : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun u => d ∈ lines u ∧ e ∈ lines u)).card ≤ N₂)
    (A : Finset V) (g : V → H) :
    (∑ f : V → H, if Function.Injective f ∧ (∀ v ∉ A, g v = f v) then
      vertexBadMass weight rate (lines ∘ f) t R J A else 0) ≤
      denom ^ A.card * ∑ n : Fin (A.card + 1),
        branchingBound (V := V) (B := Fin R) lines rate denom b mass K N₁ N₂ low ^ n.val := by
  have hbnd := selected_bad_completion_bound (V := V) (B := Fin R)
    lines rate denom b mass hd hb hm hmass K J h N₁ N₂ hK hh low
    (by simpa only [Fintype.card_fin] using hsize) herr hN₁ hN₂
    (Finset.univ \ A) (g,∅)
  have heq : Fintype.card V - (Finset.univ \ A).card = A.card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ A)]
    simp only [Finset.card_univ]
    have := Finset.card_le_card (Finset.subset_univ A)
    simp only [Finset.card_univ] at this
    omega
  rw [Fin.sum_univ_eq_sum_range] at hbnd ⊢
  simp only [heq, StaticCertificates.weight, Finset.prod_empty, one_mul] at hbnd
  apply le_trans _ hbnd
  apply Finset.sum_le_sum
  intro f hf
  split_ifs with hfi
  · apply bad_mass_le_selected_event weight rate lines f g hfi.1 R J K t low A
    intro v hv
    exact hfi.2 v (Finset.mem_sdiff.mp hv).2
  · exact ENNReal.toReal_nonneg

end SharpRamseyFive.SelectionBridge

namespace SharpRamseyFive.SelectionBridge
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations SharpRamseyFive.AmbientDesignations
open SharpRamseyFive.CertificateCover SharpRamseyFive.WeightedPrograms
open Classical
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]

def labelled (f : V → H) (v : V) : H × V := (f v, v)

omit [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] in
lemma labelled_injective (f : V → H) : Function.Injective (labelled f) := by
  intro u v h
  exact congrArg Prod.snd h

omit [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] in
lemma labelled_map_injective : Function.Injective (labelled : (V → H) → (V → H × V)) := by
  intro f g h
  funext v
  exact congrArg Prod.fst (congrFun h v)

end SharpRamseyFive.SelectionBridge
end

end OAI
