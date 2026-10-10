import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.AnchorEventsRealized

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
omit [Fintype V] [Fintype H] [DecidableEq H] [Fintype D] in
lemma make_pair (f : V → H) (hf : Function.Injective f) (hit : B → D → Prop)
    (K : ℕ) (hK : 2 ≤ K) (low : Bool) (E : Finset V) (s : State V H D B)
    (hs : Coherent lines f hit K E s) (v u : V) (hv : v ∉ E) (hu : u ∉ E) (hne : v ≠ u)
    (hp : K ≤ (sharedBatches (outsideDirections (fun v => lines (f v)) E) hit v u).card) :
    ∃ a : Action lines K s,
      Coherent lines f hit K (insert v (insert u E)) (advance lines K s a) ∧
      (insert v (insert u E)).card = E.card + degree lines K s a ∧
      Enabled lines K low s a ∧ actionCharge lines K s a = 0 := by
  classical
  obtain ⟨T, d, hT, hd, _, _, _, _⟩ :=
    pair_step_witnesses (fun v => lines (f v)) hit E s.2 v u K hs.2.1 hs.2.2.1 hp
  have hmem (r : T) : d r ∈ PairDirections lines s (f v) (f u) := by
    apply Finset.mem_sdiff.mpr
    refine ⟨(hd r).1, ?_⟩
    intro hc
    exact (hd r).2.1 (hs.2.1 hc)
  let c : PairChoice lines K s := ⟨v, u, f v, ⟨f u, fun he => hne (hf he.symm)⟩,
    ⟨T, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hT⟩⟩, fun r => ⟨d r, hmem r⟩⟩
  let a : Action lines K s := .inr (.inr (.inr c))
  have hv' : v ∉ insert u E := by simp [hne, hv]
  have hc : (insert v (insert u E)).card = E.card + degree lines K s a := by
    simp [a, degree, Finset.card_insert_of_notMem hv', Finset.card_insert_of_notMem hu,
      Nat.add_assoc]
  refine ⟨a, ?_, hc, ?_, rfl⟩
  · apply coherent_step lines f hit K hK E (insert v (insert u E)) s hs a
      ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _)) _ _ _ hc
    · have hu' := agrees_update f (insert v E)
        (Function.update s.1 v (f v), s.2) (agrees_update f E s hs.1 v s.2) u
        (advance lines K s a).2
      simpa only [a, c, advance, newValues, Finset.insert_comm] using hu'
    · intro z hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_insert_self _ _, (Finset.mem_inter.mp (hd r).1).1⟩
    · intro p hp
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hp
      exact (hd r).2.2
  · intro c' he
    simp [a] at he
omit [Fintype V] [Fintype H] [DecidableEq H] in
omit [Fintype D] in

lemma make_root (f : V → H) (hit : B → D → Prop) (K : ℕ) (hK : 2 ≤ K)
    (low : Bool) (E : Finset V) (s : State V H D B) (hs : Coherent lines f hit K E s)
    (v : V) (hv : v ∉ E) :
    ∃ a : Action lines K s, Coherent lines f hit K (insert v E) (advance lines K s a) ∧
      (insert v E).card = E.card + degree lines K s a ∧
      Enabled lines K low s a ∧ actionCharge lines K s a = -8 := by
  let a : Action lines K s := .inl (v, f v)
  have hc : (insert v E).card = E.card + degree lines K s a := by
    simp [a, degree, Finset.card_insert_of_notMem hv]
  refine ⟨a, ?_, hc, ?_, rfl⟩
  · apply coherent_step lines f hit K hK E (insert v E) s hs a
      (Finset.subset_insert _ _) (agrees_update f E s hs.1 v _) _ _ hc
    · simp [a, newEvents, paidDirections]
    · simp [a, newEvents, Realized]
  · intro c' he
    simp [a] at he

abbrev Word (K : ℕ) := DWord (Action (V := V) (B := B) lines K) (advance lines K)
abbrev finish (K : ℕ) {n : ℕ} (s : State V H D B) (w : Word lines K n s) :=
  dFinish (Action lines K) (advance lines K) s w
abbrev charge (K : ℕ) {n : ℕ} (s : State V H D B) (w : Word lines K n s) :=
  dCharge (Action lines K) (advance lines K) (actionCharge lines K) s w

 def degreeSum (K : ℕ) : {n : ℕ} → (s : State V H D B) → Word lines K n s → ℕ
  | 0, _, _ => 0
  | _ + 1, s, w => degree lines K s w.1 + degreeSum K (advance lines K s w.1) w.2

 def TraceOK (K : ℕ) (low : Bool) :
    {n : ℕ} → (s : State V H D B) → Word lines K n s → Prop
  | 0, _, _ => True
  | _ + 1, s, w => s.2.card ≤ K * Fintype.card V ∧
      Enabled lines K low s w.1 ∧ TraceOK K low (advance lines K s w.1) w.2

 def append (K : ℕ) {m : ℕ} : {n : ℕ} → (s : State V H D B) →
    (w : Word lines K n s) → Word lines K m (finish lines K s w) → Word lines K (m + n) s
  | 0, _, _, w' => w'
  | _ + 1, s, w, w' => ⟨w.1, append K (advance lines K s w.1) w.2 w'⟩

omit [Fintype V] [Fintype H] [DecidableEq H] [Fintype D] in
lemma finish_append (K : ℕ) {m n : ℕ} (s : State V H D B)
    (w : Word lines K n s) (w' : Word lines K m (finish lines K s w)) :
    finish lines K s (append lines K s w w') = finish lines K (finish lines K s w) w' := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact ih _ w.2 w'

omit [Fintype V] [Fintype H] [DecidableEq H] [Fintype D] in
lemma degreeSum_append (K : ℕ) {m n : ℕ} (s : State V H D B)
    (w : Word lines K n s) (w' : Word lines K m (finish lines K s w)) :
    degreeSum lines K s (append lines K s w w') =
      degreeSum lines K s w + degreeSum lines K (finish lines K s w) w' := by
  induction n generalizing s with
  | zero => simp only [append, degreeSum, finish, dFinish, Nat.zero_add]
  | succ n ih =>
    simpa only [append, degreeSum, finish, dFinish, Nat.add_assoc] using
      congrArg (fun t => degree lines K s w.1 + t) (ih (advance lines K s w.1) w.2 w')

omit [Fintype V] [Fintype H] [DecidableEq H] [Fintype D] in
lemma charge_append (K : ℕ) {m n : ℕ} (s : State V H D B)
    (w : Word lines K n s) (w' : Word lines K m (finish lines K s w)) :
    charge lines K s (append lines K s w w') =
      charge lines K s w + charge lines K (finish lines K s w) w' := by
  induction n generalizing s with
  | zero => simp only [append, charge, dCharge, finish, dFinish, zero_add]
  | succ n ih =>
    simpa only [append, charge, dCharge, finish, dFinish, add_assoc] using
      congrArg (fun t => actionCharge lines K s w.1 + t) (ih (advance lines K s w.1) w.2 w')

omit [Fintype H] [DecidableEq H] [Fintype D] in
lemma traceOK_append (K : ℕ) (low : Bool) {m n : ℕ} (s : State V H D B)
    (w : Word lines K n s) (w' : Word lines K m (finish lines K s w))
    (h : TraceOK lines K low s w) (h' : TraceOK lines K low (finish lines K s w) w') :
    TraceOK lines K low s (append lines K s w w') := by
  induction n generalizing s with
  | zero => exact h'
  | succ n ih => exact ⟨h.1, h.2.1, ih _ w.2 w' h.2.2 h'⟩

omit [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq B] in
lemma one_le_degree (K : ℕ) (s : State V H D B) (a : Action lines K s) :
    1 ≤ degree lines K s a := by
  rcases a with a | a
  · exact le_rfl
  rcases a with a | a
  · exact le_rfl
  rcases a with a | a
  · exact le_rfl
  · norm_num [degree]
omit [Fintype V] [Fintype H] [DecidableEq H] [Fintype D] in

lemma length_le_degreeSum (K : ℕ) {n : ℕ} (s : State V H D B) (w : Word lines K n s) :
    n ≤ degreeSum lines K s w := by
  induction n generalizing s with
  | zero => exact le_rfl
  | succ n ih =>
    have h1 := one_le_degree lines K s w.1
    have h2 := ih _ w.2
    change n + 1 ≤ _ + _
    omega
omit [Fintype H] [DecidableEq H] in
omit [Fintype D] in

lemma trace_weight (rate : D → ℝ≥0) (denom : ℝ) (hd : denom ≠ 0)
    (K : ℕ) (low : Bool) {n : ℕ} (s : State V H D B) (w : Word lines K n s)
    (hw : TraceOK lines K low s w) :
    weight (fun p : B × D => rate p.2) (finish lines K s w).2 =
      weight (fun p : B × D => rate p.2) s.2 *
        dWeight (Action lines K) (advance lines K) (programCost lines rate denom K low) s w *
          denom ^ degreeSum lines K s w := by
  induction n generalizing s with
  | zero => simp [finish, dFinish, dWeight, degreeSum]
  | succ n ih =>
    change weight _ (finish lines K (advance lines K s w.1) w.2).2 = _
    rw [ih _ w.2 hw.2.2, step_weight lines rate denom hd K low s w.1 hw.2.1 hw.1]
    simp only [dWeight, degreeSum, pow_add]
    ring

 def Segment (f : V → H) (hit : B → D → Prop) (K : ℕ) (low : Bool)
    (E F : Finset V) (s : State V H D B) {n : ℕ} (w : Word lines K n s) : Prop :=
  Coherent lines f hit K F (finish lines K s w) ∧
    F.card = E.card + degreeSum lines K s w ∧ TraceOK lines K low s w

omit [Fintype H] [DecidableEq H] [Fintype D] in
lemma segment_empty (f : V → H) (hit : B → D → Prop) (K : ℕ) (low : Bool)
    (E : Finset V) (s : State V H D B) (hs : Coherent lines f hit K E s) :
    Segment lines f hit K low E E s (n := 0) (PUnit.unit : Word lines K 0 s) := by
  exact ⟨hs, by simp [degreeSum], trivial⟩

omit [Fintype H] [DecidableEq H] [Fintype D] in
lemma segment_single (f : V → H) (hit : B → D → Prop) (K : ℕ) (low : Bool)
    (E F : Finset V) (s : State V H D B) (hs : Coherent lines f hit K E s)
    (a : Action lines K s) (hf : Coherent lines f hit K F (advance lines K s a))
    (hc : F.card = E.card + degree lines K s a) (he : Enabled lines K low s a) :
    Segment lines f hit K low E F s (n := 1) (⟨a, PUnit.unit⟩ : Word lines K 1 s) := by
  refine ⟨hf, ?_, ?_⟩
  · simpa [degreeSum] using hc
  · exact ⟨hs.2.2.2.trans (Nat.mul_le_mul_left K (Finset.card_le_univ E)), he, trivial⟩
omit [Fintype H] [DecidableEq H] [Fintype D] in

lemma segment_append (f : V → H) (hit : B → D → Prop) (K : ℕ) (low : Bool)
    (E F G : Finset V) {m n : ℕ} (s : State V H D B)
    (w : Word lines K n s) (w' : Word lines K m (finish lines K s w))
    (h : Segment lines f hit K low E F s w)
    (h' : Segment lines f hit K low F G (finish lines K s w) w') :
    Segment lines f hit K low E G s (append lines K s w w') := by
  refine ⟨?_, ?_, traceOK_append lines K low s w w' h.2.2 h'.2.2⟩
  · rw [finish_append]; exact h'.1
  · rw [degreeSum_append, ← Nat.add_assoc, ← h.2.1]
    exact h'.2.1
omit [Fintype V] [Fintype H] [DecidableEq H] in
omit [Fintype D] in

lemma make_encoding (f : V → H) (hf : Function.Injective f) (hit : B → D → Prop)
    (K : ℕ) (hK : 2 ≤ K) (low : Bool) {E F : Finset V}
    (h : EncodingStep (fun v => lines (f v)) hit (if low then 1 else 2) K E F)
    (s : State V H D B) (hs : Coherent lines f hit K E s) :
    ∃ a : Action lines K s, Coherent lines f hit K F (advance lines K s a) ∧
      F.card = E.card + degree lines K s a ∧ Enabled lines K low s a ∧
        0 ≤ actionCharge lines K s a := by
  cases h with
  | anchor v hv ha =>
    cases low with
    | false =>
      obtain ⟨a, hh, hc, he, hq⟩ := make_two lines f hit K hK false E s hs v hv ha
      exact ⟨a, hh, hc, he, by omega⟩
    | true =>
      obtain ⟨a, hh, hc, he, hq⟩ := make_one lines f hit K hK E s hs v hv ha
      exact ⟨a, hh, hc, he, by omega⟩
  | pair v u hv hu hne hp =>
    obtain ⟨a, hh, hc, he, hq⟩ := make_pair lines f hf hit K hK low E s hs v u hv hu hne hp
    exact ⟨a, hh, hc, he, by omega⟩

omit [Fintype H] [DecidableEq H] in
omit [Fintype D] in

theorem encoding_path_program (f : V → H) (hf : Function.Injective f)
    (hit : B → D → Prop) (K : ℕ) (hK : 2 ≤ K) (low : Bool) {E F : Finset V}
    (h : Relation.ReflTransGen (EncodingStep (fun v => lines (f v)) hit
      (if low then 1 else 2) K) E F)
    (s : State V H D B) (hs : Coherent lines f hit K E s) :
    ∃ n, ∃ w : Word lines K n s, Segment lines f hit K low E F s w ∧
      0 ≤ charge lines K s w := by
  induction h with
  | refl => exact ⟨0, PUnit.unit, segment_empty lines f hit K low E s hs, le_rfl⟩
  | @tail F G h hFG ih =>
    obtain ⟨n, w, hw, hq⟩ := ih
    obtain ⟨a, ha, hc, he, hqa⟩ := make_encoding lines f hf hit K hK low hFG
      (finish lines K s w) hw.1
    let w' : Word lines K 1 (finish lines K s w) := ⟨a, PUnit.unit⟩
    refine ⟨1 + n, append lines K s w w', ?_, ?_⟩
    · exact segment_append lines f hit K low E F G s w w' hw
        (segment_single lines f hit K low F G _ hw.1 a ha hc he)
    · rw [charge_append]
      exact add_nonneg hq (by simpa [w', charge, dCharge] using hqa)

omit [Fintype H] [DecidableEq H] [Fintype D] in

lemma encode_set (f : V → H) (hit : B → D → Prop) (K : ℕ) (low : Bool)
    (E R : Finset V) (s : State V H D B) (hs : Coherent lines f hit K E s) (c : ℤ)
    (hdis : Disjoint E R)
    (hmake : ∀ F : Finset V, E ⊆ F → ∀ s' : State V H D B,
      Coherent lines f hit K F s' → ∀ v ∈ R, v ∉ F →
      ∃ a : Action lines K s', Coherent lines f hit K (insert v F) (advance lines K s' a) ∧
        (insert v F).card = F.card + degree lines K s' a ∧
        Enabled lines K low s' a ∧ actionCharge lines K s' a = c) :
    ∃ n, ∃ w : Word lines K n s, Segment lines f hit K low E (E ∪ R) s w ∧
      charge lines K s w = c * R.card := by
  classical
  induction R using Finset.induction with
  | empty =>
    refine ⟨0, PUnit.unit, ?_, ?_⟩
    · simpa using segment_empty lines f hit K low E s hs
    · simp [charge, dCharge]
  | @insert v R hvR ih =>
    have hdis' : Disjoint E R := hdis.mono_right (Finset.subset_insert _ _)
    obtain ⟨n, w, hw, hq⟩ := ih hdis' (by
      intro F hEF s' hs' u hu hfu
      exact hmake F hEF s' hs' u (Finset.mem_insert_of_mem hu) hfu)
    have hvE : v ∉ E := fun hvE => Finset.disjoint_left.mp hdis hvE (Finset.mem_insert_self _ _)
    have hvF : v ∉ E ∪ R := by simp [hvE, hvR]
    obtain ⟨a, ha, hc, he, hqa⟩ := hmake (E ∪ R) Finset.subset_union_left
      (finish lines K s w) hw.1 v (Finset.mem_insert_self _ _) hvF
    let w' : Word lines K 1 (finish lines K s w) := ⟨a, PUnit.unit⟩
    refine ⟨1 + n, append lines K s w w', ?_, ?_⟩
    · have hh := segment_append lines f hit K low E (E ∪ R) (insert v (E ∪ R)) s w w' hw
        (segment_single lines f hit K low (E ∪ R) _ _ hw.1 a ha hc he)
      simpa only [Finset.union_insert] using hh
    · rw [charge_append, hq]
      change c * (R.card : ℤ) + (actionCharge lines K _ a + 0) = _
      rw [hqa, Finset.card_insert_of_notMem hvR, Nat.cast_add, Nat.cast_one]
      ring
omit [Fintype H] [DecidableEq H] in
omit [Fintype D] in

lemma residual_program (f : V → H) (hit : B → D → Prop) (K : ℕ) (hK : 2 ≤ K)
    (low : Bool) (F : Finset V) (s : State V H D B) (hs : Coherent lines f hit K F s)
    (roots : Finset {v // v ∉ F})
    (hsize : 10 * roots.card ≤ Fintype.card {v // v ∉ F})
    (hroot : ∀ v, ∃ u ∈ roots, ∃ w ∈ roots, u ≠ w ∧ u ≠ v ∧ w ≠ v ∧
      ∃ d ∈ survivingDirections (fun v => lines (f v)) F v ∩
          survivingDirections (fun v => lines (f v)) F u,
      ∃ e ∈ survivingDirections (fun v => lines (f v)) F v ∩
          survivingDirections (fun v => lines (f v)) F w,
        d ≠ e ∧ (∃ r, hit r d) ∧ (∃ r, hit r e)) :
    ∃ n, ∃ w : Word lines K n s, Segment lines f hit K low F Finset.univ s w ∧
      0 ≤ charge lines K s w := by
  classical
  let R : Finset V := roots.image Subtype.val
  have hRc : R.card = roots.card := by
    dsimp [R]
    apply Finset.card_image_of_injective
    exact Subtype.val_injective
  have hdis : Disjoint F R := by
    apply Finset.disjoint_left.mpr
    intro v hv hR
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hR
    exact u.property hv
  obtain ⟨n, w, hw, hq⟩ := encode_set lines f hit K low F R s hs (-8) hdis (by
    intro G hFG s' hs' v hv hvg
    exact make_root lines f hit K hK low G s' hs' v hvg)
  let NR : Finset V := Finset.univ \ (F ∪ R)
  have hdisNR : Disjoint (F ∪ R) NR := Finset.disjoint_sdiff
  have hmake : ∀ G : Finset V, F ∪ R ⊆ G → ∀ s' : State V H D B,
      Coherent lines f hit K G s' → ∀ v ∈ NR, v ∉ G →
      ∃ a : Action lines K s', Coherent lines f hit K (insert v G) (advance lines K s' a) ∧
        (insert v G).card = G.card + degree lines K s' a ∧
        Enabled lines K low s' a ∧ actionCharge lines K s' a = 1 := by
    intro G hFG s' hs' v hv hvg
    have hvF : v ∉ F := fun hvF => (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_left R hvF)
    obtain ⟨u, hu, u', hu', _, _, _, d, hd, e, he, hde, hdp, hep⟩ := hroot ⟨v, hvF⟩
    have hdv : d ∈ lines (f v) := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hd).1).1
    have hdu : d ∈ lines (f u.val) := (Finset.mem_sdiff.mp (Finset.mem_inter.mp hd).2).1
    have hev : e ∈ lines (f v) := (Finset.mem_sdiff.mp (Finset.mem_inter.mp he).1).1
    have heu : e ∈ lines (f u'.val) := (Finset.mem_sdiff.mp (Finset.mem_inter.mp he).2).1
    have hdE : d ∈ encodedDirections (fun v => lines (f v)) G :=
      Finset.mem_biUnion.mpr ⟨u.val, hFG (Finset.mem_union_right F
        (Finset.mem_image_of_mem Subtype.val hu)), hdu⟩
    have heE : e ∈ encodedDirections (fun v => lines (f v)) G :=
      Finset.mem_biUnion.mpr ⟨u'.val, hFG (Finset.mem_union_right F
        (Finset.mem_image_of_mem Subtype.val hu')), heu⟩
    apply make_two lines f hit K hK low G s' hs' v hvg
    apply Finset.one_lt_card.mpr
    exact ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hdv, hdE⟩, hdp⟩,
      e, Finset.mem_filter.mpr ⟨Finset.mem_inter.mpr ⟨hev, heE⟩, hep⟩, hde⟩
  obtain ⟨m, w', hw', hq'⟩ := encode_set lines f hit K low (F ∪ R) NR
    (finish lines K s w) hw.1 1 hdisNR hmake
  have hfull : (F ∪ R) ∪ NR = Finset.univ := by
    ext v
    simp only [NR, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
    tauto
  refine ⟨m + n, append lines K s w w', ?_, ?_⟩
  · simpa only [hfull] using segment_append lines f hit K low F (F ∪ R) _ s w w' hw hw'
  · rw [charge_append, hq, hq', one_mul]
    have hr : Fintype.card {v // v ∉ F} = Fintype.card V - F.card := by
      rw [Fintype.card_subtype_compl]
      simp
    have hc : NR.card + (F.card + R.card) = Fintype.card V := by
      have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (F ∪ R))
      simpa only [NR, Finset.card_univ, Finset.card_union_of_disjoint hdis] using hh
    rw [← hRc, hr] at hsize
    omega

omit [Fintype H] [DecidableEq H] in
omit [Fintype D] in

theorem bad_program_high (f : V → H) (hf : Function.Injective f)
    (hit : B → D → Prop) [∀ r d, Decidable (hit r d)] (K J h : ℕ) (hK : 2 ≤ K) (hh : 0 < h)
    (hsize : h ≤ (Fintype.card B / 2 - J) / (2 * K))
    (E : Finset V) (s : State V H D B) (hs : Coherent lines f hit K E s)
    (hbad : ∀ v ∉ E, Fintype.card B / 2 ≤
      (touchedBatches (fun v => lines (f v)) hit v).card)
    (htrunc : ∀ d, (Finset.univ.filter (fun r => hit r d)).card ≤ J)
    (herr : (Fintype.card V : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2) :
    ∃ n, ∃ w : Word lines K n s, Segment lines f hit K false E Finset.univ s w ∧
      0 ≤ charge lines K s w ∧ n ≤ Fintype.card V - E.card := by
  classical
  obtain ⟨F, hpath, roots, hr, hroot⟩ := high_case_certificate_geometry
    (fun v => lines (f v)) hit E K J h hh hsize hbad
      (by
        intro d
        apply le_trans _ (htrunc d)
        apply Finset.card_le_card
        intro r hr
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hr) herr
  obtain ⟨n, w, hw, hq⟩ := encoding_path_program lines f hf hit K hK false hpath s hs
  obtain ⟨m, w', hw', hq'⟩ := residual_program lines f hit K hK false F
    (finish lines K s w) hw.1 roots hr hroot
  refine ⟨m + n, append lines K s w w', segment_append lines f hit K false E F _ s w w' hw hw', ?_, ?_⟩
  · rw [charge_append]; exact add_nonneg hq hq'
  · have hl := length_le_degreeSum lines K s (append lines K s w w')
    have hc := (segment_append lines f hit K false E F _ s w w' hw hw').2.1
    simp only [Finset.card_univ] at hc
    omega
omit [Fintype H] [DecidableEq H] in
omit [Fintype D] in

 theorem bad_program_low (f : V → H) (hf : Function.Injective f)
    (hit : B → D → Prop) (K h : ℕ) (hK : 2 ≤ K) (hh : 0 < h)
    (hsize : h ≤ (Fintype.card B / 2) / (2 * K))
    (E : Finset V) (s : State V H D B) (hs : Coherent lines f hit K E s)
    (hbad : ∀ v ∉ E, Fintype.card B / 2 ≤
      (touchedBatches (fun v => lines (f v)) hit v).card)
    (herr : (Fintype.card V : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2) :
    ∃ n, ∃ w : Word lines K n s, Segment lines f hit K true E Finset.univ s w ∧
      0 ≤ charge lines K s w ∧ n ≤ Fintype.card V - E.card := by
  obtain ⟨F, hpath, roots, hr, hroot⟩ := low_case_certificate_geometry
    (fun v => lines (f v)) hit E K h hh hsize hbad herr
  obtain ⟨n, w, hw, hq⟩ := encoding_path_program lines f hf hit K hK true hpath s hs
  obtain ⟨m, w', hw', hq'⟩ := residual_program lines f hit K hK true F
    (finish lines K s w) hw.1 roots hr hroot
  refine ⟨m + n, append lines K s w w', segment_append lines f hit K true E F _ s w w' hw hw', ?_, ?_⟩
  · rw [charge_append]; exact add_nonneg hq hq'
  · have hl := length_le_degreeSum lines K s (append lines K s w w')
    have hc := (segment_append lines f hit K true E F _ s w w' hw hw').2.1
    simp only [Finset.card_univ] at hc
    omega

omit [DecidableEq D] [DecidableEq B] in
lemma decoded_static_union_bound {F C : Type*} [Fintype F] [DecidableEq F]
    [Fintype C] [DecidableEq C]
    (rate : D → ℝ≥0) (requirements : C → Finset (B × D)) (decode : C → F)
    (events : F → Set ((B × D) → ℕ))
    (hm : ∀ f, MeasurableSet (events f))
    (hc : ∀ f ω, ω ∈ events f → ∃ c, decode c = f ∧ ω ∈ positiveEvent (requirements c)) :
    (∑ f, (poissonLaw (fun p : B × D => rate p.2)).real (events f)) ≤
      ∑ c, weight (fun p : B × D => rate p.2) (requirements c) := by
  classical
  calc
    _ ≤ ∑ f, ∑ c ∈ Finset.univ.filter (fun c => decode c = f),
        weight (fun p : B × D => rate p.2) (requirements c) := by
      apply Finset.sum_le_sum
      intro f _
      apply static_union_bound _ requirements _ (events f) (hm f)
      intro ω hω
      obtain ⟨c, hd, he⟩ := hc f ω hω
      exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩, he⟩
    _ = _ := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      simp

abbrev AllPrograms (K : ℕ) (E : Finset V) (s : State V H D B) :=
  (n : Fin (Fintype.card V - E.card + 1)) × Word lines K n.val s

 def CompleteProgram (K : ℕ) (low : Bool) (E : Finset V) (s : State V H D B)
    (c : AllPrograms lines K E s) : Prop :=
  TraceOK lines K low s c.2 ∧ 0 ≤ charge lines K s c.2 ∧
    degreeSum lines K s c.2 = Fintype.card V - E.card

noncomputable def completePrograms (K : ℕ) (low : Bool) (E : Finset V) (s : State V H D B) :=
  {c : AllPrograms lines K E s // CompleteProgram lines K low E s c}

noncomputable instance completePrograms_fintype (K : ℕ) (low : Bool) (E : Finset V)
    (s : State V H D B) : Fintype (completePrograms lines K low E s) := by
  classical
  unfold completePrograms
  infer_instance
end SharpRamseyFive.CertificateCover
end

end OAI
