import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.WitnessList

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
namespace SharpRamseyFive.ResidualCertificate
variable {V : Type*} [Fintype V] [DecidableEq V]
section SharedHitGeometry
open scoped Classical
variable {D B : Type*} [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B]
omit [Fintype D] [Fintype B] in
lemma anchorEvents_realized (hit : B → D → Prop) (C : Finset (B × D))
    (A : Finset D) (r : A → B) (h : ∀ d : A, hit (r d) d.val) :
    Realized hit (anchorEvents C A r) := by
  intro p hp
  obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hp
  exact h d

omit [Fintype V] [Fintype D] in

theorem anchor_step_witnesses (s : V → Finset D) (hit : B → D → Prop)
    (E : Finset V) (C : Finset (B × D)) (v : V) (a : ℕ)
    (hC : DictionaryInvariant s E C) (hreal : Realized hit C)
    (ha : a ≤ (touchedToEncoded s hit E v).card) :
    ∃ (A : Finset D) (r : A → B), A.card = a ∧
      A ⊆ s v ∧ A ⊆ encodedDirections s E ∧
      (∀ d : A, hit (r d) d.val) ∧
      Disjoint C (anchorEvents C A r) ∧
      Realized hit (C ∪ anchorEvents C A r) ∧
      DictionaryInvariant s (insert v E) (C ∪ anchorEvents C A r) ∧
      (C ∪ anchorEvents C A r).card ≤ C.card + a := by
  classical
  obtain ⟨A, hA, hAc⟩ := Finset.exists_subset_card_eq ha
  have hh (d : A) : ∃ r, hit r d.val := (Finset.mem_filter.mp (hA d.property)).2
  choose r hr using hh
  have hAs : A ⊆ s v := fun d hd => (Finset.mem_inter.mp
    (Finset.mem_filter.mp (hA hd)).1).1
  have hAE : A ⊆ encodedDirections s E := fun d hd => (Finset.mem_inter.mp
    (Finset.mem_filter.mp (hA hd)).1).2
  refine ⟨A, r, hAc, hAs, hAE, hr, anchorEvents_fresh C A r,
    realized_union hit hreal (anchorEvents_realized hit C A r hr), ?_, ?_⟩
  · unfold DictionaryInvariant
    rw [paidDirections_union]
    apply Finset.union_subset
    · exact hC.trans (encodedDirections_mono s (Finset.subset_insert _ _))
    · exact (anchorEvents_directions C A r).trans
        (hAE.trans (encodedDirections_mono s (Finset.subset_insert _ _)))
  · exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left
      ((anchorEvents_card C A r).trans_eq hAc) _)

noncomputable def pairEvents (T : Finset B) (d : T → D) : Finset (B × D) :=
  T.attach.image (fun r => (r.val, d r))

omit [Fintype D] [Fintype B] in
lemma pairEvents_card (T : Finset B) (d : T → D) :
    (pairEvents T d).card = T.card := by
  rw [pairEvents, Finset.card_image_of_injective]
  · exact Finset.card_attach
  · intro r r' he
    exact Subtype.ext (congrArg Prod.fst he)

omit [Fintype D] [Fintype B] in
lemma pairEvents_realized (hit : B → D → Prop) (T : Finset B) (d : T → D)
    (h : ∀ r : T, hit r.val (d r)) : Realized hit (pairEvents T d) := by
  intro p hp
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hp
  exact h r

omit [Fintype V] [Fintype D] in

theorem pair_step_witnesses (s : V → Finset D) (hit : B → D → Prop)
    (E : Finset V) (C : Finset (B × D)) (v u : V) (K : ℕ)
    (hC : DictionaryInvariant s E C) (hreal : Realized hit C)
    (hp : K ≤ (sharedBatches (outsideDirections s E) hit v u).card) :
    ∃ (T : Finset B) (d : T → D), T.card = K ∧
      (∀ r : T, d r ∈ s v ∩ s u ∧ d r ∉ encodedDirections s E ∧ hit r.val (d r)) ∧
      Disjoint C (pairEvents T d) ∧ Realized hit (C ∪ pairEvents T d) ∧
      DictionaryInvariant s (insert v (insert u E)) (C ∪ pairEvents T d) ∧
      (C ∪ pairEvents T d).card = C.card + K := by
  classical
  obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq hp
  have hh (r : T) : ∃ d, d ∈ s v ∩ s u ∧ d ∉ encodedDirections s E ∧ hit r.val d := by
    obtain ⟨d, hd, hr⟩ := (Finset.mem_filter.mp (hT r.property)).2
    obtain ⟨hdv, hdu⟩ := Finset.mem_inter.mp hd
    exact ⟨d, Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hdv).1,
      (Finset.mem_sdiff.mp hdu).1⟩, (Finset.mem_sdiff.mp hdv).2, hr⟩
  choose d hd using hh
  have hfresh : Disjoint C (pairEvents T d) := by
    apply Finset.disjoint_left.mpr
    intro p hp he
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp he
    exact (hd r).2.1 (hC (Finset.mem_image_of_mem Prod.snd hp))
  refine ⟨T, d, hTc, hd, hfresh,
    realized_union hit hreal (pairEvents_realized hit T d (fun r => (hd r).2.2)), ?_, ?_⟩
  · unfold DictionaryInvariant
    rw [paidDirections_union]
    apply Finset.union_subset
    · exact hC.trans (encodedDirections_mono s ((Finset.subset_insert _ _).trans
        (Finset.subset_insert _ _)))
    · intro z hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_insert_self _ _,
        (Finset.mem_inter.mp (hd r).1).1⟩
  · rw [Finset.card_union_of_disjoint hfresh, pairEvents_card, hTc]

inductive PaidStep (s : V → Finset D) (hit : B → D → Prop) (a K : ℕ) :
    (Finset V × Finset (B × D)) → (Finset V × Finset (B × D)) → Prop
  | anchor (E : Finset V) (C : Finset (B × D)) (v : V) (hv : v ∉ E)
      (A : Finset D) (hA : A.card = a) (hAs : A ⊆ s v)
      (hAE : A ⊆ encodedDirections s E) (r : A → B) (hr : ∀ d : A, hit (r d) d.val) :
      PaidStep s hit a K (E, C) (insert v E, C ∪ anchorEvents C A r)
  | pair (E : Finset V) (C : Finset (B × D)) (v u : V)
      (hv : v ∉ E) (hu : u ∉ E) (hne : v ≠ u)
      (T : Finset B) (hT : T.card = K) (d : T → D)
      (hd : ∀ r : T, d r ∈ s v ∩ s u ∧ d r ∉ encodedDirections s E ∧ hit r.val (d r)) :
      PaidStep s hit a K (E, C) (insert v (insert u E), C ∪ pairEvents T d)

omit [Fintype V] in
omit [Fintype D] [Fintype B] in
lemma paidStep_realized (s : V → Finset D) (hit : B → D → Prop) (a K : ℕ)
    {Z Z' : Finset V × Finset (B × D)} (h : PaidStep s hit a K Z Z')
    (hreal : Realized hit Z.2) : Realized hit Z'.2 := by
  cases h with
  | anchor E C v hv A hA hAs hAE r hr =>
    exact realized_union hit hreal (anchorEvents_realized hit C A r hr)
  | pair E C v u hv hu hne T hT d hd =>
    exact realized_union hit hreal (pairEvents_realized hit T d (fun r => (hd r).2.2))
omit [Fintype V] [Fintype D] [Fintype B] in

lemma paidStep_dictionary (s : V → Finset D) (hit : B → D → Prop) (a K : ℕ)
    {Z Z' : Finset V × Finset (B × D)} (h : PaidStep s hit a K Z Z')
    (hC : DictionaryInvariant s Z.1 Z.2) : DictionaryInvariant s Z'.1 Z'.2 := by
  cases h with
  | anchor E C v hv A hA hAs hAE r hr =>
    unfold DictionaryInvariant
    rw [paidDirections_union]
    exact Finset.union_subset
      (hC.trans (encodedDirections_mono s (Finset.subset_insert _ _)))
      ((anchorEvents_directions C A r).trans
        (hAE.trans (encodedDirections_mono s (Finset.subset_insert _ _))))
  | pair E C v u hv hu hne T hT d hd =>
    unfold DictionaryInvariant
    rw [paidDirections_union]
    refine Finset.union_subset
      (hC.trans (encodedDirections_mono s ((Finset.subset_insert _ _).trans
        (Finset.subset_insert _ _)))) ?_
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_insert_self _ _,
      (Finset.mem_inter.mp (hd r).1).1⟩

omit [Fintype V] in
omit [Fintype D] [Fintype B] in
lemma paidStep_cost (s : V → Finset D) (hit : B → D → Prop) (a K : ℕ) (haK : a ≤ K)
    {Z Z' : Finset V × Finset (B × D)} (h : PaidStep s hit a K Z Z') :
    Z'.2.card + K * Z.1.card ≤ Z.2.card + K * Z'.1.card := by
  cases h with
  | anchor E C v hv A hA hAs hAE r hr =>
    simp only [Finset.card_insert_of_notMem hv, Nat.mul_add, Nat.mul_one]
    have hc := (Finset.card_union_le C (anchorEvents C A r)).trans
      (Nat.add_le_add_left ((anchorEvents_card C A r).trans_eq hA) C.card)
    omega
  | pair E C v u hv hu hne T hT d hd =>
    have hv' : v ∉ insert u E := by simp [hne, hv]
    simp only [Finset.card_insert_of_notMem hv', Finset.card_insert_of_notMem hu,
      Nat.mul_add, Nat.mul_one]
    have hc := Finset.card_union_le C (pairEvents T d)
    rw [pairEvents_card, hT] at hc
    omega

omit [Fintype V] [Fintype D] in

lemma encodingStep_lift (s : V → Finset D) (hit : B → D → Prop) (a K : ℕ)
    {E F : Finset V} (h : EncodingStep s hit a K E F)
    (C : Finset (B × D)) (hC : DictionaryInvariant s E C) (hreal : Realized hit C) :
    ∃ C', PaidStep s hit a K (E, C) (F, C') ∧
      DictionaryInvariant s F C' ∧ Realized hit C' := by
  cases h with
  | anchor v hv ha =>
    obtain ⟨A, r, hAc, hAs, hAE, hr, _, hh, hdict, _⟩ :=
      anchor_step_witnesses s hit E C v a hC hreal ha
    exact ⟨_, .anchor E C v hv A hAc hAs hAE r hr, hdict, hh⟩
  | pair v u hv hu hne hp =>
    obtain ⟨T, d, hTc, hd, _, hh, hdict, _⟩ :=
      pair_step_witnesses s hit E C v u K hC hreal hp
    exact ⟨_, .pair E C v u hv hu hne T hTc d hd, hdict, hh⟩
omit [Fintype V] [Fintype D] in

lemma encoding_path_lift (s : V → Finset D) (hit : B → D → Prop) (a K : ℕ)
    {E F : Finset V} (h : Relation.ReflTransGen (EncodingStep s hit a K) E F)
    (C : Finset (B × D)) (hC : DictionaryInvariant s E C) (hreal : Realized hit C) :
    ∃ C', Relation.ReflTransGen (PaidStep s hit a K) (E, C) (F, C') ∧
      DictionaryInvariant s F C' ∧ Realized hit C' := by
  induction h with
  | refl => exact ⟨C, .refl, hC, hreal⟩
  | @tail F G h hFG ih =>
    obtain ⟨C', hpath, hc', hr'⟩ := ih
    obtain ⟨C'', hstep, hc'', hr''⟩ := encodingStep_lift s hit a K hFG C' hc' hr'
    exact ⟨C'', hpath.tail hstep, hc'', hr''⟩

omit [Fintype V] in
omit [Fintype D] [Fintype B] in

lemma paid_path_cost (s : V → Finset D) (hit : B → D → Prop) (a K : ℕ) (haK : a ≤ K)
    {Z Z' : Finset V × Finset (B × D)}
    (h : Relation.ReflTransGen (PaidStep s hit a K) Z Z') :
    Z'.2.card + K * Z.1.card ≤ Z.2.card + K * Z'.1.card := by
  induction h with
  | refl => omega
  | @tail F G h hFG ih =>
    have hc := paidStep_cost s hit a K haK hFG
    omega

omit [Fintype D] in

theorem terminal_paid_certificate (s : V → Finset D) (hit : B → D → Prop)
    (a K : ℕ) (haK : a ≤ K) (E : Finset V) :
    ∃ F C, Relation.ReflTransGen (PaidStep s hit a K) (E, ∅) (F, C) ∧
      DictionaryInvariant s F C ∧ Realized hit C ∧
      C.card ≤ K * Fintype.card V ∧ (paidDirections C).card ≤ K * Fintype.card V ∧
      (∀ v ∉ F, (touchedToEncoded s hit F v).card < a) ∧
      ∀ v ∉ F, ∀ u ∉ F, v ≠ u →
        (sharedBatches (outsideDirections s F) hit v u).card < K := by
  classical
  obtain ⟨F, hF, ha, hp⟩ := exists_terminal_encoding s hit a K E
  have hc : DictionaryInvariant s E (∅ : Finset (B × D)) := by
    simp [DictionaryInvariant, paidDirections]
  have hr : Realized hit (∅ : Finset (B × D)) := by simp [Realized]
  obtain ⟨C, hpath, hC, hreal⟩ := encoding_path_lift s hit a K hF ∅ hc hr
  have hcost := paid_path_cost s hit a K haK hpath
  simp only [Finset.card_empty, zero_add] at hcost
  have hbound : C.card ≤ K * Fintype.card V := by
    have hcard := Nat.mul_le_mul_left K (Finset.card_le_univ F)
    omega
  exact ⟨F, C, hpath, hC, hreal, hbound,
    Finset.card_image_le.trans hbound, ha, hp⟩

end SharedHitGeometry

end SharpRamseyFive.ResidualCertificate

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

 def Agrees (f : V → H) (E : Finset V) (s : State V H D B) : Prop :=
  ∀ v ∈ E, s.1 v = f v

omit [Fintype V] [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D] [Fintype B] [DecidableEq B] in
lemma agrees_update (f : V → H) (E : Finset V) (s : State V H D B)
    (hs : Agrees f E s) (v : V) (C : Finset (B × D)) :
    Agrees f (insert v E) (Function.update s.1 v (f v), C) := by
  intro u hu
  rcases Finset.mem_insert.mp hu with rfl | hu
  · simp
  · by_cases he : u = v
    · subst u; simp
    · simpa [Function.update_of_ne he] using hs u hu

noncomputable def anchorName (C : Finset (B × D)) (S : Finset D)
    (d : D) (hd : d ∈ S) (r : B) : AnchorChoice C S :=
  if he : d ∈ dictionary C then .inl ⟨d, Finset.mem_inter.mpr ⟨hd, he⟩⟩
  else .inr (r, ⟨d, Finset.mem_sdiff.mpr ⟨hd, he⟩⟩)

omit [Fintype D] [Fintype B] [DecidableEq B] in
lemma anchorName_direction (C : Finset (B × D)) (S : Finset D)
    (d : D) (hd : d ∈ S) (r : B) : (anchorName C S d hd r).direction = d := by
  unfold anchorName
  split_ifs <;> rfl

omit [Fintype D] [Fintype B] [DecidableEq B] in
lemma anchorName_realized (hit : B → D → Prop) (C : Finset (B × D))
    (S : Finset D) (d : D) (hd : d ∈ S) (r : B) (hr : hit r d) :
    Realized hit (anchorName C S d hd r).requirements := by
  unfold anchorName
  split_ifs <;> simp_all [AnchorChoice.requirements, Realized]

omit [Fintype D] [Fintype B] [DecidableEq B] in
lemma anchor_req_card {C : Finset (B × D)} {S : Finset D} (a : AnchorChoice C S) :
    a.requirements.card ≤ 1 := by
  cases a <;> simp [AnchorChoice.requirements]

omit [Fintype D] [Fintype B] [DecidableEq B] in
lemma anchor_req_directions {C : Finset (B × D)} {S : Finset D}
    (a : AnchorChoice C S) : paidDirections a.requirements ⊆ {a.direction} := by
  cases a <;> simp [AnchorChoice.requirements, AnchorChoice.direction, paidDirections]
omit [Fintype D] [Fintype B] [DecidableEq B] in

lemma anchor_req_disjoint {C : Finset (B × D)} {S T : Finset D}
    (a : AnchorChoice C S) (b : AnchorChoice C T) (hne : a.direction ≠ b.direction) :
    Disjoint a.requirements b.requirements := by
  apply Finset.disjoint_left.mpr
  intro p ha hb
  have ha' := anchor_req_directions a (Finset.mem_image_of_mem Prod.snd ha)
  have hb' := anchor_req_directions b (Finset.mem_image_of_mem Prod.snd hb)
  exact hne ((Finset.mem_singleton.mp ha').symm.trans (Finset.mem_singleton.mp hb'))

omit [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] in
omit [Fintype D] in
lemma rawCost_eq_weight (rate : D → ℝ≥0) (denom : ℝ) (K : ℕ) (low : Bool)
    (s : State V H D B) (a : Action lines K s)
    (henabled : ∀ c : OneChoice lines s, a = .inr (.inl c) → low = true) :
    rawCost lines rate denom K low s a =
      weight (fun p : B × D => rate p.2) (newEvents lines K s a) /
        denom ^ degree lines K s a := by
  rcases a with a | a
  · simp [rawCost, newEvents, degree, weight]
  rcases a with a | a
  · rw [henabled a rfl]
    simp [rawCost, newEvents, degree, oneCost, AnchorChoice.weight]
  rcases a with a | a
  · simp only [rawCost, newEvents, degree, twoCost, pow_one]
    rw [weight_union_fresh _ _ _ (anchor_req_disjoint _ _ a.2.2.2.2.2.property.1),
      AnchorChoice.weight, AnchorChoice.weight]
  · rfl

omit [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] in
omit [Fintype D] in
lemma newEvents_card (K : ℕ) (hK : 2 ≤ K) (s : State V H D B) (a : Action lines K s) :
    (newEvents lines K s a).card ≤ K * degree lines K s a := by
  rcases a with a | a
  · simp [newEvents, degree]
  rcases a with a | a
  · simpa [newEvents, degree] using (anchor_req_card a.2.2.1).trans (by omega : 1 ≤ K)
  rcases a with a | a
  · change (a.2.2.2.1.requirements ∪ a.2.2.2.2.1.requirements).card ≤ K * 1
    have hc := Finset.card_union_le a.2.2.2.1.requirements a.2.2.2.2.1.requirements
    have h1 := anchor_req_card a.2.2.2.1
    have h2 := anchor_req_card a.2.2.2.2.1
    omega
  · simp only [newEvents, degree, witnessRequirements_card]
    have ht := (Finset.mem_powersetCard.mp a.2.2.2.2.1.property).2
    omega

 def Enabled (K : ℕ) (low : Bool) (s : State V H D B) (a : Action lines K s) : Prop :=
  ∀ c : OneChoice lines s, a = .inr (.inl c) → low = true

omit [Fintype H] [DecidableEq H] in
omit [Fintype D] in

lemma step_weight (rate : D → ℝ≥0) (denom : ℝ) (hdenom : denom ≠ 0)
    (K : ℕ) (low : Bool) (s : State V H D B) (a : Action lines K s)
    (he : Enabled lines K low s a) (hs : s.2.card ≤ K * Fintype.card V) :
    weight (fun p : B × D => rate p.2) (advance lines K s a).2 =
      weight (fun p : B × D => rate p.2) s.2 *
        programCost lines rate denom K low s a * denom ^ degree lines K s a := by
  rw [programCost, ite_eq_left hs, rawCost_eq_weight lines rate denom K low s a he]
  rw [advance, weight_union_fresh _ _ _ (newEvents_fresh lines K s a)]
  field_simp

 def Coherent (f : V → H) (hit : B → D → Prop) (K : ℕ)
    (E : Finset V) (s : State V H D B) : Prop :=
  Agrees f E s ∧ DictionaryInvariant (fun v => lines (f v)) E s.2 ∧
    Realized hit s.2 ∧ s.2.card ≤ K * E.card
omit [Fintype V] [Fintype H] [DecidableEq H] in
omit [Fintype D] in

lemma coherent_step (f : V → H) (hit : B → D → Prop) (K : ℕ) (hK : 2 ≤ K)
    (E F : Finset V) (s : State V H D B) (hs : Coherent lines f hit K E s)
    (a : Action lines K s) (hEF : E ⊆ F)
    (hag : Agrees f F (advance lines K s a))
    (hdict : paidDirections (newEvents lines K s a) ⊆ encodedDirections (fun v => lines (f v)) F)
    (hreal : Realized hit (newEvents lines K s a))
    (hcard : F.card = E.card + degree lines K s a) :
    Coherent lines f hit K F (advance lines K s a) := by
  refine ⟨hag, ?_, realized_union hit hs.2.2.1 hreal, ?_⟩
  · change paidDirections (s.2 ∪ newEvents lines K s a) ⊆ _
    rw [paidDirections_union]
    exact Finset.union_subset
      (hs.2.1.trans (encodedDirections_mono _ hEF)) hdict
  · change (s.2 ∪ newEvents lines K s a).card ≤ _
    apply (Finset.card_union_le _ _).trans
    calc
      _ ≤ K * E.card + K * degree lines K s a :=
        Nat.add_le_add hs.2.2.2 (newEvents_card lines K hK s a)
      _ = _ := by rw [hcard, Nat.mul_add]

omit [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] in
omit [Fintype D] [DecidableEq B] in
lemma touched_anchor (f : V → H) (hit : B → D → Prop)
    (E : Finset V) (s : State V H D B) (hs : Agrees f E s) (v : V) (d : D)
    (hd : d ∈ touchedToEncoded (fun v => lines (f v)) hit E v) :
    ∃ u ∈ E, ∃ x : AnchorChoice s.2 (lines (s.1 u)),
      x.direction = d ∧ d ∈ lines (f v) ∧ Realized hit x.requirements := by
  classical
  obtain ⟨hgeom, r, hr⟩ := Finset.mem_filter.mp hd
  obtain ⟨hv, henc⟩ := Finset.mem_inter.mp hgeom
  obtain ⟨u, hu, hdu⟩ := Finset.mem_biUnion.mp henc
  have hdu' : d ∈ lines (s.1 u) := by rw [hs u hu]; exact hdu
  exact ⟨u, hu, anchorName s.2 _ d hdu' r,
    anchorName_direction _ _ _ _ _, hv, anchorName_realized hit _ _ _ _ _ hr⟩

omit [Fintype V] [Fintype H] [DecidableEq H] in
omit [Fintype D] in

lemma make_one (f : V → H) (hit : B → D → Prop) (K : ℕ) (hK : 2 ≤ K)
    (E : Finset V) (s : State V H D B) (hs : Coherent lines f hit K E s)
    (v : V) (hv : v ∉ E)
    (ha : 1 ≤ (touchedToEncoded (fun v => lines (f v)) hit E v).card) :
    ∃ a : Action lines K s, Coherent lines f hit K (insert v E) (advance lines K s a) ∧
      (insert v E).card = E.card + degree lines K s a ∧
      Enabled lines K true s a ∧ actionCharge lines K s a = 0 := by
  classical
  obtain ⟨d, hd⟩ := Finset.card_pos.mp (by omega : 0 < (touchedToEncoded (fun v => lines (f v)) hit E v).card)
  obtain ⟨u, hu, x, hxd, hdv, hxreal⟩ := touched_anchor lines f hit E s hs.1 v d hd
  let c : OneChoice lines s := ⟨v, u, x, f v, hxd ▸ hdv⟩
  let a : Action lines K s := .inr (.inl c)
  have hc : (insert v E).card = E.card + degree lines K s a := by
    simp [a, degree, Finset.card_insert_of_notMem hv]
  refine ⟨a, ?_, hc, fun _ _ => rfl, rfl⟩
  apply coherent_step lines f hit K hK E (insert v E) s hs a (Finset.subset_insert _ _) _ _ hxreal hc
  · exact agrees_update f E s hs.1 v _
  · apply (anchor_req_directions x).trans
    intro z hz
    have hz' : z = x.direction := Finset.mem_singleton.mp hz
    apply Finset.mem_biUnion.mpr
    exact ⟨v, Finset.mem_insert_self _ _, hz' ▸ (hxd ▸ hdv)⟩
omit [Fintype V] [Fintype H] [DecidableEq H] in
omit [Fintype D] in

lemma make_two (f : V → H) (hit : B → D → Prop) (K : ℕ) (hK : 2 ≤ K)
    (low : Bool) (E : Finset V) (s : State V H D B) (hs : Coherent lines f hit K E s)
    (v : V) (hv : v ∉ E)
    (ha : 2 ≤ (touchedToEncoded (fun v => lines (f v)) hit E v).card) :
    ∃ a : Action lines K s, Coherent lines f hit K (insert v E) (advance lines K s a) ∧
      (insert v E).card = E.card + degree lines K s a ∧
      Enabled lines K low s a ∧ actionCharge lines K s a = 1 := by
  classical
  obtain ⟨d, hd, e, he, hde⟩ := Finset.one_lt_card.mp (by omega :
    1 < (touchedToEncoded (fun v => lines (f v)) hit E v).card)
  obtain ⟨u, hu, x, hxd, hdv, hxreal⟩ := touched_anchor lines f hit E s hs.1 v d hd
  obtain ⟨w, hw, y, hye, hev, hyreal⟩ := touched_anchor lines f hit E s hs.1 v e he
  let c : TwoChoice lines s := ⟨v, u, w, x, y, f v,
    by simpa only [hxd, hye] using And.intro hde (And.intro hdv hev)⟩
  let a : Action lines K s := .inr (.inr (.inl c))
  have hc : (insert v E).card = E.card + degree lines K s a := by
    simp [a, degree, Finset.card_insert_of_notMem hv]
  refine ⟨a, ?_, hc, ?_, rfl⟩
  · apply coherent_step lines f hit K hK E (insert v E) s hs a (Finset.subset_insert _ _) _ _
      (realized_union hit hxreal hyreal) hc
    · exact agrees_update f E s hs.1 v _
    · change paidDirections (x.requirements ∪ y.requirements) ⊆ _
      rw [paidDirections_union]
      apply Finset.union_subset
      · apply (anchor_req_directions x).trans
        intro z hz
        have hz' := Finset.mem_singleton.mp hz
        exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_insert_self _ _, hz' ▸ (hxd ▸ hdv)⟩
      · apply (anchor_req_directions y).trans
        intro z hz
        have hz' := Finset.mem_singleton.mp hz
        exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_insert_self _ _, hz' ▸ (hye ▸ hev)⟩
  · intro c' he
    simp [a] at he
end SharpRamseyFive.CertificateCover
end

end OAI
