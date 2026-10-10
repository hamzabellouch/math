import OAI.Computability.Superstring.HostNormalization

namespace OAI

namespace Superstring.Hierarchical

/-- A distinguished rotation exists by inspecting one finite period. -/
theorem exists_greatest_rotation {α : Type} [LinearOrder α] (A : ℤ → α)
    (p : ℕ) (hp : 0 < p) (per : Function.Periodic A (p : ℤ)) :
    ∃ t : ℤ, 0 ≤ t ∧ t < p ∧ ∀ x, forward A x ≤ forward A t := by
  classical
  let : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  obtain ⟨i, _, hmax⟩ := Finset.univ.exists_max_image
    (fun i : Fin p => forward A i.val) Finset.univ_nonempty
  refine ⟨i.val, by omega, by omega, ?_⟩
  intro x
  let r : Fin p := ⟨(x % (p : ℤ)).toNat, by
    have h0 := Int.emod_nonneg x (show (p : ℤ) ≠ 0 by omega)
    have h1 := Int.emod_lt_of_pos x (show (0 : ℤ) < p by omega)
    omega⟩
  have hr : (r.val : ℤ) = x % p := by
    dsimp only [r]
    exact Int.toNat_of_nonneg (Int.emod_nonneg x (by omega))
  have he : forward A x = forward A r.val := by
    apply congrArg toLex
    funext n
    have hdiv := Int.emod_add_ediv_mul x (p : ℤ)
    have hm := per.sub_int_mul_eq (x := x + n) (x / p)
    simp only [Int.cast_id] at hm
    have hx : x + n - (x / p) * p = r.val + n := by omega
    rw [hx] at hm
    exact hm.symm
  rw [he]
  exact hmax r (Finset.mem_univ _)

namespace Layer

variable {α : Type} {V : Set (List α)} {A : ℤ → α} {p : ℕ}

/-- Every text letter occurs on the fixed layer's last actual window. -/
theorem letters (L : Layer V A p) (closed : SubstringClosed V) (x : ℤ) : [A x] ∈ V := by
  have hlen : x + 1 ≤ L.last x := by
    have := L.start_le_first (x + 1)
    simpa only [first, last, add_sub_cancel_right] using this
  have hword : textWord A x (x + 1) = [A x] := by
    simp [textWord]
  rw [← hword]
  exact closed (L.last_actual x) (textWord_infix A le_rfl (by omega) hlen)

end Layer

/-- Finite ordered primitive-text groups supplied by the fixed base
 decomposition. All fields describe actual layers, never connecting walks. -/
structure LayerCollection {α : Type} (V : Set (List α)) (G : Type) where
  text : G → ℤ → α
  period : G → ℕ
  size : G → ℕ
  positive : ∀ g, 0 < period g
  nonempty : ∀ g, 0 < size g
  periodic : ∀ g, Function.Periodic (text g) (period g : ℤ)
  layer : ∀ g, Fin (size g) → Layer V (text g) (period g)
  ordered : ∀ g (i j : Fin (size g)), i ≤ j → ∀ x, (layer g i).z x ≤ (layer g j).z x
  different : ∀ g h, g ≠ h → ∀ c, text g ≠ fun x => text h (x + c)

namespace LayerCollection

variable {α G : Type} {V : Set (List α)} (C : LayerCollection V G)

abbrev Id := Σ g, Fin (C.size g)

def layerAt (i : C.Id) : Layer V (C.text i.1) (C.period i.1) := C.layer i.1 i.2

noncomputable def distinguished [LinearOrder α] (g : G) : ℤ :=
  (exists_greatest_rotation (C.text g) (C.period g) (C.positive g) (C.periodic g)).choose

theorem distinguished_max [LinearOrder α] (g : G) (x : ℤ) :
    forward (C.text g) x ≤ forward (C.text g) (C.distinguished g) :=
  (exists_greatest_rotation (C.text g) (C.period g) (C.positive g) (C.periodic g)).choose_spec.2.2 x

noncomputable def rank [LinearOrder α] (g : G) : Lex (ℕ → α) :=
  forward (C.text g) (C.distinguished g)

theorem letters (closed : SubstringClosed V) (g : G) (x : ℤ) : [C.text g x] ∈ V :=
  (C.layer g ⟨0, C.nonempty g⟩).letters closed x

end LayerCollection
end Superstring.Hierarchical

namespace Superstring.Hierarchical

/-- Constant-period version of base saturation, retaining every already
visited vertex. The finite index set is allowed to omit other layers. -/
theorem fill_same_layers {α ι : Type} {V : Set (List α)} {A : ℤ → α} {p : ℕ}
    (closed : SubstringClosed V) (L : ι → Layer V A p) (hp : 0 < p)
    (per : Function.Periodic A (p : ℤ)) (I : Finset ι) (P : Loop V)
    (htouch : ∀ i ∈ I, (L i).TouchedBy P.path) :
    ∃ Q : Loop V, Q.base = P.base ∧ Q.cost ≤ P.cost + I.card * p ∧
      (∀ w, P.Visits w → Q.Visits w) ∧
      ∀ i ∈ I, ∀ w ∈ (L i).Content, Q.Visits w := by
  obtain ⟨Q, hb, hc, hv, hl⟩ := fill_layers closed L (fun _ => hp) (fun _ => per) I P htouch
  exact ⟨Q, hb, by simpa using hc, hv, hl⟩

theorem forward_shift {α : Type} (A : ℤ → α) (c t : ℤ) :
    forward (fun x => A (x + c)) t = forward A (t + c) := by
  apply congrArg toLex
  funext n
  change A (t + n + c) = A (t + c + n)
  congr 1
  omega

namespace LayerCollection

variable {α G : Type} {V : Set (List α)} (C : LayerCollection V G)


def groupIds (g : G) (I : Finset (Fin (C.size g))) : Finset C.Id :=
  I.map ⟨Sigma.mk g, fun _ _ h => eq_of_heq (Sigma.mk.inj h).2⟩

@[simp] theorem card_groupIds (g : G) (I : Finset (Fin (C.size g))) :
    (C.groupIds g I).card = I.card := Finset.card_map _

theorem groupIds_same (g : G) (I : Finset (Fin (C.size g))) {i : C.Id}
    (hi : i ∈ C.groupIds g I) : i.1 = g := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
  rfl

/-- A concrete outgoing plan. Its local walks include each constituent base
turn exactly once in the reserve. -/
structure PlannedBlock [LinearOrder α] where
  source : G
  members : Finset C.Id
  nonempty : members.Nonempty
  same : ∀ i ∈ members, i.1 = source
  target : C.Id
  record : (C.layerAt target).Record (C.text source)
  foreign : C.text source ≠ fun x => C.text target.1 (x + record.offset)
  link : ∃ P : Loop V, P.cost ≤ 2 * (members.card * C.period source) ∧
    (∀ i ∈ members, ∀ w ∈ (C.layerAt i).Content, P.Visits w) ∧
    P.Visits (textWord (C.text source) record.start record.stop)
  internal : ∃ P : Loop V, P.cost + C.period source ≤ 2 * (members.card * C.period source) ∧
    ∀ i ∈ members, ∀ w ∈ (C.layerAt i).Content, P.Visits w
  short : C.rank target.1 ≤ C.rank source →
    ∃ P : Loop V, P.cost ≤ 2 * (members.card * C.period source) ∧
      (∀ i ∈ members, ∀ w ∈ (C.layerAt i).Content, P.Visits w) ∧
      P.Visits (textWord (C.text source) record.start record.stop) ∧
      ∃ w, P.Visits w ∧ w.length ≤ C.period target.1

namespace PlannedBlock

variable [LinearOrder α] {C : LayerCollection V G} (B : C.PlannedBlock)

def content : Set (List α) := {w | ∃ i ∈ B.members, w ∈ (C.layerAt i).Content}

def word : List α := textWord (C.text B.source) B.record.start B.record.stop

theorem word_content : B.word ∈ (C.layerAt B.target).Content := by
  refine ⟨B.record.start + B.record.offset, B.record.stop + B.record.offset,
    B.record.first_le, B.record.le_last, ?_⟩
  exact B.record.word_eq

theorem same_short (h : B.target.1 = B.source) : B.word.length ≤ C.period B.source := by
  have hh := B.record.same_period_length_lt (C.positive B.source) (C.periodic B.source)
    (by simpa only [h] using C.periodic B.target.1) B.foreign
  have hlo := B.record.start_le_stop
  simp only [word, length_textWord]
  omega

end PlannedBlock
end LayerCollection
end Superstring.Hierarchical

namespace Superstring.Hierarchical.LayerCollection

variable {α G : Type} [LinearOrder α] {V : Set (List α)} (C : LayerCollection V G)

omit [LinearOrder α] in
theorem covers_groupIds (g : G) (I : Finset (Fin (C.size g))) (Q : Loop V)
    (h : ∀ j ∈ I, ∀ w ∈ (C.layer g j).Content, Q.Visits w) :
    ∀ i ∈ C.groupIds g I, ∀ w ∈ (C.layerAt i).Content, Q.Visits w := by
  intro i hi
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
  exact h j hj

/-- A single upper layer satisfies exactly the ordinary individual-link
conditions. The short contact is proved by the three-window path. -/
noncomputable def individualPlan (closed : SubstringClosed V)
    (g : G) (i : Fin (C.size g)) (target : C.Id)
    (R : (C.layerAt target).Record (C.text g))
    (hne : C.text g ≠ fun x => C.text target.1 (x + R.offset))
    (hf : (C.layer g i).first R.start ≤ R.stop)
    (hl : R.stop ≤ (C.layer g i).last R.start + C.period g) : C.PlannedBlock := by
  classical
  have hex : ∃ Q : Loop V, Q.cost ≤ 2 * C.period g ∧
      (∀ j ∈ C.groupIds g {i}, ∀ w ∈ (C.layerAt j).Content, Q.Visits w) ∧
      Q.Visits (textWord (C.text g) R.start R.stop) ∧
      ∃ w, Q.Visits w ∧ w.length ≤ C.period target.1 := by
    have hlen := R.length_lt (C.positive g) (C.positive target.1)
      (C.periodic g) (C.periodic target.1) hne
    obtain ⟨P, hcP, hvP, w, hw, hwlen⟩ := individual_link closed (C.text g)
      (C.letters closed g) (C.period g) (C.period target.1) (C.periodic g)
      (C.layer g i) R.start_le_stop R.word_mem hf hl hlen
    obtain ⟨Q, _, hcQ, hvQ, hlQ⟩ := fill_same_layers closed (C.layer g) (C.positive g)
      (C.periodic g) {i} ⟨_, P⟩ (by simpa using hvP)
    have hcost : Q.cost ≤ 2 * C.period g := by
      simpa only [Finset.card_singleton, one_mul, Loop.cost, hcP, two_mul] using hcQ
    have hcover := C.covers_groupIds g {i} Q hlQ
    have hR : Q.Visits (textWord (C.text g) R.start R.stop) := hvQ _ (Path.visits_start P)
    exact ⟨Q, hcost, hcover, hR, w, hvQ w hw, hwlen⟩
  refine {
    source := g
    members := C.groupIds g {i}
    nonempty := ⟨⟨g, i⟩, Finset.mem_map.mpr ⟨i, Finset.mem_singleton_self i, rfl⟩⟩
    same := fun _ hi => C.groupIds_same g {i} hi
    target := target
    record := R
    foreign := hne
    link := by
      obtain ⟨Q, hc, hv, hr, _⟩ := hex
      exact ⟨Q, by simpa using hc, hv, hr⟩
    internal := ?_
    short := fun _ => by simpa using hex }
  obtain ⟨F, hcF, hvF⟩ := (C.layer g i).content_loop closed (C.positive g) (C.periodic g)
  refine ⟨F, by simp [hcF, two_mul], C.covers_groupIds g {i} F ?_⟩
  intro j hj
  have he : j = i := Finset.mem_singleton.mp hj
  subst j
  exact hvF

/-- A collective top block is valid INCLUDING k=1. Its ordinary link, free
period internal alternative, and maximal-rank short-contact realization are
all materialized, with every constituent base turn included once. -/
noncomputable def collectivePlan (closed : SubstringClosed V)
    (g : G) (I : Finset (Fin (C.size g))) (lo hi : Fin (C.size g))
    (hlom : lo ∈ I) (hhim : hi ∈ I)
    (hlo : ∀ j ∈ I, lo ≤ j) (hhi : ∀ j ∈ I, j ≤ hi)
    (target : C.Id) (R : (C.layerAt target).Record (C.text g))
    (hne : C.text g ≠ fun x => C.text target.1 (x + R.offset))
    (hat : R.start ≤ C.distinguished g) (htb : C.distinguished g < R.stop)
    (hsharp : (C.layer g hi).first (C.distinguished g) -
      (C.layer g lo).last (C.distinguished g) ≤ ((I.card - 1) * C.period g : ℕ))
    (hH : (C.layer g hi).first (C.distinguished g) ≤ R.stop + (I.card * C.period g : ℕ))
    (hlast : R.stop ≤ (C.layer g lo).last R.start + (I.card * C.period g : ℕ)) :
    C.PlannedBlock := by
  classical
  let L := fun j : {j // j ∈ I} => C.layer g j.val
  let l : {j // j ∈ I} := ⟨lo, hlom⟩
  let h : {j // j ∈ I} := ⟨hi, hhim⟩
  have hk : 0 < I.card := Finset.card_pos.mpr ⟨lo, hlom⟩
  have hl : ∀ j x, (L l).z x ≤ (L j).z x :=
    fun j x => C.ordered g lo j.val (hlo j.val j.property) x
  have hh : ∀ j x, (L j).z x ≤ (L h).z x :=
    fun j x => C.ordered g j.val hi (hhi j.val j.property) x
  have hband := Processing.wide_band (C.layer g hi) (C.layer g lo)
    (C.positive g) hk (C.distinguished g) hsharp R.start
  have hbudget : (I.card - 1) * C.period g + C.period g = I.card * C.period g := by
    calc
      (I.card - 1) * C.period g + C.period g = (I.card - 1 + 1) * C.period g := by rw [Nat.add_mul, Nat.one_mul]
      _ = I.card * C.period g := by rw [Nat.sub_add_cancel hk]
  have fill : ∀ P : Loop V, (∀ j, (L j).TouchedBy P.path) →
      ∃ Q : Loop V, Q.cost ≤ P.cost + I.card * C.period g ∧
        (∀ w, P.Visits w → Q.Visits w) ∧
        ∀ i ∈ C.groupIds g I, ∀ w ∈ (C.layerAt i).Content, Q.Visits w := by
    intro P ht
    obtain ⟨Q, _, hcQ, hvQ, hlQ⟩ := fill_same_layers closed (C.layer g) (C.positive g)
      (C.periodic g) I P (fun j hj => ht ⟨j, hj⟩)
    exact ⟨Q, hcQ, hvQ, C.covers_groupIds g I Q hlQ⟩
  refine {
    source := g
    members := C.groupIds g I
    nonempty := ⟨⟨g, lo⟩, Finset.mem_map.mpr ⟨lo, hlom, rfl⟩⟩
    same := fun _ hi => C.groupIds_same g I hi
    target := target
    record := R
    foreign := hne
    link := ?_
    internal := ?_
    short := ?_ }
  · obtain ⟨P, hcP, hvP⟩ := collective_link closed (C.text g) (C.letters closed g)
      (C.period g) I.card (C.periodic g) L l h hl hh R.start_le_stop R.word_mem
      ((C.layer g hi).first_mono hat |>.trans hH) hband hlast
    obtain ⟨Q, hcQ, hvQ, hlQ⟩ := fill ⟨_, P⟩ hvP
    refine ⟨Q, ?_, hlQ, hvQ _ (Path.visits_start P)⟩
    simp only [Loop.cost, hcP] at hcQ
    simpa only [card_groupIds, Loop.cost, two_mul] using hcQ
  · obtain ⟨P, hcP, hvP⟩ := one_free_period closed (C.text g) (C.letters closed g)
      (C.period g) I.card (C.periodic g) L l h hl hh (C.distinguished g) hsharp
    obtain ⟨Q, hcQ, _, hlQ⟩ := fill ⟨_, P⟩ hvP
    refine ⟨Q, ?_, hlQ⟩
    rw [card_groupIds]
    change Q.cost ≤ P.cost + I.card * C.period g at hcQ
    omega
  · intro hRank
    have hper : Function.Periodic (fun x => C.text target.1 (x + R.offset))
        (C.period target.1 : ℤ) := by
      intro x
      simpa only [add_right_comm] using C.periodic target.1 (x + R.offset)
    have hbelow : ∀ x, forward (fun x => C.text target.1 (x + R.offset)) x ≤
        forward (C.text g) (C.distinguished g) := by
      intro x
      rw [forward_shift]
      exact (C.distinguished_max target.1 (x + R.offset)).trans hRank
    obtain ⟨P, hcP, hvP, hs⟩ := cycle_collective_contact closed (C.text g)
      (fun x => C.text target.1 (x + R.offset)) (C.letters closed g)
      (C.period g) I.card (C.period target.1) (C.positive g) hk (C.positive target.1)
      (C.periodic g) hper L l h hl hh hat htb R.word_mem R.agree hne
      (C.distinguished_max g) hbelow hH hband hlast
    obtain ⟨Q, hcQ, hvQ, hlQ⟩ := fill ⟨_, P⟩ hvP
    refine ⟨Q, ?_, hlQ, hvQ _ (Path.visits_start P), ?_⟩
    · simp only [Loop.cost, hcP] at hcQ
      simpa only [card_groupIds, Loop.cost, two_mul] using hcQ
    · rcases hs with ⟨j, a, b, hf, hz, hlen⟩ | ⟨w, hw, hlen⟩
      · refine ⟨textWord (C.text g) a b, ?_, hlen⟩
        exact hlQ ⟨g, j.val⟩ (Finset.mem_map.mpr ⟨j.val, j.property, rfl⟩)
          _ ⟨a, b, hf, hz, rfl⟩
      · exact ⟨w, hvQ w hw, hlen⟩

end Superstring.Hierarchical.LayerCollection

namespace Superstring.Hierarchical.LayerCollection.PlannedBlock

variable {α G : Type} [LinearOrder α] {V : Set (List α)} {C : LayerCollection V G}

def reserve (B : C.PlannedBlock) : ℕ := 2 * (B.members.card * C.period B.source)

/-- Execute the concrete geometrically proved plans. Target ownership does
not require a disjointness assumption: any covering block can be chosen, and
every reserve is charged once. Group processing will prove the total budget. -/
theorem execute (closed : SubstringClosed V) (I : Finset C.PlannedBlock)
    (P : Path V [] [])
    (covered : ∀ i : C.Id, (∀ w ∈ (C.layerAt i).Content, P.Visits w) ∨
      ∃ B ∈ I, i ∈ B.members) :
    ∃ Q : Path V [] [], Q.cost ≤ P.cost + ∑ B ∈ I, B.reserve ∧
      (∀ w, P.Visits w → Q.Visits w) ∧
      ∀ i : C.Id, ∀ w ∈ (C.layerAt i).Content, Q.Visits w := by
  classical
  let target : C.PlannedBlock → Option C.PlannedBlock := fun B =>
    if h : ∃ D ∈ I, B.target ∈ D.members then some h.choose else none
  have spec : ∀ B D, target B = some D → D ∈ I ∧ B.target ∈ D.members := by
    intro B D he
    dsimp only [target] at he
    split_ifs at he with h
    · have hd : h.choose = D := Option.some.inj he
      exact hd ▸ h.choose_spec
  have no_spec : ∀ B, target B = none → ¬ ∃ D ∈ I, B.target ∈ D.members := by
    intro B he h
    simp [target, dite_eq_left h] at he
  let F : BlockPlan V C.PlannedBlock (Lex (ℕ → α)) := {
    content := fun B => B.content
    reserve := fun B => B.reserve
    free := fun B => C.period B.source
    rank := fun B => C.rank B.source
    target := target
    record := fun B => B.word
    target_mem := by
      intro B D he
      exact ⟨B.target, (spec B D he).2, B.word_content⟩
    link := by
      intro B
      obtain ⟨Q, hc, hv, hr⟩ := B.link
      exact ⟨Q, hc, fun w ⟨i, hi, hw⟩ => hv i hi w hw, hr⟩
    internal := by
      intro B
      obtain ⟨Q, hc, hv⟩ := B.internal
      exact ⟨Q, hc, fun w ⟨i, hi, hw⟩ => hv i hi w hw⟩
    short := by
      intro B D ht _ hr
      have hg := D.same B.target (spec B D ht).2
      obtain ⟨Q, hc, hv, hr, hs⟩ := B.short (by simpa only [hg] using hr)
      exact ⟨Q, hc, fun w ⟨i, hi, hw⟩ => hv i hi w hw, hr, by simpa only [hg] using hs⟩
    self_short := by
      intro B ht
      have hm := (spec B B ht).2
      exact ⟨B.word, ⟨B.target, hm, B.word_content⟩, B.same_short (B.same _ hm)⟩ }
  have ready : ∀ B ∈ I, match F.target B with
      | none => P.Visits (F.record B)
      | some D => D ∈ I ∨ P.Visits (F.record B) := by
    intro B _
    change match target B with
      | none => P.Visits B.word
      | some D => D ∈ I ∨ P.Visits B.word
    split <;> rename_i ht
    · rcases covered B.target with hroot | hblock
      · exact hroot B.word B.word_content
      · exact False.elim (no_spec B ht hblock)
    · exact Or.inl (spec B _ ht).1
  obtain ⟨Q, hcQ, hvQ, hbQ⟩ := F.connect closed I P (by
    intro B hB
    have hh := ready B hB
    cases h : F.target B <;> simpa only [h] using hh)
  refine ⟨Q, hcQ, hvQ, ?_⟩
  intro i w hw
  rcases covered i with hroot | ⟨B, hB, hi⟩
  · exact hvQ w (hroot w hw)
  · exact hbQ B hB w ⟨i, hi, hw⟩

end Superstring.Hierarchical.LayerCollection.PlannedBlock

end OAI
