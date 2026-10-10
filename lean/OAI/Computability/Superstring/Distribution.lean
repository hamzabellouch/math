import OAI.Computability.Superstring.Collections

namespace OAI

namespace Superstring.Hierarchical.LayerCollection

variable {α G : Type} {V : Set (List α)} (C : LayerCollection V G)


structure Child (d : C.Id) where
  source : G
  members : Finset (Fin (C.size source))
  nonempty : members.Nonempty
  record : (C.layerAt d).Record (C.text source)
  foreign : C.text source ≠ fun x => C.text d.1 (x + record.offset)
  long : ∀ i ∈ members, record.start + C.period source < (C.layer source i).first record.start
  margin : ∀ i ∈ members, (C.layer source i).last record.start < record.stop - C.period source

namespace Child

variable {C} {d : C.Id} (R : C.Child d)

def ids : Finset C.Id := C.groupIds R.source R.members

def budget : ℕ := R.members.card * C.period R.source

theorem later : C.period R.source < C.period d.1 := by
  obtain ⟨i, hi⟩ := R.nonempty
  have hl := R.long i hi
  have hm := R.margin i hi
  have hf := (C.layer R.source i).first_le_last R.record.start
  have hb := R.record.length_lt (C.positive R.source) (C.positive d.1)
    (C.periodic R.source) (C.periodic d.1) R.foreign
  omega


def hosted : HostedGroup (C.layerAt d) where
  text := fun x => C.text R.source (x - R.record.offset)
  period := C.period R.source
  positive := C.positive R.source
  periodic := fun x => by
    simpa only [add_sub_right_comm] using C.periodic R.source (x - R.record.offset)
  start := R.record.start + R.record.offset
  stop := R.record.stop + R.record.offset
  first_le := R.record.first_le
  le_last := R.record.le_last
  agree := by
    intro x hx hy
    have hh := R.record.agree (x - R.record.offset) (by omega) (by omega)
    simpa only [sub_add_cancel] using hh
  foreign := by
    intro he
    apply R.foreign
    funext x
    simpa only [add_sub_cancel_right] using congrFun he (x + R.record.offset)

def request (i : {j // j ∈ R.members}) : R.hosted.Request where
  layer := (C.layer R.source i.val).translate R.record.offset
  stop := (C.layer R.source i.val).first R.record.start + R.record.offset
  first_le := by simp [hosted]
  le_last := by
    simp only [hosted, Layer.translate_last, add_sub_cancel_right]
    have hf := (C.layer R.source i.val).first_le_last R.record.start
    omega
  long := by
    have hh := R.long i.val i.property
    change R.record.start + R.record.offset + C.period R.source < _
    omega
  margin := by
    have hh := R.margin i.val i.property
    have hf := (C.layer R.source i.val).first_le_last R.record.start
    change _ ≤ R.record.stop + R.record.offset - C.period R.source
    omega

theorem hosted_different (S : C.Child d) (hne : R.source ≠ S.source) (c : ℤ) :
    R.hosted.text ≠ fun x => S.hosted.text (x + c) := by
  intro he
  apply C.different R.source S.source hne (R.record.offset + c - S.record.offset)
  funext x
  have hh := congrFun he (x + R.record.offset)
  change C.text R.source (x + R.record.offset - R.record.offset) =
    C.text S.source (x + R.record.offset + c - S.record.offset) at hh
  have hx : x + R.record.offset + c - S.record.offset =
      x + (R.record.offset + c - S.record.offset) := by omega
  simpa only [add_sub_cancel_right, hx] using hh

end Child

/-- A nonempty collection of actual child groups can be fulfilled together.
The reserve includes the original turn of every requesting layer and of the
recipient. No other layer of the recipient group is charged or rooted here. -/
theorem fulfill {ι : Type} [Fintype ι] [Nonempty ι]
    (closed : SubstringClosed V) (d : C.Id) (R : ι → C.Child d)
    (distinct : Function.Injective (fun i => (R i).source)) :
    ∃ Q : Path V [] [], Q.cost ≤ 2 * C.period d.1 + 2 * ∑ i, (R i).budget ∧
      (∀ w ∈ (C.layerAt d).Content, Q.Visits w) ∧
      ∀ j i, i ∈ (R j).members → ∀ w ∈ (C.layer (R j).source i).Content, Q.Visits w := by
  classical
  let K := Σ j : ι, {i // i ∈ (R j).members}
  let child : K → ι := fun k => k.1
  let req := fun k : K => (R k.1).request k.2
  have hK : (Finset.univ : Finset K).Nonempty := by
    obtain ⟨j⟩ := ‹Nonempty ι›
    obtain ⟨i, hi⟩ := (R j).nonempty
    exact ⟨⟨j, i, hi⟩, Finset.mem_univ _⟩
  have budget_sum : (∑ k : K, C.period (R k.1).source) = ∑ j, (R j).budget := by
    simp only [K, Fintype.sum_sigma, Finset.sum_const, Finset.card_univ,
      Fintype.card_coe, smul_eq_mul, Child.budget]
  obtain ⟨P, hcP, hdP, hrP⟩ := host_requests closed (C.layerAt d) (C.positive d.1)
    (C.periodic d.1) (C.letters closed d.1) (fun j => (R j).hosted) child req
    (fun j x => C.letters closed (R j).source (x - (R j).record.offset))
    (fun i j hij c => (R i).hosted_different (R j) (fun he => hij (distinct he)) c)
    Finset.univ hK
  obtain ⟨Q, hbQ, hcQ, hvQ, hdQ⟩ := fill_same_layers closed (fun _ : Unit => C.layerAt d)
    (C.positive d.1) (C.periodic d.1) {()} ⟨[], P⟩ (fun _ _ => hdP)
  obtain ⟨T, hbT, hcT, hvT, hrT⟩ := fill_layers closed (fun k : K => (req k).layer)
    (fun k => C.positive (R k.1).source) (fun k => (R k.1).hosted.periodic) Finset.univ Q
    (fun k hk => by
      obtain ⟨x, e, hf, hl, hp⟩ := hrP k hk
      exact ⟨x, e, hf, hl, hvQ _ hp⟩)
  have hbase : T.base = [] := hbT.trans hbQ
  refine ⟨T.path.copy hbase hbase, ?_, ?_, ?_⟩
  · simp only [Path.cost_copy]
    change T.cost ≤ _
    simp only [Finset.card_singleton, one_mul] at hcQ
    change Q.cost ≤ P.cost + C.period d.1 at hcQ
    change P.cost ≤ C.period d.1 + ∑ k : K, C.period (R k.1).source at hcP
    change T.cost ≤ Q.cost + ∑ k : K, C.period (R k.1).source at hcT
    rw [budget_sum] at hcP hcT
    omega
  · intro w hw
    exact (Path.visits_copy ..).mpr (hvT w (hdQ () (Finset.mem_singleton_self ()) w hw))
  · intro j i hi w hw
    apply (Path.visits_copy ..).mpr
    apply hrT ⟨j, i, hi⟩ (Finset.mem_univ _) w
    change w ∈ ((C.layer (R j).source i).translate (R j).record.offset).Content
    rwa [Layer.translate_content]

end Superstring.Hierarchical.LayerCollection

namespace Superstring.Hierarchical

/-- Concatenate a finite family of rooted closed walks, preserving every
visit and charging at most their sum. Abstracted only to avoid repeated splices. -/
theorem combine_rooted {α ι : Type} {V : Set (List α)} (he : [] ∈ V)
    (F : ι → Path V [] []) (I : Finset ι) :
    ∃ Q : Path V [] [], Q.cost ≤ ∑ i ∈ I, (F i).cost ∧
      ∀ i ∈ I, ∀ w, (F i).Visits w → Q.Visits w := by
  apply Loop.of_connected (fun i => ⟨[], F i⟩) I [] he
  intro U hU hclosed i hi w hw
  exact hclosed i hi ⟨[], hU, Path.visits_start (F i)⟩ w hw

namespace LayerCollection

variable {α G : Type} {V : Set (List α)} (C : LayerCollection V G)

include C in
theorem empty_mem (closed : SubstringClosed V) (g : G) : [] ∈ V :=
  closed (C.letters closed g 0) List.nil_infix

theorem root_short (closed : SubstringClosed V) (g : G) (i : Fin (C.size g))
    (hs : (C.layer g i).HasShort (C.period g)) :
    ∃ Q : Path V [] [], Q.cost ≤ 2 * C.period g ∧
      ∀ w ∈ (C.layer g i).Content, Q.Visits w := by
  obtain ⟨x, e, hf, hl, hc⟩ := hs
  obtain ⟨P, hcP, hvP⟩ := Path.root_loop closed _ ((C.layer g i).actual x e hf hl)
  obtain ⟨Q, hbQ, hcQ, _, hvQ⟩ := fill_same_layers closed (C.layer g) (C.positive g)
    (C.periodic g) {i} ⟨[], P⟩ (by
      intro j hj
      have he : j = i := Finset.mem_singleton.mp hj
      subst j
      exact ⟨x, e, hf, hl, hvP⟩)
  refine ⟨Q.path.copy hbQ hbQ, ?_, fun w hw => (Path.visits_copy ..).mpr
    (hvQ i (Finset.mem_singleton_self i) w hw)⟩
  simp only [Path.cost_copy]
  change Q.cost ≤ _
  simp only [Finset.card_singleton, one_mul] at hcQ
  change Q.cost ≤ P.cost + C.period g at hcQ
  omega

end LayerCollection
end Superstring.Hierarchical

namespace Superstring.Hierarchical.Processing

/-- Once the cardinality test stops, every layer strictly below the top k
has last end strictly below the tested threshold. -/
theorem below_stopped {m : ℕ} (z : Fin m → ℤ) (hz : Monotone z) (H : ℤ) (p k : ℕ)
    (hstop : (qualifying z H p k).card ≤ k) (i : Fin m) (hi : i.val < m - k) :
    z i < H - (k * p : ℕ) := by
  by_contra hh
  have hsub : Finset.Ici i ⊆ qualifying z H p k := by
    intro j hj
    simp only [qualifying, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (le_of_not_gt hh).trans (hz (Finset.mem_Ici.mp hj))
  have hc := Finset.card_le_card hsub
  rw [Fin.card_Ici] at hc
  omega

end Superstring.Hierarchical.Processing

namespace Superstring.Hierarchical.LayerCollection

variable {α G : Type} [LinearOrder α] {V : Set (List α)} (C : LayerCollection V G)


theorem distribute_individuals (closed : SubstringClosed V) (g : G)
    (d : C.Id) (R : (C.layerAt d).Record (C.text g))
    (foreign : C.text g ≠ fun x => C.text d.1 (x + R.offset))
    (I : Finset (Fin (C.size g)))
    (hfirst : ∀ i ∈ I, (C.layer g i).first R.start ≤ R.stop) :
    ∃ (Q : Path V [] []) (B : Finset C.PlannedBlock) (A : Finset (Fin (C.size g))),
      Q.cost + (∑ b ∈ B, b.reserve) + 2 * (A.card * C.period g) ≤ 2 * (I.card * C.period g) ∧
      (∀ i ∈ I, (∀ w ∈ (C.layer g i).Content, Q.Visits w) ∨
        (∃ b ∈ B, (⟨g, i⟩ : C.Id) ∈ b.members) ∨ i ∈ A) ∧
      A ⊆ I ∧
      (∀ i ∈ A, R.start + C.period g < (C.layer g i).first R.start) ∧
      (∀ i ∈ A, (C.layer g i).last R.start < R.stop - C.period g) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    exact ⟨.nil [] (C.empty_mem closed g), ∅, ∅, by simp [Path.cost],
      by simp, by simp, by simp, by simp⟩
  | @insert i I hi ih =>
    obtain ⟨Q, B, A, hcQ, hvQ, hAI, hlong, hmargin⟩ := ih
      (fun j hj => hfirst j (Finset.mem_insert_of_mem hj))
    have hcard : 2 * ((insert i I).card * C.period g) =
        2 * (I.card * C.period g) + 2 * C.period g := by
      rw [Finset.card_insert_of_notMem hi, Nat.add_mul, Nat.one_mul, Nat.mul_add]
    have lift_cover (T : Path V [] []) (B' : Finset C.PlannedBlock)
        (A' : Finset (Fin (C.size g)))
        (hP : ∀ w, Q.Visits w → T.Visits w) (hB : B ⊆ B') (hA : A ⊆ A')
        (hv : (∀ w ∈ (C.layer g i).Content, T.Visits w) ∨
          (∃ b ∈ B', (⟨g, i⟩ : C.Id) ∈ b.members) ∨ i ∈ A') :
        ∀ j ∈ insert i I, (∀ w ∈ (C.layer g j).Content, T.Visits w) ∨
          (∃ b ∈ B', (⟨g, j⟩ : C.Id) ∈ b.members) ∨ j ∈ A' := by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hv
      · rcases hvQ j hj with hp | ⟨b, hb, hm⟩ | ha
        · exact Or.inl (fun w hw => hP w (hp w hw))
        · exact Or.inr (Or.inl ⟨b, hB hb, hm⟩)
        · exact Or.inr (Or.inr (hA ha))
    by_cases hs : (C.layer g i).HasShort (C.period g)
    · obtain ⟨P, hcP, hvP⟩ := C.root_short closed g i hs
      refine ⟨Q.trans P, B, A, ?_, lift_cover _ _ _ (fun _ h => Or.inl h)
        (fun _ h => h) (fun _ h => h) (Or.inl (fun w hw => Or.inr (hvP w hw))),
        hAI.trans (Finset.subset_insert i I), hlong, hmargin⟩
      rw [Path.cost_trans, hcard]
      omega
    · by_cases ht : R.stop ≤ (C.layer g i).last R.start + C.period g
      · let b := C.individualPlan closed g i d R foreign
          (hfirst i (Finset.mem_insert_self i I)) ht
        have hbc : b.reserve = 2 * C.period g := by
          simp [b, individualPlan, PlannedBlock.reserve]
        have hsum : (∑ x ∈ insert b B, x.reserve) ≤ b.reserve + ∑ x ∈ B, x.reserve := by
          by_cases hb : b ∈ B
          · rw [Finset.insert_eq_of_mem hb]
            omega
          · rw [Finset.sum_insert hb]
        have hmem : (⟨g, i⟩ : C.Id) ∈ b.members := by
          exact Finset.mem_map.mpr ⟨i, Finset.mem_singleton_self i, rfl⟩
        refine ⟨Q, insert b B, A, ?_, lift_cover _ _ _ (fun _ h => h)
          (Finset.subset_insert b B) (fun _ h => h)
          (Or.inr (Or.inl ⟨b, Finset.mem_insert_self b B, hmem⟩)),
          hAI.trans (Finset.subset_insert i I), hlong, hmargin⟩
        rw [hcard]
        omega
      · have hni : i ∉ A := fun hm => hi (hAI hm)
        have hl := (C.layer g i).first_long_of_not_short (C.period g) hs R.start
        refine ⟨Q, B, insert i A, ?_, lift_cover _ _ _ (fun _ h => h)
          (fun _ h => h) (Finset.subset_insert i A)
          (Or.inr (Or.inr (Finset.mem_insert_self i A))),
          Finset.insert_subset_insert i hAI, ?_, ?_⟩
        · rw [Finset.card_insert_of_notMem hni, Nat.add_mul, Nat.one_mul, Nat.mul_add, hcard]
          omega
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · omega
          · exact hlong j hj
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · omega
          · exact hmargin j hj

end Superstring.Hierarchical.LayerCollection

namespace Superstring.Hierarchical.LayerCollection

variable {α G : Type} [LinearOrder α] {V : Set (List α)} (C : LayerCollection V G)

/-- The hard-case distribution, using the ONE record already forced by the
count rule. Collective and uncollected individual budgets are disjoint. -/
theorem distribute_record (closed : SubstringClosed V) (g : G)
    (I : Finset (Fin (C.size g))) (k : ℕ) (hk : 0 < k) (hkm : k ≤ C.size g)
    (hI : ∀ i : Fin (C.size g), C.size g - k ≤ i.val → i ∈ I)
    (d : C.Id) (R : (C.layerAt d).Record (C.text g))
    (foreign : C.text g ≠ fun x => C.text d.1 (x + R.offset))
    (hat : R.start ≤ C.distinguished g) (htb : C.distinguished g < R.stop)
    (hb : (C.layer g ⟨C.size g - 1, by have := C.nonempty g; omega⟩).first (C.distinguished g)
      ≤ R.stop + (k * C.period g : ℕ))
    (hsharp : (C.layer g ⟨C.size g - 1, by have := C.nonempty g; omega⟩).first (C.distinguished g) -
      (C.layer g ⟨C.size g - k, by omega⟩).last (C.distinguished g) ≤ ((k - 1) * C.period g : ℕ))
    (hstop : (Processing.qualifying (fun j => (C.layer g j).last (C.distinguished g))
      ((C.layer g ⟨C.size g - 1, by have := C.nonempty g; omega⟩).first (C.distinguished g))
      (C.period g) k).card ≤ k) :
    ∃ (Q : Path V [] []) (B : Finset C.PlannedBlock) (A : Finset (Fin (C.size g))),
      Q.cost + (∑ b ∈ B, b.reserve) + 2 * (A.card * C.period g) ≤ 2 * (I.card * C.period g) ∧
      (∀ i ∈ I, (∀ w ∈ (C.layer g i).Content, Q.Visits w) ∨
        (∃ b ∈ B, (⟨g, i⟩ : C.Id) ∈ b.members) ∨ i ∈ A) ∧
      A ⊆ I ∧
      (∀ i ∈ A, R.start + C.period g < (C.layer g i).first R.start) ∧
      (∀ i ∈ A, (C.layer g i).last R.start < R.stop - C.period g) := by
  classical
  let top : Fin (C.size g) := ⟨C.size g - 1, by have := C.nonempty g; omega⟩
  let lo : Fin (C.size g) := ⟨C.size g - k, by omega⟩
  let J := Finset.Ici lo
  have hJcard : J.card = k := by simp only [J, Fin.card_Ici, lo]; omega
  have hJI : J ⊆ I := by
    intro i hi
    have hh : lo ≤ i := Finset.mem_Ici.mp hi
    exact hI i hh
  have htop : ∀ i : Fin (C.size g), i ≤ top := by
    intro i
    change i.val ≤ C.size g - 1
    omega
  have hlo : lo ∈ J := Finset.mem_Ici.mpr le_rfl
  have hhi : top ∈ J := Finset.mem_Ici.mpr (htop lo)
  have first_below : ∀ i : Fin (C.size g), i ∉ J → (C.layer g i).first R.start ≤ R.stop := by
    intro i hi
    have hil : i.val < C.size g - k := by
      have hh : ¬ lo ≤ i := fun h => hi (Finset.mem_Ici.mpr h)
      change ¬ C.size g - k ≤ i.val at hh
      omega
    have hh := Processing.below_stopped (fun j => (C.layer g j).last (C.distinguished g))
      (fun i j hij => C.ordered g i j hij _) ((C.layer g top).first (C.distinguished g))
      (C.period g) k hstop i hil
    have hfa := (C.layer g i).first_mono hat
    have hfl := (C.layer g i).first_le_last (C.distinguished g)
    change (C.layer g top).first (C.distinguished g) ≤ _ at hb
    omega
  by_cases hcollect : R.stop ≤ (C.layer g lo).last R.start + (k * C.period g : ℕ)
  · let b := C.collectivePlan closed g J lo top hlo hhi
      (fun _ hj => Finset.mem_Ici.mp hj) (fun i _ => htop i) d R foreign hat htb
      (by simpa only [hJcard] using hsharp) (by simpa only [hJcard] using hb)
      (by simpa only [hJcard] using hcollect)
    obtain ⟨Q, B, A, hcQ, hvQ, hA, hlong, hmargin⟩ := C.distribute_individuals closed g d R foreign
      (I \ J) (fun i hi => first_below i (Finset.mem_sdiff.mp hi).2)
    have hbc : b.reserve = 2 * (k * C.period g) := by
      simp only [b, collectivePlan, PlannedBlock.reserve, card_groupIds, hJcard]
    have hsum : (∑ x ∈ insert b B, x.reserve) ≤ b.reserve + ∑ x ∈ B, x.reserve := by
      by_cases hb : b ∈ B
      · rw [Finset.insert_eq_of_mem hb]; omega
      · rw [Finset.sum_insert hb]
    have hcard := Finset.card_sdiff_add_card_eq_card hJI
    have hcost : 2 * ((I \ J).card * C.period g) + 2 * (k * C.period g) =
        2 * (I.card * C.period g) := by
      rw [← Nat.mul_add, ← Nat.add_mul, ← hJcard, hcard]
    refine ⟨Q, insert b B, A, by omega, ?_, hA.trans Finset.sdiff_subset, hlong, hmargin⟩
    intro i hi
    by_cases hij : i ∈ J
    · exact Or.inr (Or.inl ⟨b, Finset.mem_insert_self b B,
        Finset.mem_map.mpr ⟨i, hij, rfl⟩⟩)
    · rcases hvQ i (Finset.mem_sdiff.mpr ⟨hi, hij⟩) with hr | ⟨x, hx, hm⟩ | ha
      · exact Or.inl hr
      · exact Or.inr (Or.inl ⟨x, Finset.mem_insert_of_mem hx, hm⟩)
      · exact Or.inr (Or.inr ha)
  · apply C.distribute_individuals closed g d R foreign I
    intro i _
    have hw := Processing.wide_band (C.layer g top) (C.layer g lo)
      (C.positive g) hk (C.distinguished g) hsharp R.start
    have hu := C.ordered g i top (htop i) (R.start - 1)
    change (C.layer g i).first R.start ≤ (C.layer g top).first R.start at hu
    omega

end Superstring.Hierarchical.LayerCollection

namespace Superstring.Hierarchical.Threading

variable {α ι : Type} [Fintype ι] {V : Set (List α)}

/-- The finite ordered collection is the actual sorted base decomposition,
not an arbitrary family substituted for its multiplicities. -/
noncomputable def collection (T : Threading V ι) (closed : SubstringClosed V) :
    LayerCollection V T.Groups where
  text := T.groupText
  period := T.groupPeriod
  size := fun g => Fintype.card (T.Aligned (T.groupText g))
  positive := fun g => (T.primitive_group g).positive
  nonempty := fun g => Fintype.card_pos_iff.mpr ⟨⟨Quotient.out g, rfl⟩⟩
  periodic := fun g => (T.primitive_group g).periodic
  layer := fun g j => T.layerAt closed ⟨g, j⟩
  ordered := fun g i j hij x => T.layers_ordered (T.groupText g) i j hij x
  different := by
    intro g h hne c he
    apply hne
    exact (T.group_eq_of_alignment g h c 0 (fun x => by
      simpa only [add_zero] using (congrFun he x).symm)).symm

end Superstring.Hierarchical.Threading

namespace Superstring.Hierarchical.LayerCollection

variable {α G : Type} {V : Set (List α)} (C : LayerCollection V G)


def RecordSupply : Prop :=
  ∀ (g : G) (j : Fin (C.size g)) (t : ℤ) (k : ℕ), 0 < k →
    t + (k * C.period g : ℕ) < (C.layer g j).first t →
    (Processing.qualifying (fun l => (C.layer g l).last t)
      ((C.layer g j).first t) (C.period g) k).card ≤ k →
    ∃ d : C.Id, ∃ R : (C.layerAt d).Record (C.text g),
      R.start ≤ t ∧ (C.layer g j).first t - (k * C.period g : ℕ) ≤ R.stop ∧
      C.text g ≠ fun x => C.text d.1 (x + R.offset)

end Superstring.Hierarchical.LayerCollection

namespace Superstring.Counts.Data

variable {α : Type} [DecidableEq α] [Inhabited α]

theorem collection_records (D : Data α) (hD : D.WellFormed) :
    ((D.threading hD).collection hD.closed).RecordSupply := by
  intro g j t k hk hh hs
  obtain ⟨d, R, ha, hb, hd, _⟩ := D.hard_case_record hD g j t k hk hh hs
  exact ⟨d, R, ha, hb, hd⟩

end Superstring.Counts.Data

end OAI
