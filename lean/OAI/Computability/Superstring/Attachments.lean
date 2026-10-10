import OAI.Computability.Superstring.Distribution

namespace OAI

namespace Superstring.Hierarchical.LayerCollection

variable {α G : Type} {V : Set (List α)} (C : LayerCollection V G)

/-- Complete one touched base layer and splice it into the rooted walk.
Only this layer's base turn and its one geometric connection are charged. -/
theorem attach_layer (closed : SubstringClosed V) (g : G) (i : Fin (C.size g))
    (P : Path V [] []) (F : Loop V) (hcF : F.cost ≤ C.period g)
    (ht : (C.layer g i).TouchedBy F.path) (hmeet : (Loop.mk [] P).Meets F) :
    ∃ Q : Path V [] [], Q.cost ≤ P.cost + 2 * C.period g ∧
      (∀ w, P.Visits w → Q.Visits w) ∧
      ∀ w ∈ (C.layer g i).Content, Q.Visits w := by
  obtain ⟨T, _, hcT, hvT, hlT⟩ := fill_same_layers closed (C.layer g) (C.positive g)
    (C.periodic g) {i} F (by simpa using ht)
  obtain ⟨w, hp, hf⟩ := hmeet
  obtain ⟨Q, hcQ, hvQ⟩ := P.splice T.path w hp (hvT w hf)
  refine ⟨Q, ?_, fun v hv => (hvQ v).mpr (Or.inl hv), fun v hv => ?_⟩
  · simp only [Finset.card_singleton, one_mul] at hcT
    change Q.cost = P.cost + T.cost at hcQ
    omega
  · exact (hvQ v).mpr (Or.inr (hlT i (Finset.mem_singleton_self i) v hv))

/-- Root each as-yet-unspent layer below the chosen recipient baseline. The
baseline itself is already fully retained by the incoming-request operation. -/
theorem root_below (closed : SubstringClosed V) (g : G) (base : Fin (C.size g))
    (P : Path V [] []) (hp : ∀ w ∈ (C.layer g base).Content, P.Visits w)
    (a b : ℤ) (hbf : (C.layer g base).first a ≤ b)
    (hbl : b ≤ (C.layer g base).last a) (hlen : b - a < 2 * C.period g)
    (I : Finset (Fin (C.size g))) (hbelow : ∀ i ∈ I, i ≤ base) :
    ∃ Q : Path V [] [], Q.cost ≤ P.cost + 2 * (I.card * C.period g) ∧
      (∀ w, P.Visits w → Q.Visits w) ∧
      ∀ i ∈ I, ∀ w ∈ (C.layer g i).Content, Q.Visits w := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨P, by simp, fun _ h => h, by simp⟩
  | @insert i I hi ih =>
    obtain ⟨Q, hcQ, hvQ, hlQ⟩ := ih (fun j hj => hbelow j (Finset.mem_insert_of_mem hj))
    have hqbase : Q.Visits (textWord (C.text g) a b) :=
      hvQ _ (hp _ ⟨a, b, hbf, hbl, rfl⟩)
    obtain ⟨F, hcF, htF, hmeet⟩ : ∃ F : Loop V,
        F.cost ≤ C.period g ∧ (C.layer g i).TouchedBy F.path ∧ (Loop.mk [] Q).Meets F := by
      rcases (C.layer g i).below_baseline (C.layer g base) closed (C.letters closed g)
        (C.periodic g) (C.ordered g i base (hbelow i (Finset.mem_insert_self i I)))
        hbf hbl hlen with ⟨F, hcF, htF⟩ | ⟨F, hcF, htF⟩
      · exact ⟨⟨[], F⟩, hcF, htF, [], Path.visits_start Q, Path.visits_start F⟩
      · exact ⟨⟨_, F⟩, hcF, htF, _, hqbase, Path.visits_start F⟩
    obtain ⟨T, hcT, hvT, hlT⟩ := C.attach_layer closed g i Q F hcF htF hmeet
    refine ⟨T, ?_, fun w hw => hvT w (hvQ w hw), ?_⟩
    · rw [Finset.card_insert_of_notMem hi, Nat.add_mul, Nat.one_mul, Nat.mul_add]
      omega
    · intro j hj w hw
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hlT w hw
      · exact hvT w (hlQ j hj w hw)

/-- Easy upper round-trip branch, including all upper base turns. -/
theorem root_upper_budget (closed : SubstringClosed V) (g : G)
    (I : Finset (Fin (C.size g))) (top : Fin (C.size g))
    (hupper : ∀ i ∈ I, i ≤ top) (t : ℤ)
    (hcost : (C.layer g top).first t - t ≤ (I.card * C.period g : ℕ)) :
    ∃ Q : Path V [] [], Q.cost ≤ 2 * (I.card * C.period g) ∧
      ∀ i ∈ I, ∀ w ∈ (C.layer g i).Content, Q.Visits w := by
  let L := fun i : Fin (C.size g) => C.layer g i
  have hall : ∀ j : {i // i ∈ insert top I}, ∀ x, (L j.val).z x ≤ (L top).z x := by
    intro j x
    rcases Finset.mem_insert.mp j.property with he | hj
    · rw [he]
    · exact C.ordered g j.val top (hupper j.val hj) x
  obtain ⟨P, hcP, htP⟩ := root_upper closed (fun j : {i // i ∈ insert top I} => L j.val)
    ⟨top, Finset.mem_insert_self top I⟩ hall t
  obtain ⟨Q, hbQ, hcQ, _, hvQ⟩ := fill_same_layers closed (C.layer g) (C.positive g)
    (C.periodic g) I ⟨[], P⟩ (fun i hi => htP ⟨i, Finset.mem_insert_of_mem hi⟩)
  refine ⟨Q.path.copy hbQ hbQ, ?_, fun i hi w hw => (Path.visits_copy ..).mpr (hvQ i hi w hw)⟩
  simp only [Path.cost_copy]
  change Q.cost ≤ _
  change Q.cost ≤ P.cost + I.card * C.period g at hcQ
  simp only [length_textWord] at hcP
  have ht := (C.layer g top).start_le_first t
  change P.cost = Int.toNat ((C.layer g top).first t - t) at hcP
  omega

/-- Easy upper band branch, paid only by upper layers, not by the already
rooted baseline's budget. -/
theorem attach_upper_band (closed : SubstringClosed V) (g : G)
    (I : Finset (Fin (C.size g))) (base top : Fin (C.size g))
    (horder : ∀ i ∈ I, base ≤ i ∧ i ≤ top) (hbt : base ≤ top)
    (P : Path V [] []) (hp : ∀ w ∈ (C.layer g base).Content, P.Visits w) (t : ℤ)
    (hband : (C.layer g top).first t - (C.layer g base).last t ≤ (I.card * C.period g : ℕ)) :
    ∃ Q : Path V [] [], Q.cost ≤ P.cost + 2 * (I.card * C.period g) ∧
      (∀ w, P.Visits w → Q.Visits w) ∧
      ∀ i ∈ I, ∀ w ∈ (C.layer g i).Content, Q.Visits w := by
  classical
  let J := insert base (insert top I)
  let L := fun j : {i // i ∈ J} => C.layer g j.val
  let lo : {i // i ∈ J} := ⟨base, Finset.mem_insert_self _ _⟩
  let hi : {i // i ∈ J} := ⟨top, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)⟩
  have ho : ∀ j : {i // i ∈ J}, base ≤ j.val ∧ j.val ≤ top := by
    intro j
    rcases Finset.mem_insert.mp j.property with he | hm
    · simpa only [he] using And.intro (le_refl base) hbt
    · rcases Finset.mem_insert.mp hm with he | hm
      · simpa only [he] using And.intro hbt (le_refl top)
      · exact horder j.val hm
  obtain ⟨F, hcF, htF⟩ := join_band closed (C.text g) (C.letters closed g)
    (C.period g) I.card (C.periodic g) L lo hi
    (fun j x => C.ordered g base j.val (ho j).1 x)
    (fun j x => C.ordered g j.val top (ho j).2 x) t hband
  obtain ⟨T, _, hcT, hvT, hlT⟩ := fill_same_layers closed (C.layer g) (C.positive g)
    (C.periodic g) I ⟨_, F⟩ (fun i hi => htF ⟨i, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hi)⟩)
  let w := textWord (C.text g) t ((C.layer g base).last t)
  have hwP : P.Visits w := hp w ⟨t, _, (C.layer g base).first_le_last t, le_rfl, rfl⟩
  have hwT : T.Visits w := hvT _ (Path.visits_start F)
  obtain ⟨Q, hcQ, hvQ⟩ := P.splice T.path w hwP hwT
  refine ⟨Q, ?_, fun v hv => (hvQ v).mpr (Or.inl hv), fun i hi v hv =>
    (hvQ v).mpr (Or.inr (hlT i hi v hv))⟩
  change T.cost ≤ F.cost + I.card * C.period g at hcT
  change Q.cost = P.cost + T.cost at hcQ
  omega

end Superstring.Hierarchical.LayerCollection

namespace Superstring.Hierarchical.LayerCollection

variable {α G : Type} {V : Set (List α)} (C : LayerCollection V G)


abbrev Pending := Σ d : C.Id, C.Child d

namespace Pending
variable {C} (r : C.Pending)
def source : G := r.2.source
def ids : Finset C.Id := r.2.ids
def reserve : ℕ := 2 * r.2.budget

theorem later : C.period r.source < C.period r.1.1 := r.2.later

theorem same (i : C.Id) (hi : i ∈ r.ids) : i.1 = r.source :=
  C.groupIds_same r.source r.2.members hi
end Pending

def upper (g : G) (cut : ℕ) : Finset (Fin (C.size g)) :=
  Finset.univ.filter (fun i => cut ≤ i.val)

@[simp] theorem mem_upper (g : G) (cut : ℕ) (i : Fin (C.size g)) :
    i ∈ C.upper g cut ↔ cut ≤ i.val := by simp [upper]

@[simp] theorem card_upper (g : G) (cut : ℕ) :
    (C.upper g cut).card = C.size g - cut := by
  by_cases hc : cut < C.size g
  · have he : C.upper g cut = Finset.Ici (⟨cut, hc⟩ : Fin (C.size g)) := by
      ext i
      simp only [mem_upper, Finset.mem_Ici, Fin.le_def]
    rw [he, Fin.card_Ici]
  · have he : C.upper g cut = ∅ := by
      ext i
      simp only [mem_upper, Finset.notMem_empty, iff_false]
      omega
    rw [he, Finset.card_empty]
    omega

variable [LinearOrder α]

def Covered (P : Path V [] []) (B : Finset C.PlannedBlock) (R : Finset C.Pending)
    (i : C.Id) : Prop :=
  (∀ w ∈ (C.layerAt i).Content, P.Visits w) ∨
    (∃ b ∈ B, i ∈ b.members) ∨ ∃ r ∈ R, i ∈ r.ids

/-- Complete exactly the unspent upper interval. The failed count test is
resolved by the proved record supply, not taken as a plan oracle. -/
theorem complete_upper (closed : SubstringClosed V) (supply : C.RecordSupply)
    (g : G) (cut : ℕ) (hcut : cut ≤ C.size g) (P : Path V [] [])
    (hp : ∀ i : Fin (C.size g), i.val < cut →
      ∀ w ∈ (C.layer g i).Content, P.Visits w) :
    ∃ (Q : Path V [] []) (B : Finset C.PlannedBlock) (R : Finset C.Pending),
      Q.cost + (∑ b ∈ B, b.reserve) + (∑ r ∈ R, r.reserve) ≤
        P.cost + 2 * ((C.size g - cut) * C.period g) ∧
      (∀ w, P.Visits w → Q.Visits w) ∧
      (∀ i ∈ C.upper g cut, C.Covered Q B R ⟨g, i⟩) ∧
      (∀ r ∈ R, r.source = g) ∧ R.card ≤ 1 := by
  classical
  let n := C.size g - cut
  let I := C.upper g cut
  have hcard : I.card = n := C.card_upper g cut
  by_cases hn : n = 0
  · refine ⟨P, ∅, ∅, by simp, fun _ h => h, ?_, by simp, by simp⟩
    intro i hi
    have hh := (C.mem_upper g cut i).mp hi
    have := i.isLt
    dsimp only [n] at hn
    omega
  have hnpos : 0 < n := by omega
  have hnm : n ≤ C.size g := Nat.sub_le _ _
  let top : Fin (C.size g) := ⟨C.size g - 1, by have := C.nonempty g; omega⟩
  let t := C.distinguished g
  let H := (C.layer g top).first t
  have htop : ∀ i ∈ I, i ≤ top := by
    intro i _
    change i.val ≤ C.size g - 1
    omega
  have easy (Q : Path V [] []) (hc : Q.cost ≤ P.cost + 2 * (n * C.period g))
      (hv : ∀ w, P.Visits w → Q.Visits w)
      (hi : ∀ i ∈ I, ∀ w ∈ (C.layer g i).Content, Q.Visits w) :
      ∃ (Q : Path V [] []) (B : Finset C.PlannedBlock) (R : Finset C.Pending),
        Q.cost + (∑ b ∈ B, b.reserve) + (∑ r ∈ R, r.reserve) ≤
          P.cost + 2 * ((C.size g - cut) * C.period g) ∧
        (∀ w, P.Visits w → Q.Visits w) ∧
        (∀ i ∈ C.upper g cut, C.Covered Q B R ⟨g, i⟩) ∧
        (∀ r ∈ R, r.source = g) ∧ R.card ≤ 1 := by
    exact ⟨Q, ∅, ∅, by simpa using hc, hv, fun i hm => Or.inl (hi i hm),
      by simp, by simp⟩
  by_cases he : H - t ≤ (n * C.period g : ℕ)
  · obtain ⟨Q, hcQ, hvQ⟩ := C.root_upper_budget closed g I top htop t (by simpa [hcard] using he)
    apply easy (P.trans Q)
    · rw [Path.cost_trans]
      rw [hcard] at hcQ
      omega
    · exact fun _ h => Or.inl h
    · exact fun i hi w hw => Or.inr (hvQ i hi w hw)
  have hz : Monotone (fun i : Fin (C.size g) => (C.layer g i).last t) := by
    intro i j hij
    exact C.ordered g i j hij t
  by_cases hb : ∃ base : Fin (C.size g), base.val + 1 = cut ∧
      H - (C.layer g base).last t ≤ (n * C.period g : ℕ)
  · obtain ⟨base, hbase, hband⟩ := hb
    obtain ⟨Q, hcQ, hvQ, hiQ⟩ := C.attach_upper_band closed g I base top
      (by intro i hi; exact ⟨by have hh := (C.mem_upper g cut i).mp hi; change base.val ≤ i.val; omega,
        htop i hi⟩)
      (by change base.val ≤ C.size g - 1; omega) P
      (hp base (by omega)) t (by simpa [hcard] using hband)
    exact easy Q (by simpa only [hcard] using hcQ) hvQ hiQ
  have hstopn : (Processing.qualifying (fun i => (C.layer g i).last t)
      H (C.period g) n).card ≤ n := by
    by_cases hzero : cut = 0
    · have hh := Finset.card_le_univ (Processing.qualifying
        (fun i => (C.layer g i).last t) H (C.period g) n)
      simpa only [Fintype.card_fin, n, hzero, Nat.sub_zero] using hh
    · let base : Fin (C.size g) := ⟨cut - 1, by omega⟩
      have hfail : (C.layer g base).last t < H - (n * C.period g : ℕ) := by
        by_contra hh
        apply hb
        exact ⟨base, by dsimp only [base]; omega, by omega⟩
      have hh := Processing.qualifying_bound _ hz H (C.period g) n base hfail
      change _ ≤ C.size g - 1 - (cut - 1) at hh
      dsimp only [n] at hh ⊢
      omega
  obtain ⟨k, hk, hkn, hstop, hsharp⟩ := Processing.choose_k hnpos hnm _ hz H
    (C.period g) ((C.layer g top).first_le_last t) hstopn
  have hkm : k ≤ C.size g := hkn.trans hnm
  have hmul : k * C.period g ≤ n * C.period g := Nat.mul_le_mul_right _ hkn
  have hhard : t + (k * C.period g : ℕ) < (C.layer g top).first t := by omega
  obtain ⟨d, R, ha, hh, hd⟩ := supply g top t k hk hhard hstop
  have ht : t < R.stop := by omega
  obtain ⟨Q, B, A, hcQ, hvQ, hAI, hlA, hmA⟩ := C.distribute_record closed g I k hk hkm
    (by intro i hi; apply (C.mem_upper g cut i).mpr; dsimp only [n] at hkn; omega)
    d R hd ha ht (by dsimp only [top, t, H] at hh ⊢; omega)
      (by dsimp only [top, t, H] at hsharp ⊢; omega) hstop
  have hhcost : (P.trans Q).cost + (∑ b ∈ B, b.reserve) + 2 * (A.card * C.period g) ≤
      P.cost + 2 * ((C.size g - cut) * C.period g) := by
    rw [Path.cost_trans]
    rw [hcard] at hcQ
    dsimp only [n] at hcQ
    omega
  by_cases hA : A.Nonempty
  · let r : C.Pending := ⟨d, {
      source := g
      members := A
      nonempty := hA
      record := R
      foreign := hd
      long := hlA
      margin := hmA }⟩
    refine ⟨P.trans Q, B, {r}, ?_, fun _ h => Or.inl h, ?_, ?_, by simp⟩
    · simpa [r, Pending.reserve, Child.budget] using hhcost
    · intro i hi
      rcases hvQ i hi with hv | hB | hiA
      · exact Or.inl (fun w hw => Or.inr (hv w hw))
      · exact Or.inr (Or.inl hB)
      · exact Or.inr (Or.inr ⟨r, Finset.mem_singleton_self _,
          Finset.mem_map.mpr ⟨i, hiA, rfl⟩⟩)
    · intro s hs
      have heq := Finset.mem_singleton.mp hs
      subst s
      rfl
  · have heA : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    refine ⟨P.trans Q, B, ∅, ?_, fun _ h => Or.inl h, ?_, by simp, by simp⟩
    · simpa only [heA, Finset.card_empty, Nat.zero_mul, Nat.mul_zero, add_zero,
        Finset.sum_empty] using hhcost
    · intro i hi
      rcases hvQ i hi with hv | hB | hiA
      · exact Or.inl (fun w hw => Or.inr (hv w hw))
      · exact Or.inr (Or.inl hB)
      · simp only [heA, Finset.notMem_empty] at hiA

end Superstring.Hierarchical.LayerCollection

namespace Superstring.Hierarchical.LayerCollection

variable {α G : Type} {V : Set (List α)} (C : LayerCollection V G)

namespace Pending
variable {C} (r : C.Pending)

def onTarget (d : C.Id) (h : r.1 = d) : C.Child d := h ▸ r.2

@[simp] theorem at_source (d : C.Id) (h : r.1 = d) : (r.onTarget d h).source = r.source := by
  cases h
  rfl

@[simp] theorem at_budget (d : C.Id) (h : r.1 = d) : 2 * (r.onTarget d h).budget = r.reserve := by
  cases h
  rfl

@[simp] theorem at_ids (d : C.Id) (h : r.1 = d) : (r.onTarget d h).ids = r.ids := by
  cases h
  rfl

end Pending

/-- Fulfill precisely the pending requests on one fixed recipient. -/
theorem fulfill_fibre (closed : SubstringClosed V) (d : C.Id) (R : Finset C.Pending)
    (hne : R.Nonempty) (ht : ∀ r ∈ R, r.1 = d)
    (distinct : Set.InjOn Pending.source (R : Set C.Pending)) :
    ∃ Q : Path V [] [], Q.cost ≤ 2 * C.period d.1 + ∑ r ∈ R, r.reserve ∧
      (∀ w ∈ (C.layerAt d).Content, Q.Visits w) ∧
      ∀ r ∈ R, ∀ i ∈ r.ids, ∀ w ∈ (C.layerAt i).Content, Q.Visits w := by
  classical
  let ι := {r // r ∈ R}
  let : Nonempty ι := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  let F : ι → C.Child d := fun r => r.val.onTarget d (ht r.val r.property)
  have hd : Function.Injective (fun r => (F r).source) := by
    intro r s he
    apply Subtype.ext
    apply distinct r.property s.property
    simpa only [F, Pending.at_source] using he
  obtain ⟨Q, hc, hv, hr⟩ := C.fulfill closed d F hd
  have hsum : 2 * ∑ r : ι, (F r).budget = ∑ r ∈ R, r.reserve := by
    rw [Finset.mul_sum]
    simp only [F, Pending.at_budget]
    exact (Finset.sum_subtype R (fun _ => Iff.rfl) Pending.reserve).symm
  refine ⟨Q, by simpa only [hsum] using hc, hv, ?_⟩
  intro r hrR i hi w hw
  have hiF : i ∈ (F ⟨r, hrR⟩).ids := by simpa only [F, Pending.at_ids] using hi
  obtain ⟨j, hj, he⟩ := Finset.mem_map.mp hiF
  subst i
  exact hr ⟨r, hrR⟩ j hj w hw


theorem fulfill_all (closed : SubstringClosed V) (g : G) (R : Finset C.Pending)
    (targets : ∀ r ∈ R, r.1.1 = g)
    (distinct : Set.InjOn Pending.source (R : Set C.Pending)) :
    ∃ (Q : Path V [] []) (J : Finset (Fin (C.size g))),
      Q.cost ≤ 2 * (J.card * C.period g) + ∑ r ∈ R, r.reserve ∧
      (∀ j ∈ J, ∀ w ∈ (C.layer g j).Content, Q.Visits w) ∧
      (∀ r ∈ R, ∀ i ∈ r.ids, ∀ w ∈ (C.layerAt i).Content, Q.Visits w) ∧
      (∀ j ∈ J, ∃ a b : ℤ, (C.layer g j).first a ≤ b ∧
        b ≤ (C.layer g j).last a ∧ b - a < 2 * C.period g) ∧
      (J = ∅ ↔ R = ∅) := by
  classical
  let J : Finset (Fin (C.size g)) := Finset.univ.filter
    (fun j => ∃ r ∈ R, r.1 = ⟨g, j⟩)
  let fibre := fun j => R.filter (fun r => r.1 = ⟨g, j⟩)
  have hJ : ∀ j, j ∈ J ↔ ∃ r ∈ R, r.1 = ⟨g, j⟩ := by simp [J]
  have recipient : ∀ r ∈ R, ∃ j : Fin (C.size g), r.1 = ⟨g, j⟩ := by
    intro r hr
    obtain ⟨⟨a, j⟩, c⟩ := r
    have he := targets ⟨⟨a, j⟩, c⟩ hr
    change a = g at he
    subst a
    exact ⟨j, rfl⟩
  have hex : ∀ j ∈ J, ∃ Q : Path V [] [],
      Q.cost ≤ 2 * C.period g + ∑ r ∈ fibre j, r.reserve ∧
      (∀ w ∈ (C.layer g j).Content, Q.Visits w) ∧
      ∀ r ∈ fibre j, ∀ i ∈ r.ids, ∀ w ∈ (C.layerAt i).Content, Q.Visits w := by
    intro j hj
    obtain ⟨r, hr, ht⟩ := (hJ j).mp hj
    exact C.fulfill_fibre closed ⟨g, j⟩ (fibre j)
      ⟨r, Finset.mem_filter.mpr ⟨hr, ht⟩⟩
      (fun _ h => (Finset.mem_filter.mp h).2)
      (distinct.mono (by intro r hr; exact (Finset.mem_filter.mp hr).1))
  let F : Fin (C.size g) → Path V [] [] := fun j =>
    if h : j ∈ J then (hex j h).choose else .nil [] (C.empty_mem closed g)
  have hF : ∀ j ∈ J,
      (F j).cost ≤ 2 * C.period g + ∑ r ∈ fibre j, r.reserve ∧
      (∀ w ∈ (C.layer g j).Content, (F j).Visits w) ∧
      ∀ r ∈ fibre j, ∀ i ∈ r.ids, ∀ w ∈ (C.layerAt i).Content, (F j).Visits w := by
    intro j hj
    simpa only [F, dite_eq_left hj] using (hex j hj).choose_spec
  have hsum : ∑ j ∈ J, ∑ r ∈ fibre j, r.reserve = ∑ r ∈ R, r.reserve := by
    simp only [fibre, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r hr
    obtain ⟨j, hj⟩ := recipient r hr
    have hjJ : j ∈ J := (hJ j).mpr ⟨r, hr, hj⟩
    rw [Finset.sum_eq_single j]
    · simp only [hj, ↓reduceIte]
    · intro k _ hkj
      have hne : r.1 ≠ ⟨g, k⟩ := by
        intro he
        have hh : j = k := by simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hj.symm.trans he
        exact hkj hh.symm
      simp only [hne, ↓reduceIte]
    · exact fun h => False.elim (h hjJ)
  obtain ⟨Q, hcQ, hvQ⟩ := combine_rooted (C.empty_mem closed g) F J
  refine ⟨Q, J, ?_, ?_, ?_, ?_, ?_⟩
  · have hh := Finset.sum_le_sum (fun j hj => (hF j hj).1)
    have he : (∑ j ∈ J, (2 * C.period g + ∑ r ∈ fibre j, r.reserve)) =
        2 * (J.card * C.period g) + ∑ r ∈ R, r.reserve := by
      rw [Finset.sum_add_distrib, hsum]
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
      ring
    rw [he] at hh
    exact hcQ.trans hh
  · intro j hj w hw
    exact hvQ j hj w ((hF j hj).2.1 w hw)
  · intro r hr i hi w hw
    obtain ⟨j, hj⟩ := recipient r hr
    have hjJ : j ∈ J := (hJ j).mpr ⟨r, hr, hj⟩
    exact hvQ j hjJ w ((hF j hjJ).2.2 r (Finset.mem_filter.mpr ⟨hr, hj⟩) i hi w hw)
  · intro j hj
    obtain ⟨r, hr, ht⟩ := (hJ j).mp hj
    let c := r.onTarget ⟨g, j⟩ ht
    refine ⟨c.record.start + c.record.offset, c.record.stop + c.record.offset,
      c.record.first_le, c.record.le_last, ?_⟩
    have hl := c.record.length_lt (C.positive c.source) (C.positive g)
      (C.periodic c.source) (C.periodic g) c.foreign
    have hp := c.later
    change c.record.stop - c.record.start < (C.period c.source : ℤ) + C.period g at hl
    change C.period c.source < C.period g at hp
    omega
  · constructor
    · intro he
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro r hr
      obtain ⟨j, hj⟩ := recipient r hr
      have hm := (hJ j).mpr ⟨r, hr, hj⟩
      simp only [he, Finset.notMem_empty] at hm
    · intro he
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      obtain ⟨r, hr, _⟩ := (hJ j).mp hj
      simp only [he, Finset.notMem_empty] at hr

end Superstring.Hierarchical.LayerCollection

end OAI
