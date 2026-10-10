import OAI.Computability.WLIdentification.BinaryAddresses

namespace OAI

namespace WLIdentification

namespace BinaryAddress

def carryMap {d : ℕ} (h : Fin d) : ProductMap d where
  domain i := if i < h then {true} else if i = h then {false} else Finset.univ
  nonempty i := by split <;> first | exact Finset.singleton_nonempty _ | split <;> simp
  mapping i b := if i ≤ h then !b else b
  injective i _ _ _ _ he := by
    by_cases hi : i ≤ h
    · simpa only [hi, ite_true, Bool.not_not] using congrArg (fun b => !b) he
    · simpa only [hi, ite_false] using he

@[simp] theorem carryMap_rel {d : ℕ} (h : Fin d) (x y : Bits d) :
    (carryMap h).Rel x y ↔ Carry h true x ∧ y = flipPrefix h x := by
  change ((∀ i, x i ∈ if i < h then {true} else if i = h then {false} else Finset.univ) ∧
    (∀ i, (if i ≤ h then !(x i) else x i) = y i)) ↔ _
  have he : (∀ i, (if i ≤ h then !(x i) else x i) = y i) ↔ y = flipPrefix h x := by
    rw [← funext_iff, eq_comm]; rfl
  rw [he]
  apply and_congr_left
  intro _
  constructor
  · intro hv
    refine ⟨fun i hi => ?_, ?_⟩
    · simpa only [hi, ite_true, Finset.mem_singleton] using hv i
    · simpa using hv h
  · rintro ⟨hv, hh⟩ i
    by_cases hi : i < h
    · simp [hi, hv i hi]
    · by_cases he : i = h
      · subst i; simpa using hh
      · simp [hi, he]

theorem carryMap_sound {d : ℕ} (h : Fin d) {x y : Bits d}
    (hxy : (carryMap h).Rel x y) : value y = value x + 1 := by
  obtain ⟨hx, rfl⟩ := (carryMap_rel _ _ _).mp hxy
  rw [← advance_carry h x hx]
  exact value_advance x (carry_not_last hx)

theorem carryMap_complete {d : ℕ} (x y : Bits d) (hxy : value y = value x + 1) :
    ∃ h : Fin d, (carryMap h).Rel x y := by
  have hn : x ≠ fun _ => true := by
    intro he
    have h := value_lt y
    rw [hxy, he, value_one] at h
    omega
  obtain ⟨h, hh⟩ := carry_exists x hn
  refine ⟨h, (carryMap_rel _ _ _).mpr ⟨hh, ?_⟩⟩
  apply value_injective d
  rw [← advance_carry h x hh, value_advance x (carry_not_last hh), hxy]

/-- An additional all-ones case supplies the cyclic seam for positions only. -/
def cycleMap (d : ℕ) : Option (Fin d) → ProductMap d
  | none => ProductMap.singleton (fun _ => true) (fun _ => false)
  | some h => carryMap h

theorem cycleMap_sound {d : ℕ} (h : Option (Fin d)) {x y : Bits d}
    (hxy : (cycleMap d h).Rel x y) : y = advance x := by
  cases h with
  | none =>
    obtain ⟨rfl, rfl⟩ := (ProductMap.singleton_rel _ _ _ _).mp hxy
    exact (advance_one d).symm
  | some h =>
    obtain ⟨hh, rfl⟩ := (carryMap_rel _ _ _).mp hxy
    exact (advance_carry h x hh).symm

theorem cycleMap_complete {d : ℕ} (x : Bits d) :
    ∃ h, (cycleMap d h).Rel x (advance x) := by
  by_cases he : x = fun _ => true
  · exact ⟨none, (ProductMap.singleton_rel _ _ _ _).mpr ⟨he, he ▸ advance_one d⟩⟩
  · obtain ⟨h, hh⟩ := carry_exists x he
    exact ⟨some h, (carryMap_rel _ _ _).mpr ⟨hh, advance_carry h x hh⟩⟩

noncomputable def rotation (d : ℕ) : Bits d ≃ Bits d :=
  (equiv d).trans ((finRotate (2 ^ d)).trans (equiv d).symm)

theorem rotation_advance {d : ℕ} (x : Bits d) : rotation d x = advance x := by
  apply value_injective d
  have h : value (rotation d x) = ((value x + 1) % (2 ^ d)) := by
    change ((equiv d) (rotation d x)).val = _
    simp only [rotation, Equiv.trans_apply, Equiv.apply_symm_apply]
    rw [finRotate_apply]
    simp only [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
    rfl
  exact h.trans (advance_mod x).symm

end BinaryAddress

namespace BinaryAddress

/-- The largest differing bit determines strict numeric order. -/
theorem value_lt_iff {d : ℕ} (x y : Bits d) : value x < value y ↔
    ∃ h : Fin d, x h = false ∧ y h = true ∧ ∀ i, h < i → x i = y i := by
  induction d with
  | zero => simp [value]
  | succ d ih =>
    let xt : Bits d := fun i => x i.succ
    let yt : Bits d := fun i => y i.succ
    constructor
    · intro h
      by_cases ht : value xt < value yt
      · obtain ⟨i, hi, hj, hh⟩ := (ih xt yt).mp ht
        refine ⟨i.succ, hi, hj, ?_⟩
        intro j hji
        cases j using Fin.cases with
        | zero => exact (Fin.not_lt_zero _ hji).elim
        | succ j => exact hh j (by simpa using hji)
      · have he : value xt = value yt := by
          change (if x 0 then 1 else 0) + 2 * value xt < (if y 0 then 1 else 0) + 2 * value yt at h
          split_ifs at h <;> omega
        have hev := value_injective d he
        refine ⟨0, ?_, ?_, ?_⟩
        · change (if x 0 then 1 else 0) + 2 * value xt < (if y 0 then 1 else 0) + 2 * value yt at h
          cases hx0 : x 0 <;> cases hy0 : y 0 <;> simp_all
        · change (if x 0 then 1 else 0) + 2 * value xt < (if y 0 then 1 else 0) + 2 * value yt at h
          cases hx0 : x 0 <;> cases hy0 : y 0 <;> simp_all
        · intro i hi
          cases i using Fin.cases with
          | zero => exact (lt_irrefl _ hi).elim
          | succ i => exact congrFun hev i
    · rintro ⟨h, hx, hy, hhigh⟩
      cases h using Fin.cases with
      | zero =>
        have hev : xt = yt := by
          funext i
          exact hhigh i.succ (by simp)
        change (if x 0 then 1 else 0) + 2 * value xt < (if y 0 then 1 else 0) + 2 * value yt
        rw [hx, hy, hev]
        simp
      | succ h =>
        have ht : value xt < value yt := (ih xt yt).mpr
          ⟨h, hx, hy, fun i hi => hhigh i.succ (by simpa using hi)⟩
        change (if x 0 then 1 else 0) + 2 * value xt < (if y 0 then 1 else 0) + 2 * value yt
        split_ifs <;> omega

/-- A threshold request fixes its high prefix and first strictly-larger bit. -/
def aboveMap {d : ℕ} (x : Bits d) (h : Fin d) : ProductMap d where
  domain i := if h < i then {x i} else if i = h then {true} else Finset.univ
  nonempty i := by split <;> first | exact Finset.singleton_nonempty _ | split <;> simp
  mapping _ b := b
  injective _ _ _ _ _ he := he

@[simp] theorem aboveMap_rel {d : ℕ} (x : Bits d) (h : Fin d) (y z : Bits d) :
    (aboveMap x h).Rel y z ↔ y = z ∧ y h = true ∧ ∀ i, h < i → y i = x i := by
  change ((∀ i, y i ∈ if h < i then {x i} else if i = h then {true} else Finset.univ) ∧
    ∀ i, y i = z i) ↔ _
  rw [← funext_iff]
  constructor
  · rintro ⟨hy, rfl⟩
    exact ⟨rfl, by simpa using hy h, fun i hi => by simpa [hi] using hy i⟩
  · rintro ⟨rfl, hh, hhi⟩
    refine ⟨fun i => ?_, rfl⟩
    by_cases hi : h < i
    · simp [hi, hhi i hi]
    · by_cases he : i = h
      · subst i; simp [hh]
      · simp [hi, he]

abbrev ThresholdCase {d : ℕ} (x : Bits d) := Option {h : Fin d // x h = false}

def thresholdMap {d : ℕ} (x : Bits d) : ThresholdCase x → ProductMap d
  | none => ProductMap.singleton x x
  | some h => aboveMap x h.val

theorem threshold_sound {d : ℕ} (x : Bits d) (h : ThresholdCase x) {y z : Bits d}
    (hy : (thresholdMap x h).Rel y z) : value x ≤ value y ∧ y = z := by
  cases h with
  | none =>
    obtain ⟨rfl, rfl⟩ := (ProductMap.singleton_rel _ _ _ _).mp hy
    exact ⟨le_rfl, rfl⟩
  | some h =>
    obtain ⟨he, hh, hhi⟩ := (aboveMap_rel _ _ _ _).mp hy
    exact ⟨le_of_lt ((value_lt_iff x y).mpr
      ⟨h.val, h.property, hh, fun i hi => (hhi i hi).symm⟩), he⟩

theorem threshold_complete {d : ℕ} (x y : Bits d) (hxy : value x ≤ value y) :
    ∃ h : ThresholdCase x, (thresholdMap x h).Rel y y := by
  rcases lt_or_eq_of_le hxy with hlt | he
  · obtain ⟨h, hx, hy, hhi⟩ := (value_lt_iff x y).mp hlt
    exact ⟨some ⟨h, hx⟩, (aboveMap_rel _ _ _ _).mpr ⟨rfl, hy, fun i hi => (hhi i hi).symm⟩⟩
  · have he' := value_injective d he
    exact ⟨none, (ProductMap.singleton_rel _ _ _ _).mpr ⟨he'.symm, he'.symm⟩⟩

end BinaryAddress

namespace ProductCircuit
variable {r : ℕ} {P E Z T : Type} (C : ProductCircuit r P E Z T)

theorem edge_rel (e : E) {x y : Fin r → Bool} (h : (C.edgeMap e).Rel x y)
    (hx : C.True (C.source e) x) : C.PortTrue (C.target e) y (C.port e) := by
  obtain ⟨a, rfl, rfl⟩ := (ProductMap.rel_iff _ _ _).mp h
  exact PortTrue.edge e a hx

theorem seed_rel (z : Z) {x y : Fin r → Bool} (h : (C.seedMap z).Rel x y) :
    C.True (C.seedType z) x := by
  obtain ⟨a, rfl, rfl⟩ := (ProductMap.rel_iff _ _ _).mp h
  exact fun j => PortTrue.seed z a j

end ProductCircuit

end WLIdentification

end OAI
