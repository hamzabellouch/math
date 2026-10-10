import OAI.MeasureTheory.DyadicAvoidance.GridSeparation

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem310.FiniteTableModel

/-- Child `M` is default and the other `M` children have selectors. -/
abbrev Child (M : ℕ) := Fin (M + 1)

/-- Nodes at which a depth-`d` router still makes a decision. -/
abbrev Node (M d : ℕ) := {P : List (Child M) // P.length < d}

/-- A terminal path. This is definitionally a list with the required length. -/
abbrev Leaf (M d : ℕ) := List.Vector (Child M) d

instance nodeFintype (M d : ℕ) : Fintype (Node M d) := by
  classical
  let f : (Σ k : Fin d, List.Vector (Child M) k.val) → Node M d :=
    fun p => ⟨p.2.val, by simpa only [p.2.property] using p.1.isLt⟩
  apply Fintype.ofSurjective f
  intro P
  exact ⟨⟨⟨P.val.length, P.property⟩, ⟨P.val, rfl⟩⟩, rfl⟩

instance nodeMeasurableSpace (M d : ℕ) : MeasurableSpace (Node M d) := ⊤
instance nodeDiscreteMeasurableSpace (M d : ℕ) : DiscreteMeasurableSpace (Node M d) := by constructor; intro s; trivial
instance leafMeasurableSpace (M d : ℕ) : MeasurableSpace (Leaf M d) := ⊤
instance leafDiscreteMeasurableSpace (M d : ℕ) : DiscreteMeasurableSpace (Leaf M d) := by constructor; intro s; trivial

/-- Finite selector-table addresses include the table name as well as its key. -/
abbrev SelectorAddress {M d : ℕ} (b : Node M d → Fin M → ℕ) :=
  Σ e : Node M d × Fin M, Fin (2 ^ (b e.1 e.2 + 2))

/-- Terminal addresses include the leaf name, preventing collisions between tables. -/
abbrev TerminalAddress {M d : ℕ} (b : Leaf M d → ℕ) :=
  Σ L : Leaf M d, Fin (2 ^ (b L + 2))

instance selectorAddressMeasurableSpace {M d : ℕ} (b : Node M d → Fin M → ℕ) :
    MeasurableSpace (SelectorAddress b) := ⊤
instance selectorAddressDiscreteMeasurableSpace {M d : ℕ} (b : Node M d → Fin M → ℕ) :
    DiscreteMeasurableSpace (SelectorAddress b) := by constructor; intro s; trivial
instance terminalAddressMeasurableSpace {M d : ℕ} (b : Leaf M d → ℕ) :
    MeasurableSpace (TerminalAddress b) := ⊤
instance terminalAddressDiscreteMeasurableSpace {M d : ℕ} (b : Leaf M d → ℕ) :
    DiscreteMeasurableSpace (TerminalAddress b) := by constructor; intro s; trivial

abbrev SelectorTable {M d : ℕ} (b : Node M d → Fin M → ℕ) := SelectorAddress b → Bool
abbrev TerminalTable {M d : ℕ} (b : Leaf M d → ℕ) := TerminalAddress b → Bool

/-- The center exposure consults exactly one deterministic coordinate per selector table. -/
def selectorAddress {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (P : Node M d) (i : Fin M) (x : ℝ) : SelectorAddress b :=
  ⟨(P, i), GridSeparation.dyadicKey (b P i) x⟩

/-- The terminal coordinate read along the selected leaf. -/
def terminalAddress {M d : ℕ} (b : Leaf M d → ℕ)
    (L : Leaf M d) (x : ℝ) : TerminalAddress b :=
  ⟨L, GridSeparation.dyadicKey (b L) x⟩

/-- Selector values are extended to all lists; routing uses only valid nodes. -/
def selectorValue {M d : ℕ} (b : Node M d → Fin M → ℕ) (ω : SelectorTable b)
    (P : List (Child M)) (i : Fin M) (x : ℝ) : Bool :=
  if h : P.length < d then ω (selectorAddress b ⟨P, h⟩ i x) else false

@[simp] theorem selectorValue_valid {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) (P : Node M d) (i : Fin M) (x : ℝ) :
    selectorValue b ω P.val i x = ω (selectorAddress b P i x) := by
  simp [selectorValue, P.property]

lemma measurable_dyadicKey (b : ℕ) : Measurable (GridSeparation.dyadicKey b) := by
  apply measurable_to_countable
  intro y
  have hm : Measurable (GridSeparation.periodicKey ((2 : ℝ) ^ (b + 2))) := by
    exact (measurable_const.mul measurable_fract).floor
  convert (measurableSet_singleton (GridSeparation.periodicKey ((2 : ℝ) ^ (b + 2)) y)).preimage hm using 1
  ext x
  exact GridSeparation.dyadicKey_eq_iff b x y

lemma dyadicKey_add_one (b : ℕ) (x : ℝ) :
    GridSeparation.dyadicKey b (x + 1) = GridSeparation.dyadicKey b x := by
  apply (GridSeparation.dyadicKey_eq_iff _ _ _).mpr
  exact GridSeparation.periodicKey_add_one _ _

lemma measurable_selectorAddress {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (P : Node M d) (i : Fin M) : Measurable (selectorAddress b P i) := by
  exact (measurable_of_finite (fun k => (⟨(P, i), k⟩ : SelectorAddress b))).comp
    (measurable_dyadicKey (b P i))

lemma measurable_terminalAddress {M d : ℕ} (b : Leaf M d → ℕ)
    (L : Leaf M d) : Measurable (terminalAddress b L) := by
  exact (measurable_of_finite (fun k => (⟨L, k⟩ : TerminalAddress b))).comp
    (measurable_dyadicKey (b L))

lemma measurable_selectorValue {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) (P : List (Child M)) (i : Fin M) :
    Measurable (selectorValue b ω P i) := by
  change Measurable (fun x : ℝ => if h : P.length < d then
    ω (selectorAddress b ⟨P, h⟩ i x) else false)
  by_cases h : P.length < d
  · simp only [dite_eq_left h]
    exact (measurable_of_finite ω).comp (measurable_selectorAddress b ⟨P, h⟩ i)
  · simpa only [dite_eq_right h] using (measurable_const : Measurable (fun _ : ℝ => false))

@[simp] lemma selectorAddress_add_one {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (P : Node M d) (i : Fin M) (x : ℝ) :
    selectorAddress b P i (x + 1) = selectorAddress b P i x := by
  simp [selectorAddress, dyadicKey_add_one]

@[simp] lemma terminalAddress_add_one {M d : ℕ} (b : Leaf M d → ℕ)
    (L : Leaf M d) (x : ℝ) :
    terminalAddress b L (x + 1) = terminalAddress b L x := by
  simp [terminalAddress, dyadicKey_add_one]

@[simp] lemma selectorValue_add_one {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) (P : List (Child M)) (i : Fin M) (x : ℝ) :
    selectorValue b ω P i (x + 1) = selectorValue b ω P i x := by
  by_cases h : P.length < d <;> simp [selectorValue, h]

/-- Exposing the center reads distinct coordinates because table names are retained. -/
lemma center_selectorAddress_injective {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (x : ℝ) : Function.Injective (fun e : Node M d × Fin M => selectorAddress b e.1 e.2 x) := by
  intro e f h
  exact congrArg Sigma.fst h

lemma selectorAddress_ne_center {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (P : Node M d) (i : Fin M) {x t : ℝ} {n : ℕ}
    (hn : 3 ≤ n) (hnb : n ≤ b P i) (ht : t ∈ Set.Icc (1 : ℝ) 2) :
    selectorAddress b P i x ≠ selectorAddress b P i (x + t * ((2 : ℝ)⁻¹) ^ n) := by
  intro h
  have hk := (Sigma.mk.inj h).2
  exact GridSeparation.dyadicKey_ne_center hn hnb ht.1 ht.2 (eq_of_heq hk)

lemma dyadicKey_eq_of_refine {b B : ℕ} (hb : b ≤ B) {x y : ℝ}
    (hkey : GridSeparation.dyadicKey B x = GridSeparation.dyadicKey B y) :
    GridSeparation.dyadicKey b x = GridSeparation.dyadicKey b y := by
  apply (GridSeparation.dyadicKey_eq_iff b x y).mpr
  exact GridSeparation.periodicKey_dyadic_eq_of_refine hb
    ((GridSeparation.dyadicKey_eq_iff B x y).mp hkey)

/-- Any selector lookup at a coarser resolution is determined by a finest key. -/
lemma selectorValue_eq_of_key_eq {M d : ℕ} (b : Node M d → Fin M → ℕ)
    (ω : SelectorTable b) (P : List (Child M)) (i : Fin M) (B : ℕ)
    (hlevel : ∀ h : P.length < d, b ⟨P, h⟩ i ≤ B) {x y : ℝ}
    (hkey : GridSeparation.dyadicKey B x = GridSeparation.dyadicKey B y) :
    selectorValue b ω P i x = selectorValue b ω P i y := by
  by_cases h : P.length < d
  · simp only [selectorValue, dite_eq_left h]
    apply congrArg ω
    unfold selectorAddress
    congr 1
    exact dyadicKey_eq_of_refine (hlevel h) hkey
  · simp only [selectorValue, dite_eq_right h]

/-- At a fixed leaf, the finer key also determines the terminal table lookup. -/
lemma terminal_lookup_eq_of_key_eq {M d : ℕ} (b : Leaf M d → ℕ)
    (ω : TerminalTable b) (L : Leaf M d) (B : ℕ) (hlevel : b L ≤ B) {x y : ℝ}
    (hkey : GridSeparation.dyadicKey B x = GridSeparation.dyadicKey B y) :
    ω (terminalAddress b L x) = ω (terminalAddress b L y) := by
  apply congrArg ω
  unfold terminalAddress
  congr 1
  exact dyadicKey_eq_of_refine hlevel hkey

end Problem310.FiniteTableModel

end

end OAI
