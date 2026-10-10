import OAI.Computability.WLIdentification.BufferedCircuits

namespace OAI

namespace WLIdentification

namespace ProductCircuit
variable {r : ℕ} {P E Z T : Type} (C : ProductCircuit r P E Z T)

abbrev Shifts := (e : C.Comparison) → (C.comparisonMap e).Point → Bit

/-- General, address-dependent image consistency, as extracted from arbitrary
WL mates. It is deliberately weaker than simultaneous pointwise solvability. -/
structure Images (delta : C.Shifts) where
  values : (p : C.RealType) → (Fin r → Bool) → Set (Fin (C.realDimension p) → Bit)
  nonempty : ∀ p a, (values p a).Nonempty
  equation : ∀ e (a : (C.comparisonMap e).Point),
    C.comparisonLeft e '' values (C.comparisonSource e) ((C.comparisonMap e).source a) =
      (fun v => delta e a + C.comparisonRight e v) ''
        values (C.comparisonTarget e) ((C.comparisonMap e).target a)

namespace Images
variable {C} {delta : C.Shifts} (I : C.Images delta)
open BufferAlgebra

theorem first_equation (l : C.Connection) (a : (C.connectionMap l).Point) :
    C.sourceForm l '' I.values (.primary (C.connectionSource l)) ((C.connectionMap l).source a) =
      (fun v => delta (.first l) a + v (0 : Fin 2)) '' I.values (.buffer l) ((C.connectionMap l).source a) :=
  I.equation (.first l) a

theorem second_equation (l : C.Connection) (a : (C.connectionMap l).Point) :
    C.sourceForm l '' I.values (.primary (C.connectionSource l)) ((C.connectionMap l).source a) =
      (fun v => delta (.second l) a + v (1 : Fin 2)) '' I.values (.buffer l) ((C.connectionMap l).source a) :=
  I.equation (.second l) a

theorem third_equation (l : C.Connection) (a : (C.connectionMap l).Point) :
    (fun v => v (0 : Fin 2) + v (1 : Fin 2)) '' I.values (.buffer l) ((C.connectionMap l).source a) =
      (fun v => delta (.third l) a + C.targetForm l v) ''
        I.values (.primary (C.connectionTarget l)) ((C.connectionMap l).target a) :=
  I.equation (.third l) a

theorem forward (l : C.Connection) (a : (C.connectionMap l).Point)
    (h : Determined (I.values (.primary (C.connectionSource l)) ((C.connectionMap l).source a))
      (C.sourceForm l)) :
    Determined (I.values (.primary (C.connectionTarget l)) ((C.connectionMap l).target a))
      (C.targetForm l) :=
  BufferAlgebra.forward _ _ _ (I.first_equation l a) (I.second_equation l a) (I.third_equation l a) h

theorem coordinate_eq_sum_of_one {d : ℕ} (hd : d = 1) (v : Fin d → Bit) (j : Fin d) :
    v j = sumForm d v := by
  subst d
  fin_cases j
  simp [sumForm_apply]

theorem seed (z : Z) (a : (C.seedMap z).Point) (j : Fin (C.dimension (C.seedType z))) :
    Determined (I.values (.primary (some (C.seedType z))) ((C.seedMap z).source a))
      (fun v => v j) := by
  have h : Determined (I.values (.primary (some (C.seedType z))) ((C.seedMap z).source a))
      (sumForm (C.dimension (C.seedType z))) :=
    (determined_comp (delta (.seed z) a) (I.equation (.seed z) a)).mpr
      (determined_zero _)
  intro v hv w hw
  dsimp only
  rw [coordinate_eq_sum_of_one (C.seed_scalar z) v j,
    coordinate_eq_sum_of_one (C.seed_scalar z) w j]
  exact h v hv w hw

theorem true_port {p : P} {a : Fin r → Bool} {j : Fin (C.dimension p)}
    (h : C.PortTrue p a j) :
    Determined (I.values (.primary (some p)) a) (fun v => v j) := by
  induction h with
  | seed z a j => exact I.seed z a j
  | edge e a h ih =>
    apply I.forward (.original e) a
    simpa only [sourceForm, BufferAlgebra.Determined, sumForm_apply] using determined_sum ih

theorem true_output {p : P} {a : Fin r → Bool} (h : C.True p a) :
    Determined (I.values (.primary (some p)) a) (sumForm (C.dimension p)) := by
  simpa only [BufferAlgebra.Determined, sumForm_apply] using determined_sum (fun j => I.true_port (h j))

end Images

/-- Coordinate flips connect the entire Boolean address cube, not only the
addresses actually visited by the computation. -/
theorem cube_propagation (Q : (Fin r → Bool) → Prop)
    (hstep : ∀ a i, Q a → Q (fun j => if j = i then !(a j) else a j))
    {a₀ : Fin r → Bool} (h₀ : Q a₀) : ∀ a, Q a := by
  classical
  intro a
  have hp (s : Finset (Fin r)) : Q (fun i => if i ∈ s then a i else a₀ i) := by
    induction s using Finset.induction_on with
    | empty => simpa using h₀
    | @insert i s hi ih =>
      let b : Fin r → Bool := fun j => if j ∈ s then a j else a₀ j
      by_cases he : a i = b i
      · convert ih using 1
        funext j
        by_cases hj : j = i
        · subst j; simpa only [Finset.mem_insert_self, ite_true] using he
        · simp only [Finset.mem_insert, hj, false_or]
      · have hb : a i = !(b i) := by cases ha : a i <;> cases hh : b i <;> simp_all
        convert hstep b i ih using 1
        funext j
        by_cases hj : j = i
        · subst j
          simp only [Finset.mem_insert_self, ite_true]
          exact hb
        · simp only [Finset.mem_insert, hj, false_or, ite_false, b]
  simpa using hp Finset.univ

namespace Images
variable {C} {delta : C.Shifts} (I : C.Images delta)
open BufferAlgebra

include I in
theorem accepted_broadcast (h : C.Accepted) (a : Fin r → Bool) :
    Determined (I.values (.primary none) a) (fun v => v (0 : Fin 1)) := by
  obtain ⟨t, x, ht⟩ := h
  have h₀ : Determined (I.values (.primary none) ((C.testMap t).source x)) (fun v => v (0 : Fin 1)) :=
    I.forward (.test t) x (I.true_output ht)
  apply cube_propagation (fun a => Determined (I.values (.primary none) a) (fun v => v (0 : Fin 1))) _ h₀ a
  intro b i hb
  exact I.forward (.flip i) (ProductMap.ofAddress b) hb

theorem accepted_primary (h : C.Accepted) (p : C.Primary) (a : Fin r → Bool) :
    (I.values (.primary p) a).Subsingleton := by
  apply subsingleton_of_coordinates
  intro j
  cases p with
  | none =>
    have hj : j = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
    subst j
    exact I.accepted_broadcast h a
  | some p =>
    exact I.forward (.broadcast p j) (ProductMap.ofAddress a) (I.accepted_broadcast h a)

noncomputable def primaryValue (p : C.Primary) (a : Fin r → Bool) :
    Fin (C.primaryDimension p) → Bit := (I.nonempty (.primary p) a).choose

theorem primaryValue_mem (p : C.Primary) (a : Fin r → Bool) :
    I.primaryValue p a ∈ I.values (.primary p) a := (I.nonempty (.primary p) a).choose_spec

theorem primary_eq_singleton (h : C.Accepted) (p : C.Primary) (a : Fin r → Bool) :
    I.values (.primary p) a = {I.primaryValue p a} := by
  ext v
  constructor
  · exact fun hv => (I.accepted_primary h p a) hv (I.primaryValue_mem p a)
  · intro hv
    have he : v = I.primaryValue p a := hv
    exact he.symm ▸ I.primaryValue_mem p a

end Images
end ProductCircuit

namespace ProductCircuit.Images
variable {r : ℕ} {P E Z T : Type} {C : ProductCircuit r P E Z T}
    {delta : C.Shifts} (I : C.Images delta)

noncomputable def bufferValue (l : C.Connection) (a : (C.connectionMap l).Point) :
    Fin 2 → Bit := (I.nonempty (.buffer l) ((C.connectionMap l).source a)).choose

theorem bufferValue_mem (l : C.Connection) (a : (C.connectionMap l).Point) :
    I.bufferValue l a ∈ I.values (.buffer l) ((C.connectionMap l).source a) :=
  (I.nonempty (.buffer l) ((C.connectionMap l).source a)).choose_spec

theorem buffer_values (h : C.Accepted) (l : C.Connection) (a : (C.connectionMap l).Point) :
    C.sourceForm l (I.primaryValue (C.connectionSource l) ((C.connectionMap l).source a)) =
      delta (.first l) a + I.bufferValue l a 0 ∧
    C.sourceForm l (I.primaryValue (C.connectionSource l) ((C.connectionMap l).source a)) =
      delta (.second l) a + I.bufferValue l a 1 ∧
    I.bufferValue l a 0 + I.bufferValue l a 1 = delta (.third l) a +
      C.targetForm l (I.primaryValue (C.connectionTarget l) ((C.connectionMap l).target a)) := by
  have hm := I.bufferValue_mem l a
  constructor
  · obtain ⟨v, hv, he⟩ := (I.first_equation l a).symm ▸
      (show delta (.first l) a + I.bufferValue l a 0 ∈
        (fun v : Fin 2 → Bit => delta (.first l) a + v 0) ''
          I.values (.buffer l) ((C.connectionMap l).source a) from ⟨_, hm, rfl⟩)
    rw [(I.accepted_primary h _ _) hv (I.primaryValue_mem _ _)] at he
    exact he
  constructor
  · obtain ⟨v, hv, he⟩ := (I.second_equation l a).symm ▸
      (show delta (.second l) a + I.bufferValue l a 1 ∈
        (fun v : Fin 2 → Bit => delta (.second l) a + v 1) ''
          I.values (.buffer l) ((C.connectionMap l).source a) from ⟨_, hm, rfl⟩)
    rw [(I.accepted_primary h _ _) hv (I.primaryValue_mem _ _)] at he
    exact he
  · obtain ⟨v, hv, he⟩ := (I.third_equation l a) ▸
      (show I.bufferValue l a 0 + I.bufferValue l a 1 ∈
        (fun v : Fin 2 → Bit => v 0 + v 1) ''
          I.values (.buffer l) ((C.connectionMap l).source a) from ⟨_, hm, rfl⟩)
    rw [(I.accepted_primary h _ _) hv (I.primaryValue_mem _ _)] at he
    exact he.symm

theorem primary_rowSum (h : C.Accepted)
    (hd : ∀ e, CycleRows.RowSum (fun i => {x // x ∈ (C.comparisonMap e).domain i}) Bit (delta e))
    (p : C.Primary) :
    CycleRows.RowSum (fun _ : Fin r => Bool) (Fin (C.primaryDimension p) → Bit) (I.primaryValue p) := by
  apply CycleRows.RowSum.pi
  intro j
  have hv (a : Fin r → Bool) : I.primaryValue p a j =
      delta (.first (.self p j)) (ProductMap.ofAddress a) +
      delta (.second (.self p j)) (ProductMap.ofAddress a) +
      delta (.third (.self p j)) (ProductMap.ofAddress a) := by
    obtain ⟨h₁, h₂, h₃⟩ := I.buffer_values h (.self p j) (ProductMap.ofAddress a)
    exact BufferAlgebra.self_value _ _ _ _ _ _ h₁ h₂ h₃
  have ha := (hd (.first (.self p j))).pullback
    (fun _ (x : Bool) => (⟨x, Finset.mem_univ _⟩ : {b : Bool // b ∈ (Finset.univ : Finset Bool)}))
  have hb := (hd (.second (.self p j))).pullback
    (fun _ (x : Bool) => (⟨x, Finset.mem_univ _⟩ : {b : Bool // b ∈ (Finset.univ : Finset Bool)}))
  have hc := (hd (.third (.self p j))).pullback
    (fun _ (x : Bool) => (⟨x, Finset.mem_univ _⟩ : {b : Bool // b ∈ (Finset.univ : Finset Bool)}))
  convert (ha.add hb).add hc using 1
  exact funext hv

theorem solve_shift {x d z : Bit} (h : x = d + z) : z = x + d := by
  rw [h]
  calc z = (d + d) + z := by rw [CharTwo.add_self_eq_zero, zero_add]
    _ = d + z + d := by ac_rfl

theorem buffer_rowSum (h : C.Accepted)
    (hd : ∀ e, CycleRows.RowSum (fun i => {x // x ∈ (C.comparisonMap e).domain i}) Bit (delta e))
    (l : C.Connection) :
    CycleRows.RowSum (fun i => {x // x ∈ (C.connectionMap l).domain i})
      (Fin 2 → Bit) (I.bufferValue l) := by
  apply CycleRows.RowSum.pi
  have hs := ((I.primary_rowSum h hd (C.connectionSource l)).pullback
    (fun i (x : {x // x ∈ (C.connectionMap l).domain i}) => x.val)).map (C.sourceForm l).toAddMonoidHom
  intro j
  fin_cases j
  · change CycleRows.RowSum _ Bit (fun a => I.bufferValue l a 0)
    have he : (fun a => I.bufferValue l a 0) =
        (fun a => C.sourceForm l
          (I.primaryValue (C.connectionSource l) ((C.connectionMap l).source a)) + delta (.first l) a) := by
      funext a
      exact solve_shift (I.buffer_values h l a).1
    rw [he]
    exact hs.add (hd (.first l))
  · change CycleRows.RowSum _ Bit (fun a => I.bufferValue l a 1)
    have he : (fun a => I.bufferValue l a 1) =
        (fun a => C.sourceForm l
          (I.primaryValue (C.connectionSource l) ((C.connectionMap l).source a)) + delta (.second l) a) := by
      funext a
      exact solve_shift (I.buffer_values h l a).2.1
    rw [he]
    exact hs.add (hd (.second l))

theorem buffer_extension (h : C.Accepted)
    (hd : ∀ e, CycleRows.RowSum (fun i => {x // x ∈ (C.comparisonMap e).domain i}) Bit (delta e))
    (l : C.Connection) :
    ∃ f : (Fin r → Bool) → Fin 2 → Bit,
      CycleRows.RowSum (fun _ : Fin r => Bool) (Fin 2 → Bit) f ∧
      ∀ a : (C.connectionMap l).Point, f ((C.connectionMap l).source a) = I.bufferValue l a :=
  (I.buffer_rowSum h hd l).extend (fun _ x => x.val) (fun _ => Subtype.val_injective)

include I in
/-- Acceptance supplies genuine row-sum functions at ALL real types, not merely
pointwise scalar images. No property outside a buffer's active domain is used. -/
theorem rows_of_accepted (h : C.Accepted)
    (hd : ∀ e, CycleRows.RowSum (fun i => {x // x ∈ (C.comparisonMap e).domain i}) Bit (delta e)) :
    ∃ f : (p : C.RealType) → (Fin r → Bool) → Fin (C.realDimension p) → Bit,
      (∀ p, CycleRows.RowSum (fun _ : Fin r => Bool) (Fin (C.realDimension p) → Bit) (f p)) ∧
      ∀ e (a : (C.comparisonMap e).Point),
        C.comparisonLeft e (f (C.comparisonSource e) ((C.comparisonMap e).source a)) +
        C.comparisonRight e (f (C.comparisonTarget e) ((C.comparisonMap e).target a)) = delta e a := by
  choose B hB hBa using I.buffer_extension h hd
  let f (p : C.RealType) : (Fin r → Bool) → Fin (C.realDimension p) → Bit := match p with
    | .primary p => I.primaryValue p
    | .buffer l => B l
    | .dummy => fun _ _ => 0
  refine ⟨f, ?_, ?_⟩
  · intro p
    cases p with
    | primary p => exact I.primary_rowSum h hd p
    | buffer l => exact hB l
    | dummy => exact CycleRows.RowSum.zero
  · intro e a
    cases e with
    | seed z =>
      obtain ⟨v, _, he⟩ := (I.equation (.seed z) a) ▸
        (show C.comparisonLeft (.seed z) (I.primaryValue (some (C.seedType z)) ((C.seedMap z).source a)) ∈
          C.comparisonLeft (.seed z) '' I.values (.primary (some (C.seedType z))) ((C.seedMap z).source a)
          from ⟨_, I.primaryValue_mem _ _, rfl⟩)
      change sumForm (C.dimension (C.seedType z))
        (I.primaryValue (some (C.seedType z)) ((C.seedMap z).source a)) + 0 = _
      simpa only [comparisonRight, LinearMap.zero_apply, add_zero] using he.symm
    | first l =>
      have he := I.buffer_values h l a |>.1
      change C.sourceForm l (I.primaryValue _ ((C.connectionMap l).source a)) +
        B l ((C.connectionMap l).source a) 0 = _
      rw [hBa l a, he, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    | second l =>
      have he := I.buffer_values h l a |>.2.1
      change C.sourceForm l (I.primaryValue _ ((C.connectionMap l).source a)) +
        B l ((C.connectionMap l).source a) 1 = _
      rw [hBa l a, he, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    | third l =>
      have he := I.buffer_values h l a |>.2.2
      change (B l _ 0 + B l _ 1) + C.targetForm l (I.primaryValue _ _) = _
      rw [hBa l a, he, add_assoc, CharTwo.add_self_eq_zero, add_zero]

end ProductCircuit.Images

namespace ProductCircuit
variable {r : ℕ} {P E Z T : Type} [Fintype P] [Fintype E] [Fintype Z] [Fintype T]
    (C : ProductCircuit r P E Z T)

abbrev wireDelta (n : ℕ) (beta : (C.schemas.layout n).Block → Bit) : C.Shifts :=
  fun e a => C.schemas.wireShift n beta e a

noncomputable def imagesOfEquivalent (hr : 32 ≤ r) (n : ℕ)
    (beta : (C.schemas.layout n).Block → Bit)
    (he : Equivalent r (((C.schemas.layout n).affine (by omega)).graph 0)
      (((C.schemas.layout n).affine (by omega)).graph beta)) : C.Images (C.wireDelta n beta) where
  values p a := C.schemas.responseImages (by omega) n beta p (ProductMap.ofAddress a)
  nonempty p a := (C.schemas.image_consistency hr n beta he).1 p (ProductMap.ofAddress a)
  equation e a := (C.schemas.image_consistency hr n beta he).2 e a

/-- Acceptance gives identification against every finite
simple uncolored mate; no special-twist condition is imposed on its shifts. -/
theorem identifies_of_accepted (hr : 32 ≤ r) (n : ℕ) (h : C.Accepted) :
    Identifies r (((C.schemas.layout n).affine (by omega)).graph 0) := by
  intro H he
  obtain ⟨beta, hb⟩ := (C.schemas.layout n).arbitrary_mate hr H he
  have he' := equivalent_trans he (isomorphic_equivalent hb r)
  let I := C.imagesOfEquivalent hr n beta he'
  obtain ⟨f, hf, hfe⟩ := I.rows_of_accepted h (fun e => C.schemas.wireShift_rowSum n beta e)
  have hs : ∃ z, ((C.schemas.layout n).affine (by omega)).Solves beta z := by
    apply (C.schemas.offsets_iff_real_rowSums (by omega) n beta).mpr
    refine ⟨fun p a => f p (fun i => (a i).val), ?_, ?_⟩
    · intro p
      exact (hf p).pullback (fun _ (b : {b : Bool // b ∈ (Finset.univ : Finset Bool)}) => b.val)
    · intro e a
      exact hfe e a
  exact isomorphic_trans (((C.schemas.layout n).affine (by omega)).graph_isomorphic_iff beta |>.mpr hs)
    (isomorphic_symm hb)

end ProductCircuit

end WLIdentification

end OAI
