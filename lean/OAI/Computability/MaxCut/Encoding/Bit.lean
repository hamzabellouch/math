import Mathlib
import OAI.Computability.MaxCut.Games.Identities

namespace OAI

namespace OptimalMaxCut.TreeCode

open scoped BigOperators

abbrev Bit := ZMod 2
abbrev Branch (s : ℕ) := Fin s × Bool
abbrev Table (s : ℕ) := (Fin s → Bit) → Bit

@[reducible] def Nodes (s : ℕ) : ℕ → Type
  | 0 => Empty
  | m + 1 => Unit ⊕ (Branch s × Nodes s m)

@[reducible] def Leaves (s : ℕ) : ℕ → Type
  | 0 => Unit
  | m + 1 => Branch s × Leaves s m

instance nodesFintype (s m : ℕ) : Fintype (Nodes s m) := by
  induction m with
  | zero => exact inferInstanceAs (Fintype Empty)
  | succ m ih => exact inferInstanceAs (Fintype (Unit ⊕ (Branch s × Nodes s m)))

instance leavesFintype (s m : ℕ) : Fintype (Leaves s m) := by
  induction m with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ m ih => exact inferInstanceAs (Fintype (Branch s × Leaves s m))

instance nodesDecidableEq (s m : ℕ) : DecidableEq (Nodes s m) := by
  induction m with
  | zero => exact inferInstanceAs (DecidableEq Empty)
  | succ m ih => exact inferInstanceAs (DecidableEq (Unit ⊕ (Branch s × Nodes s m)))

instance leavesDecidableEq (s m : ℕ) : DecidableEq (Leaves s m) := by
  induction m with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ m ih => exact inferInstanceAs (DecidableEq (Branch s × Leaves s m))

@[simp] theorem card_leaves (s m : ℕ) : Fintype.card (Leaves s m) = (2 * s) ^ m := by
  induction m with
  | zero =>
      change Fintype.card Unit = 1
      exact Fintype.card_unique
  | succ m ih =>
      change Fintype.card (Branch s × Leaves s m) = _
      rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin,
        Fintype.card_bool, ih, pow_succ]
      ring

def gate {s : ℕ} (F : Table s) (Z : Branch s → Bit) : Bit :=
  (∑ g, Z (g, false)) + F (fun g => Z (g, false) + Z (g, true))

/-- The same complete 2s-ary tree code, with leaves canonically indexed by
branch words instead of choosing an arbitrary bijection with Fin k. -/
def word {s : ℕ} : {m : ℕ} → (Nodes s m → Table s) → (Leaves s m → Bit) → Bit
  | 0, _, x => x ()
  | _m + 1, F, x => gate (F (.inl ())) (fun gb =>
      word (fun v => F (.inr (gb, v))) (fun i => x (gb, i)))

inductive Slice (s : ℕ) : ℕ → Type
  | root : Slice s 0
  | next {j : ℕ} (pair : Fin s) (child : Bool → Slice s j) : Slice s (j + 1)

/-- Membership in the slice, for a tree of any total depth. -/
def onSlice {s : ℕ} : {j m : ℕ} → Slice s j → Nodes s m → Bool
  | _, 0, _, v => nomatch v
  | 0, _ + 1, .root, .inl _ => true
  | 0, _ + 1, .root, .inr _ => false
  | _ + 1, _ + 1, .next _ _, .inl _ => false
  | _ + 1, _ + 1, .next g child, .inr ((g', b), v) =>
      if g' = g then onSlice (child b) v else false

/-- Negate exactly the whole tables on the fixed slice, and no other table. -/
def flipTables {s j m : ℕ} (S : Slice s j) (F : Nodes s m → Table s) :
    Nodes s m → Table s := fun v z => F v z + if onSlice S v then 1 else 0

@[simp] theorem bit_add_self (a : Bit) : a + a = 0 := by
  have := ZMod.natCast_self 2
  linear_combination a * this

@[simp] theorem bit_one_add_one : (1 + 1 : Bit) = 0 := by decide

/-- Simultaneously multiplying the two children in pair g by -1 leaves all
inputs to the gate table fixed and multiplies its prefactor by -1. -/
theorem gate_pair_flip {s : ℕ} (F : Table s) (Z : Branch s → Bit) (g : Fin s) :
    gate F (fun gb => Z gb + if gb.1 = g then 1 else 0) = gate F Z + 1 := by
  have inputs : (fun h : Fin s =>
        (Z (h, false) + if h = g then 1 else 0) +
        (Z (h, true) + if h = g then 1 else 0)) =
      (fun h => Z (h, false) + Z (h, true)) := by
    funext h
    by_cases hh : h = g
    · simp only [hh, ↓reduceIte]
      calc
        (Z (g, false) + 1) + (Z (g, true) + 1) =
            (Z (g, false) + Z (g, true)) + (1 + 1) := by ring
        _ = _ := by rw [bit_one_add_one, add_zero]
    · simp [hh]
  unfold gate
  simp only at inputs ⊢
  rw [inputs, Finset.sum_add_distrib]
  simp
  ring

theorem word_flipTables {s j m : ℕ} (S : Slice s j) (hjm : j < m)
    (F : Nodes s m → Table s) (x : Leaves s m → Bit) :
    word (flipTables S F) x = word F x + 1 := by
  induction S generalizing m with
  | root =>
      cases m with
      | zero => omega
      | succ m =>
          have hc (gb : Branch s) :
              (fun v => flipTables .root F (.inr (gb, v))) =
              (fun v => F (.inr (gb, v))) := by
            funext v z
            simp [flipTables, onSlice]
          change gate (fun z => F (.inl ()) z + 1) _ = gate (F (.inl ())) _ + 1
          simp_rw [hc]
          unfold gate
          ring
  | @next j g child ih =>
      cases m with
      | zero => omega
      | succ m =>
          have hm : j < m := by omega
          have each (gb : Branch s) :
              word (fun v => flipTables (.next g child) F (.inr (gb, v)))
                  (fun i => x (gb, i)) =
              word (fun v => F (.inr (gb, v))) (fun i => x (gb, i)) +
                if gb.1 = g then 1 else 0 := by
            rcases gb with ⟨g', b⟩
            by_cases hg : g' = g
            · subst g'
              have hc :
                  (fun v => flipTables (.next g child) F (.inr ((g, b), v))) =
                  flipTables (child b) (fun v => F (.inr ((g, b), v))) := by
                funext v z
                simp [flipTables, onSlice]
              rw [hc]
              simpa using ih b hm (fun v => F (.inr ((g, b), v))) (fun i => x ((g, b), i))
            · have hc :
                  (fun v => flipTables (.next g child) F (.inr ((g', b), v))) =
                  (fun v => F (.inr ((g', b), v))) := by
                funext v z
                simp [flipTables, onSlice, hg]
              simp [hc, hg]
          change gate (fun z => F (.inl ()) z + 0) _ = gate (F (.inl ())) _ + 1
          simp only [add_zero]
          simp_rw [each]
          exact gate_pair_flip _ _ g

theorem bit_cases (x : Bit) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

def sign (x : Bit) : ℝ := if x = 0 then 1 else -1

@[simp] theorem sign_zero : sign 0 = 1 := by norm_num [sign]
@[simp] theorem sign_one : sign 1 = -1 := by norm_num [sign]

 theorem sign_add (a b : Bit) : sign (a + b) = sign a * sign b := by
  rcases bit_cases a with rfl | rfl <;> rcases bit_cases b with rfl | rfl <;>
    simp []

@[simp] theorem sign_sq (a : Bit) : sign a ^ 2 = 1 := by
  fin_cases a <;> norm_num [sign]

 theorem sign_add_one (a : Bit) : sign (a + 1) = - sign a := by
  rw [sign_add, sign_one]
  ring

 theorem sign_sum {I : Type*} (S : Finset I) (f : I → Bit) :
    sign (∑ i ∈ S, f i) = ∏ i ∈ S, sign (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih => simp [ha, sign_add, ih]

/-- The implemented gate is EXACTLY equation (gate-rule), not a replacement
operator with only the same symmetry. -/
 theorem gate_sign {s : ℕ} (F : Table s) (Z : Branch s → Bit) :
    sign (gate F Z) =
      (∏ g, sign (Z (g, false))) * sign (F (fun g => Z (g, false) + Z (g, true))) := by
  rw [gate, sign_add]
  congr 1
  simpa using sign_sum Finset.univ (fun g => Z (g, false))

def labelWord {A : Type*} {s m : ℕ} (F : Nodes s m → Table s)
    (R : Leaves s m → A → Bit) : A → Bit := fun a => word F (fun i => R i a)

 theorem labelWord_flipTables {A : Type*} {s j m : ℕ} (S : Slice s j)
    (hjm : j < m) (F : Nodes s m → Table s) (R : Leaves s m → A → Bit) :
    labelWord (flipTables S F) R = fun a => labelWord F R a + 1 := by
  funext a
  exact word_flipTables S hjm F _

def Odd {A : Type*} (φ : (A → Bit) → ℝ) : Prop :=
  ∀ w, φ (fun a => w a + 1) = -φ w

 theorem code_flipTables {A : Type*} {s j m : ℕ} (S : Slice s j)
    (hjm : j < m) (F : Nodes s m → Table s) (R : Leaves s m → A → Bit)
    (φ : (A → Bit) → ℝ) (hφ : Odd φ) :
    φ (labelWord (flipTables S F) R) = -φ (labelWord F R) := by
  rw [labelWord_flipTables S hjm]
  exact hφ _

abbrev SliceNode {s j m : ℕ} (S : Slice s j) :=
  {v : Nodes s m // onSlice S v = true}

abbrev SliceTables {s j m : ℕ} (S : Slice s j) := SliceNode (m := m) S → Table s

/-- Fill the slice with independently supplied complete Boolean tables,
leaving all outside tables at their fixed values. -/
def fillTables {s j m : ℕ} (S : Slice s j) (outside : Nodes s m → Table s)
    (inside : SliceTables (m := m) S) : Nodes s m → Table s :=
  fun v => if hv : onSlice S v = true then inside ⟨v, hv⟩ else outside v

/-- The measure-preserving simultaneous negation of all slice-entry signs. -/
def insideFlip {s j m : ℕ} (S : Slice s j) :
    SliceTables (m := m) S ≃ SliceTables (m := m) S where
  toFun F v z := F v z + 1
  invFun F v z := F v z + 1
  left_inv F := by funext v z; dsimp; rw [add_assoc, bit_one_add_one, add_zero]
  right_inv F := by funext v z; dsimp; rw [add_assoc, bit_one_add_one, add_zero]

 theorem fillTables_insideFlip {s j m : ℕ} (S : Slice s j)
    (outside : Nodes s m → Table s) (inside : SliceTables (m := m) S) :
    fillTables S outside (insideFlip S inside) = flipTables S (fillTables S outside inside) := by
  funext v z
  by_cases hv : onSlice S v = true
  · simp [fillTables, insideFlip, flipTables, hv]
  · simp [fillTables, flipTables, hv]

/-- The precise conditional balancing assertion used in extraction Step 1.
Rows, all outside tables, and the fixed slice are arbitrary and NOT averaged.
Only independent uniform slice bits are averaged. -/
 theorem conditional_code_mean_zero {A : Type*} {s j m : ℕ} (S : Slice s j)
    (hjm : j < m) (outside : Nodes s m → Table s) (R : Leaves s m → A → Bit)
    (φ : (A → Bit) → ℝ) (hφ : Odd φ) :
    (𝔼 inside : SliceTables (m := m) S, φ (labelWord (fillTables S outside inside) R)) = 0 := by
  classical
  let f : SliceTables (m := m) S → ℝ :=
    fun inside => φ (labelWord (fillTables S outside inside) R)
  have hx (inside : SliceTables (m := m) S) : f (insideFlip S inside) = - f inside := by
    dsimp [f]
    rw [fillTables_insideFlip]
    exact code_flipTables S hjm _ R φ hφ
  have he := Fintype.expect_equiv (insideFlip (m := m) S)
    (fun x => f (insideFlip S x)) f (fun _ => rfl)
  simp_rw [hx] at he
  rw [Finset.expect_neg_distrib] at he
  change (𝔼 inside, f inside) = 0
  linarith

section RowSmoothing

variable {H I : Type*} [Fintype H] [DecidableEq H] [Nonempty H]
  [Fintype I] [DecidableEq I]

/-- Exactly retain the old whole row with probability r, otherwise draw an
independent uniform whole row. This is not independent noise on its bits. -/
noncomputable def rowKernel (r : ℝ) (x y : H) : ℝ :=
  (if x = y then r else 0) + (1 - r) / Fintype.card H

 theorem rowKernel_nonneg (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (x y : H) :
    0 ≤ rowKernel r x y := by
  unfold rowKernel
  apply add_nonneg
  · split_ifs <;> positivity
  · positivity

 theorem rowKernel_sum (r : ℝ) (x : H) : ∑ y, rowKernel r x y = 1 := by
  have hc : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [rowKernel, Finset.sum_add_distrib]
  simp
  field_simp
  ring

omit [Nonempty H] in
 theorem rowKernel_symm (r : ℝ) (x y : H) : rowKernel r x y = rowKernel r y x := by
  simp [rowKernel, eq_comm]

noncomputable def rowsKernel (r : ℝ) (x y : I → H) : ℝ :=
  ∏ i, rowKernel r (x i) (y i)

omit [DecidableEq I] in
 theorem rowsKernel_nonneg (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (x y : I → H) :
    0 ≤ rowsKernel r x y := by
  exact Finset.prod_nonneg (fun i _ => rowKernel_nonneg r hr hr1 (x i) (y i))

 theorem rowsKernel_sum (r : ℝ) (x : I → H) : ∑ y, rowsKernel r x y = 1 := by
  unfold rowsKernel
  rw [← Fintype.prod_sum]
  simp [rowKernel_sum]

noncomputable def rowSmoothing (r : ℝ) (f : (I → H) → ℝ) (R : I → H) : ℝ :=
  ∑ R', rowsKernel r R R' * f R'

 theorem rowSmoothing_range (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (f : (I → H) → ℝ) (hf : ∀ R, -1 ≤ f R ∧ f R ≤ 1) (R : I → H) :
    -1 ≤ rowSmoothing r f R ∧ rowSmoothing r f R ≤ 1 := by
  have hk := rowsKernel_nonneg (H := H) (I := I) r hr hr1
  have hs := rowsKernel_sum (I := I) r R
  constructor
  · calc
      -1 = ∑ R', rowsKernel r R R' * (-1) := by simp [hs]
      _ ≤ rowSmoothing r f R := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (hf i).1 (hk R i))
  · calc
      rowSmoothing r f R ≤ ∑ R', rowsKernel r R R' * 1 :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hf i).2 (hk R i))
      _ = 1 := by simpa using hs

end RowSmoothing

/-- Exact conditional balancing survives whole-row resampling, with fixed
rows/outside tables/slice. No probabilistic averaging of those contexts is used. -/
 theorem conditional_smoothed_code_mean_zero {A H : Type*} [Fintype H]
    [DecidableEq H] [Nonempty H] {s j m : ℕ} (S : Slice s j) (hjm : j < m)
    (outside : Nodes s m → Table s) (evalRow : H → A → Bit) (r : ℝ)
    (R : Leaves s m → H) (φ : (A → Bit) → ℝ) (hφ : Odd φ) :
    (𝔼 inside : SliceTables (m := m) S,
      rowSmoothing r (fun R' => φ (labelWord (fillTables S outside inside)
        (fun i => evalRow (R' i)))) R) = 0 := by
  classical
  unfold rowSmoothing
  rw [Finset.expect_sum_comm]
  simp_rw [← Finset.mul_expect]
  simp [conditional_code_mean_zero S hjm outside _ φ hφ]

section BitWalsh

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Probability-normalized finite Walsh transform, expressed in the same
sign-bit coordinates as the tree. -/
def character (q x : I → Bit) : ℝ := ∏ i, sign (q i * x i)

 theorem bit_character_orthogonality (q q' : Bit) :
    (∑ x : Bit, sign (q * x) * sign (q' * x)) = if q = q' then 2 else 0 := by
  rcases bit_cases q with rfl | rfl <;>
    rcases bit_cases q' with rfl | rfl <;>
    norm_num [show (Finset.univ : Finset Bit) = {0, 1} by
      ext x; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff];
      exact bit_cases x, sign]

omit [DecidableEq I] in
 theorem character_symm (q x : I → Bit) : character q x = character x q := by
  simp only [character, mul_comm]

 theorem character_sum_orthogonality (q q' : I → Bit) :
    (∑ x, character q x * character q' x) =
      if q = q' then (Fintype.card (I → Bit) : ℝ) else 0 := by
  classical
  simp only [character, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : I) (b : Bit) => sign (q i * b) * sign (q' i * b))]
  simp only [bit_character_orthogonality]
  by_cases h : q = q'
  · subst q'
    simp [ZMod.card]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact ite_eq_right hi

noncomputable def bitCoefficient (f : (I → Bit) → ℝ) (q : I → Bit) : ℝ :=
  𝔼 x, f x * character q x

 theorem bitWalsh_inversion (f : (I → Bit) → ℝ) (x : I → Bit) :
    (∑ q, bitCoefficient f q * character q x) = f x := by
  classical
  unfold bitCoefficient
  simp_rw [Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  have h (y : I → Bit) :
      (∑ q, (f y * character q y) * character q x) =
        f y * (if y = x then (Fintype.card (I → Bit) : ℝ) else 0) := by
    simp only [mul_assoc, ← Finset.mul_sum]
    congr 1
    simp_rw [character_symm (x := y), character_symm (x := x)]
    exact character_sum_orthogonality y x
  simp_rw [h]
  rw [Fintype.expect_eq_sum_div_card]
  simp

end BitWalsh

 theorem gate_expansion {s : ℕ} (F : Table s) (Z : Branch s → Bit) :
    sign (gate F Z) = ∑ q : Fin s → Bit,
      bitCoefficient (fun z => sign (F z)) q *
        ∏ g, sign (Z (g, if q g = 0 then false else true)) := by
  classical
  rw [gate_sign, ← bitWalsh_inversion (fun z => sign (F z))
    (fun g => Z (g, false) + Z (g, true)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [mul_left_comm]
  congr 1
  simp only [character, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro g _
  rcases bit_cases (q g) with hq | hq
  · simp [hq]
  · simp only [hq, one_mul, one_ne_zero, ↓reduceIte, sign_add]
    rw [← mul_assoc, ← pow_two, sign_sq, one_mul]

section TensorSmoothing
variable {I J H : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H] [Nonempty H]

 theorem rowSmoothing_one (r : ℝ) (R : I → H) :
    rowSmoothing r (fun _ : I → H => (1 : ℝ)) R = 1 := by
  simp only [rowSmoothing, mul_one]
  exact rowsKernel_sum r R

omit [Nonempty H] in
 theorem rowSmoothing_sum {K : Type*} [Fintype K]
    (r : ℝ) (f : K → (I → H) → ℝ) (R : I → H) :
    rowSmoothing r (fun x => ∑ k, f k x) R = ∑ k, rowSmoothing r (f k) R := by
  simp only [rowSmoothing, Finset.mul_sum]
  rw [Finset.sum_comm]

omit [Nonempty H] in
 theorem rowSmoothing_smul (r a : ℝ) (f : (I → H) → ℝ) (R : I → H) :
    rowSmoothing r (fun x => a * f x) R = a * rowSmoothing r f R := by
  simp only [rowSmoothing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

omit [Nonempty H] in
/-- Independence of whole-row resampling across disjoint complete subtrees. -/
 theorem rowSmoothing_tensor (r : ℝ) (f : I → (J → H) → ℝ) (R : I × J → H) :
    rowSmoothing r (fun x => ∏ i, f i (fun j => x (i, j))) R =
      ∏ i, rowSmoothing r (f i) (fun j => R (i, j)) := by
  classical
  unfold rowSmoothing rowsKernel
  rw [Fintype.sum_equiv (Equiv.curry I J H)
    (fun x => (∏ i : I × J, rowKernel r (R i) (x i)) * ∏ i, f i (fun j => x (i, j)))
    (fun x => ∏ i, ((∏ j, rowKernel r (R (i, j)) (x i j)) * f i (x i)))]
  · exact (Fintype.prod_sum (fun (i : I) (x : J → H) =>
      (∏ j, rowKernel r (R (i, j)) (x j)) * f i x)).symm
  · intro x
    simp only [Equiv.curry_apply, Function.curry, Fintype.prod_prod_type, Finset.prod_mul_distrib]
    rfl

/-- A tensor product with one chosen member of each ordered pair. The unused
subtrees are integrated with total mass exactly one. -/
 theorem rowSmoothing_pairs {s : ℕ} (r : ℝ) (b : Fin s → Bool)
    (f : Branch s → (J → H) → ℝ) (R : Branch s × J → H) :
    rowSmoothing r (fun x => ∏ g, f (g, b g) (fun j => x ((g, b g), j))) R =
      ∏ g, rowSmoothing r (f (g, b g)) (fun j => R ((g, b g), j)) := by
  classical
  let h : Branch s → (J → H) → ℝ := fun gb x => if gb.2 = b gb.1 then f gb x else 1
  have hp (x : Branch s × J → H) :
      (∏ i : Branch s, h i (fun j => x (i, j))) =
        ∏ g, f (g, b g) (fun j => x ((g, b g), j)) := by
    rw [Fintype.prod_prod_type]
    apply Finset.prod_congr rfl
    intro g _
    cases hb : b g <;> simp [h, hb]
  have hf := funext hp
  rw [← hf, rowSmoothing_tensor, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro g _
  cases hb : b g <;> simp [h, hb, rowSmoothing_one]

end TensorSmoothing

 theorem sum_sign : ∑ x : Bit, sign x = 0 := by
  rw [show (Finset.univ : Finset Bit) = {0, 1} by
    ext x; simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact bit_cases x]
  norm_num

 theorem rowKernel_sign (r : ℝ) (x : Bit) :
    (∑ y, rowKernel r x y * sign y) = r * sign x := by
  simp only [rowKernel, add_mul, Finset.sum_add_distrib, ← Finset.mul_sum, sum_sign,
    mul_zero, add_zero]
  simp

 theorem word_leaf_smoothing {s m : ℕ} (F : Nodes s m → Table s)
    (r : ℝ) (x : Leaves s m → Bit) :
    rowSmoothing r (fun y => sign (word F y)) x = r ^ (s ^ m) * sign (word F x) := by
  induction m with
  | zero =>
      change (∑ y : Unit → Bit, (∏ i : Unit, rowKernel r (x i) (y i)) * sign (y ())) = _
      simp only [Fintype.prod_unique]
      calc
        _ = ∑ y : Bit, rowKernel r (x ()) y * sign y := by
          exact Fintype.sum_equiv (Equiv.funUnique Unit Bit) _ _ (fun _ => rfl)
        _ = _ := by simpa only [pow_zero, pow_one, word] using rowKernel_sign r (x ())
  | succ m ih =>
      have hx (y : Leaves s (m + 1) → Bit) :
          sign (word F y) = ∑ q : Fin s → Bit,
            bitCoefficient (fun z => sign (F (.inl ()) z)) q *
              ∏ g, sign (word (fun v => F (.inr ((g, if q g = 0 then false else true), v)))
                (fun i => y ((g, if q g = 0 then false else true), i))) :=
        gate_expansion _ _
      rw [funext hx, rowSmoothing_sum]
      simp_rw [rowSmoothing_smul]
      have ht (q : Fin s → Bit) := rowSmoothing_pairs (J := Leaves s m) r
        (fun g => if q g = 0 then false else true)
        (fun gb y => sign (word (fun v => F (.inr (gb, v))) y)) x
      simp_rw [ht, ih, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
      rw [hx]
      simp only [pow_succ, pow_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring

end OptimalMaxCut.TreeCode

end OAI
