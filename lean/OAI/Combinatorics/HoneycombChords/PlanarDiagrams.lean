import OAI.Combinatorics.HoneycombChords.RasterGrid

namespace OAI

/-!
# Planar cup and cap normalization

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

/-!
Planar loop erasure for physical finite strips.
This implements the adjacent cup/cap contractions of the exact dilute
Temperley--Lieb tile. No physical partition-function estimate is assumed.
-/
namespace CriticalHoneycomb.Transfer.PlanarNormalization
open scoped BigOperators

noncomputable def phase : ℂ := Complex.exp (((Real.pi/4:ℝ):ℂ)*Complex.I)
lemma phase_ne_zero : phase ≠ 0 := Complex.exp_ne_zero _
lemma phase_sq : phase^2 = Complex.I := by
  unfold phase
  rw [← Complex.exp_nat_mul]
  convert Complex.exp_pi_div_two_mul_I using 1
  push_cast
  ring_nf

noncomputable def cup (a b : Bool) : ℂ :=
  if a=b then 0 else if a then phase⁻¹ else phase

lemma loop_value : (∑ a : Bool, ∑ b : Bool, cup a b * cup a b) = 0 := by
  simp [cup]
  rw [← sq, ← sq, inv_pow, phase_sq, Complex.inv_I]
  simp

lemma snake_left (a c : Bool) :
    (∑ b : Bool, cup a b * cup b c) = if a=c then 1 else 0 := by
  cases a <;> cases c <;> simp [cup, phase_ne_zero]

lemma snake_right (a c : Bool) :
    (∑ b : Bool, cup b a * cup c b) = if a=c then 1 else 0 := by
  cases a <;> cases c <;> simp [cup, phase_ne_zero]

abbrev State := List Bool → ℂ

/-- Insert an adjacent cup at a frontier position. States are zero on
words too short for the requested position. -/
noncomputable def create : ℕ → State → State
  | 0, f, a::b::xs => cup a b * f xs
  | 0, _, _ => 0
  | i+1, f, a::xs => create i (fun ys => f (a::ys)) xs
  | _+1, _, [] => 0

/-- Contract two adjacent frontier strands with the ordinary transpose cap. -/
noncomputable def contract : ℕ → State → State
  | 0, f, xs => ∑ a : Bool, ∑ b : Bool, cup a b * f (a::b::xs)
  | i+1, f, a::xs => contract i (fun ys => f (a::ys)) xs
  | _+1, _, [] => 0

lemma create_prefix (i : ℕ) (f : State) (a : Bool) :
    (fun xs => create (i+1) f (a::xs)) = create i (fun xs => f (a::xs)) := rfl
lemma contract_prefix (i : ℕ) (f : State) (a : Bool) :
    (fun xs => contract (i+1) f (a::xs)) = contract i (fun xs => f (a::xs)) := rfl

lemma create_zero : ∀ i : ℕ, create i (fun _ => 0) = fun _ => 0 := by
  intro i
  induction i with
  | zero => funext xs; cases xs with
    | nil => rfl
    | cons a xs => cases xs <;> simp [create]
  | succ i ih =>
    funext xs
    cases xs with
    | nil => rfl
    | cons a xs => simpa only [create] using congrFun ih xs

lemma contract_zero : ∀ i : ℕ, contract i (fun _ => 0) = fun _ => 0 := by
  intro i
  induction i with
  | zero => funext xs; simp [contract]
  | succ i ih =>
    funext xs
    cases xs with
    | nil => rfl
    | cons a xs => simpa only [contract] using congrFun ih xs

lemma contract_create_same (i : ℕ) (f : State) :
    contract i (create i f) = fun _ => 0 := by
  induction i generalizing f with
  | zero =>
    funext xs
    have hl := loop_value
    simp only [Fintype.sum_bool] at hl
    simp only [contract, create, Fintype.sum_bool]
    linear_combination f xs * hl
  | succ i ih =>
    funext xs
    cases xs with
    | nil => rfl
    | cons a xs =>
      simpa only [contract, create_prefix] using congrFun (ih (fun ys => f (a::ys))) xs

lemma contract_create_next (i : ℕ) (f : State) (xs : List Bool)
    (h : i < xs.length) :
    contract i (create (i+1) f) xs = f xs := by
  induction i generalizing f xs with
  | zero =>
    cases xs with
    | nil => simp at h
    | cons x xs =>
      cases x <;> simp [contract, create, cup, phase_ne_zero]
  | succ i ih =>
    cases xs with
    | nil => simp at h
    | cons x xs =>
      simpa only [contract, create_prefix] using
        ih (fun ys => f (x::ys)) xs (by simpa using h)

lemma contract_next_create (i : ℕ) (f : State) (xs : List Bool)
    (h : i < xs.length) :
    contract (i+1) (create i f) xs = f xs := by
  induction i generalizing f xs with
  | zero =>
    cases xs with
    | nil => simp at h
    | cons x xs =>
      cases x <;> simp [contract, create, cup, phase_ne_zero, ← mul_assoc]
  | succ i ih =>
    cases xs with
    | nil => simp at h
    | cons x xs =>
      simpa only [contract, create_prefix] using
        ih (fun ys => f (x::ys)) xs (by simpa using h)

lemma create_add (i : ℕ) (f g : State) :
    create i (fun xs => f xs + g xs) = fun xs => create i f xs + create i g xs := by
  induction i generalizing f g with
  | zero =>
    funext xs
    cases xs with
    | nil => simp [create]
    | cons x xs => cases xs <;> simp [create, mul_add]
  | succ i ih =>
    funext xs
    cases xs with
    | nil => simp [create]
    | cons x xs => exact congrFun (ih (fun ys => f (x::ys)) (fun ys => g (x::ys))) xs

lemma create_mul (i : ℕ) (z : ℂ) (f : State) :
    create i (fun xs => z * f xs) = fun xs => z * create i f xs := by
  induction i generalizing f with
  | zero =>
    funext xs
    cases xs with
    | nil => simp [create]
    | cons x xs => cases xs <;> simp [create]; ring
  | succ i ih =>
    funext xs
    cases xs with
    | nil => simp [create]
    | cons x xs => exact congrFun (ih (fun ys => f (x::ys))) xs

lemma contract_mul (i : ℕ) (z : ℂ) (f : State) :
    contract i (fun xs => z * f xs) = fun xs => z * contract i f xs := by
  induction i generalizing f with
  | zero => funext xs; simp only [contract, Fintype.sum_bool]; ring
  | succ i ih =>
    funext xs
    cases xs with
    | nil => simp [contract]
    | cons x xs => exact congrFun (ih (fun ys => f (x::ys))) xs

lemma create_mul_apply (i : ℕ) (z : ℂ) (f : State) (xs : List Bool) :
    create i (fun ys => z * f ys) xs = z * create i f xs := congrFun (create_mul i z f) xs

lemma create_sum_bool (i : ℕ) (f : Bool → State) (xs : List Bool) :
    create i (fun ys => ∑ a : Bool, f a ys) xs = ∑ a : Bool, create i (f a) xs := by
  simp only [Fintype.sum_bool]
  exact congrFun (create_add i (f true) (f false)) xs

/-- A cap wholly to the left of a newly inserted cup commutes past it. -/
lemma contract_create_before (i gap : ℕ) (f : State) :
    contract i (create (i+gap+2) f) = create (i+gap) (contract i f) := by
  induction i generalizing f with
  | zero =>
    funext xs
    simp only [Nat.zero_add]
    change (∑ a : Bool, ∑ b : Bool,
      cup a b * create gap (fun ys => f (a::b::ys)) xs) =
      create gap (fun ys => ∑ a : Bool, ∑ b : Bool, cup a b * f (a::b::ys)) xs
    simp only [create_sum_bool, create_mul_apply]
  | succ i ih =>
    funext xs
    cases xs with
    | nil => simp [Nat.succ_add, contract, create]
    | cons x xs =>
      simpa only [Nat.succ_add, contract, create_prefix, contract_prefix, create] using
        congrFun (ih (fun ys => f (x::ys))) xs

/-- A cap wholly to the right of a newly inserted cup commutes past it. -/
lemma contract_create_after (i gap : ℕ) (f : State) :
    contract (i+gap+2) (create i f) = create i (contract (i+gap) f) := by
  induction i generalizing f with
  | zero =>
    funext xs
    cases xs with
    | nil => simp [contract, create]
    | cons x xs =>
      cases xs with
      | nil => simp [contract, create]
      | cons y xs =>
        simp only [Nat.zero_add]
        change contract gap (fun ys => cup x y * f ys) xs =
          cup x y * contract gap f xs
        exact congrFun (contract_mul gap (cup x y) f) xs
  | succ i ih =>
    funext xs
    cases xs with
    | nil => simp [contract, create]
    | cons x xs =>
      simpa only [Nat.succ_add, contract, create_prefix, contract_prefix, create] using
        congrFun (ih (fun ys => f (x::ys))) xs

lemma create_congr_length (i : ℕ) (f g : State) (xs : List Bool)
    (hfg : ∀ ys, ys.length + 2 = xs.length → f ys = g ys) :
    create i f xs = create i g xs := by
  induction i generalizing f g xs with
  | zero =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y xs => simp only [create]; rw [hfg xs (by simp)]
  | succ i ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      apply ih (fun ys => f (x::ys)) (fun ys => g (x::ys)) xs
      intro ys hy
      apply hfg (x::ys)
      simp only [List.length_cons]
      omega

lemma contract_congr_length (i : ℕ) (f g : State) (xs : List Bool)
    (hfg : ∀ ys, ys.length = xs.length + 2 → f ys = g ys) :
    contract i f xs = contract i g xs := by
  induction i generalizing f g xs with
  | zero =>
    simp only [contract]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [hfg (a::b::xs) (by simp)]
  | succ i ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      apply ih (fun ys => f (x::ys)) (fun ys => g (x::ys)) xs
      intro ys hy
      apply hfg (x::ys)
      simp only [List.length_cons]
      omega

/-- A planar cup-only normal form. `b` is the number of through strands
(0 for the empty boundary, 1 for one specified oriented path). -/
inductive CupHistory (b : ℕ) : ℕ → Type
  | base : CupHistory b 0
  | insert {k : ℕ} (h : CupHistory b k) (i : ℕ) (hi : i ≤ b + 2*k) :
      CupHistory b (k+1)

noncomputable def CupHistory.eval {b : ℕ} : {k : ℕ} → CupHistory b k → State → State
  | _, .base, f => f
  | _, .insert h i _, f => create i (h.eval f)

noncomputable def optionEval {b k : ℕ} (h : Option (CupHistory b k)) (f : State) : State :=
  match h with
  | none => fun _ => 0
  | some h => h.eval f

lemma optionEval_map_insert {b k : ℕ} (r : Option (CupHistory b k))
    (i : ℕ) (hi : i ≤ b+2*k) (f : State) :
    optionEval (r.map (fun h => CupHistory.insert h i hi)) f =
      create i (optionEval r f) := by
  cases r with
  | none => exact (create_zero i).symm
  | some h => rfl

/-- Contracting any adjacent two frontier strands in a planar cup normal
form either removes a closed zero-weight loop or gives another cup normal
form. This is the local-to-global cancellation step, at exact phase pi/4. -/
theorem contract_history {b k : ℕ} (hb : b ≤ 1)
    (h : CupHistory b (k+1)) (j : ℕ) (hj : j ≤ b+2*k) (f : State) :
    ∃ r : Option (CupHistory b k), ∀ xs : List Bool, xs.length = b+2*k →
      contract j (h.eval f) xs = optionEval r f xs := by
  induction k using Nat.strong_induction_on generalizing j with
  | h k ih =>
    cases h with
    | insert old i hi =>
      by_cases heq : j=i
      · subst j
        refine ⟨none, ?_⟩
        intro xs hxs
        exact congrFun (contract_create_same i (old.eval f)) xs
      by_cases hnext : i=j+1
      · refine ⟨some old, ?_⟩
        intro xs hxs
        change contract j (create i (old.eval f)) xs = old.eval f xs
        rw [hnext]
        apply contract_create_next
        omega
      by_cases hprev : j=i+1
      · refine ⟨some old, ?_⟩
        intro xs hxs
        change contract j (create i (old.eval f)) xs = old.eval f xs
        rw [hprev]
        apply contract_next_create
        omega
      by_cases hlt : j+2 ≤ i
      · cases k with
        | zero => omega
        | succ k =>
          obtain ⟨r,hr⟩ := ih k (by omega) old j (by omega)
          have hi' : i-2 ≤ b+2*k := by omega
          refine ⟨r.map (fun q => CupHistory.insert q (i-2) hi'), ?_⟩
          intro xs hxs
          rw [optionEval_map_insert]
          change contract j (create i (old.eval f)) xs = _
          have hc : contract j (create i (old.eval f)) =
              create (i-2) (contract j (old.eval f)) := by
            have hh := contract_create_before j (i-j-2) (old.eval f)
            have ha : j+(i-j-2)=i-2 := by omega
            have hh' : j+(i-j-2)+2=i := by omega
            rw [hh', ha] at hh
            exact hh
          rw [hc]
          apply create_congr_length
          intro ys hys
          apply hr
          omega
      · have hgt : i+2 ≤ j := by omega
        cases k with
        | zero => omega
        | succ k =>
          obtain ⟨r,hr⟩ := ih k (by omega) old (j-2) (by omega)
          have hi' : i ≤ b+2*k := by omega
          refine ⟨r.map (fun q => CupHistory.insert q i hi'), ?_⟩
          intro xs hxs
          rw [optionEval_map_insert]
          change contract j (create i (old.eval f)) xs = _
          have hc : contract j (create i (old.eval f)) =
              create i (contract (j-2) (old.eval f)) := by
            have hh := contract_create_after i (j-i-2) (old.eval f)
            have ha : i+(j-i-2)=j-2 := by omega
            have hh' : i+(j-i-2)+2=j := by omega
            rw [hh', ha] at hh
            exact hh
          rw [hc]
          apply create_congr_length
          intro ys hys
          apply hr
          omega

/-- A sliced planar diagram, with all vacant strands suppressed. The local
moves are exactly cup creation and adjacent cap contraction; any number
of identity tiles can be inserted without changing this word. -/
inductive PlanarWord (b : ℕ) : ℕ → Type
  | start : PlanarWord b 0
  | insert {k : ℕ} (w : PlanarWord b k) (i : ℕ) (hi : i ≤ b+2*k) :
      PlanarWord b (k+1)
  | erase {k : ℕ} (w : PlanarWord b (k+1)) (i : ℕ) (hi : i ≤ b+2*k) :
      PlanarWord b k

noncomputable def PlanarWord.eval {b : ℕ} : {k : ℕ} → PlanarWord b k → State → State
  | _, .start, f => f
  | _, .insert w i _, f => create i (w.eval f)
  | _, .erase w i _, f => contract i (w.eval f)

theorem word_normal_form {b k : ℕ} (hb : b ≤ 1) (w : PlanarWord b k) (f : State) :
    ∃ r : Option (CupHistory b k), ∀ xs : List Bool, xs.length = b+2*k →
      w.eval f xs = optionEval r f xs := by
  induction w with
  | start => exact ⟨some .base, fun _ _ => rfl⟩
  | @insert k w i hi ih =>
    obtain ⟨r,hr⟩ := ih
    refine ⟨r.map (fun q => CupHistory.insert q i hi), ?_⟩
    intro xs hxs
    rw [optionEval_map_insert]
    change create i (w.eval f) xs = create i (optionEval r f) xs
    apply create_congr_length
    intro ys hys
    apply hr
    omega
  | @erase k w i hi ih =>
    obtain ⟨r,hr⟩ := ih
    cases r with
    | none =>
      refine ⟨none, ?_⟩
      intro xs hxs
      change contract i (w.eval f) xs = 0
      calc
        _ = contract i (fun _ => 0) xs := by
          apply contract_congr_length
          intro ys hys
          apply hr
          omega
        _ = 0 := congrFun (contract_zero i) xs
    | some h =>
      obtain ⟨r,hr'⟩ := contract_history hb h i hi f
      refine ⟨r, ?_⟩
      intro xs hxs
      change contract i (w.eval f) xs = optionEval r f xs
      calc
        _ = contract i (h.eval f) xs := by
          apply contract_congr_length
          intro ys hys
          apply hr
          omega
        _ = optionEval r f xs := hr' xs hxs

/-- Every nonempty closed planar arc diagram has zero contraction.
This is a proved normalization theorem, not a loop-cancellation assumption. -/
theorem closed_word_zero (w : PlanarWord 0 0) (hw : w ≠ .start) (f : State) :
    w.eval f [] = 0 := by
  cases w with
  | start => exact (hw rfl).elim
  | erase w i hi =>
    have hi0 : i=0 := by omega
    subst i
    obtain ⟨r,hr⟩ := word_normal_form (by omega : 0 ≤ 1) w f
    change contract 0 (w.eval f) [] = 0
    have hc : contract 0 (w.eval f) [] = contract 0 (optionEval r f) [] := by
      apply contract_congr_length
      intro ys hys
      apply hr
      simpa using hys
    rw [hc]
    cases r with
    | none => exact congrFun (contract_zero 0) []
    | some h =>
      cases h with
      | insert q j hj =>
        have hj0 : j=0 := by omega
        subst j
        exact congrFun (contract_create_same 0 (q.eval f)) []

/-- A one-strand planar rectangle is either killed by a loop or acts as
identity on its specified orientation. This gives the phase-1 alternative
used for a surviving right-to-left path in the physical matrix expansion. -/
theorem one_strand_zero_or_identity (w : PlanarWord 1 0) (f : State) :
    (∀ a : Bool, w.eval f [a] = 0) ∨ (∀ a : Bool, w.eval f [a] = f [a]) := by
  obtain ⟨r,hr⟩ := word_normal_form (by omega : 1 ≤ 1) w f
  cases r with
  | none => exact Or.inl (fun a => hr [a] (by simp))
  | some h =>
    cases h with
    | base => exact Or.inr (fun a => hr [a] (by simp))


/-! Finite dilute networks. The following operator acts on the *actual* three
spin states (vacant and two occupied orientations); it is the planar local
matrix `P R` in the source. No loop-erasure hypothesis enters this definition. -/
abbrev Spin := Option Bool
abbrev DiluteState := List Spin → ℂ

def occupancy (xs : List Spin) : List Bool := xs.map Option.isSome
def orientations (xs : List Spin) : List Bool := xs.filterMap id
noncomputable def embed (o : List Bool) (f : State) : DiluteState :=
  fun xs => if occupancy xs = o then f (orientations xs) else 0

lemma embed_add (o : List Bool) (f g : State) :
    embed o (fun xs => f xs + g xs) = fun xs => embed o f xs + embed o g xs := by
  funext xs
  simp only [embed]
  split <;> simp
lemma embed_smul (o : List Bool) (z : ℂ) (f : State) :
    embed o (fun xs => z * f xs) = fun xs => z * embed o f xs := by
  funext xs
  simp only [embed]
  split <;> simp
lemma embed_zero (o : List Bool) : embed o (fun _ => 0) = fun _ => 0 := by
  funext xs; simp [embed]
@[simp] lemma embed_false (o : List Bool) (f : State) (xs : List Spin) :
    embed (false::o) f (none::xs) = embed o f xs := by
  simp [embed, occupancy, orientations]
@[simp] lemma embed_true (o : List Bool) (f : State) (a : Bool) (xs : List Spin) :
    embed (true::o) f (some a::xs) = embed o (fun ys => f (a::ys)) xs := by
  simp [embed, occupancy, orientations]
@[simp] lemma embed_false_some (o : List Bool) (f : State) (a : Bool) (xs : List Spin) :
    embed (false::o) f (some a::xs) = 0 := by simp [embed,occupancy]
@[simp] lemma embed_true_none (o : List Bool) (f : State) (xs : List Spin) :
    embed (true::o) f (none::xs) = 0 := by simp [embed,occupancy]
@[simp] lemma embed_cons_nil (a : Bool) (o : List Bool) (f : State) :
    embed (a::o) f [] = 0 := by simp [embed,occupancy]

structure TileWeights where
  a : ℂ
  h : ℂ
  v : ℂ
  c : ℂ
  d : ℂ

noncomputable def tile (t : TileWeights) : Spin → Spin → Spin → Spin → ℂ
  | none, none, none, none => 1
  | some i, none, some k, none => if i=k then t.a else 0
  | none, some i, none, some k => if i=k then t.a else 0
  | some i, none, none, some k => if i=k then t.v else 0
  | none, some i, some k, none => if i=k then t.v else 0
  | some i, some j, none, none => t.h * cup i j
  | none, none, some k, some l => t.h * cup k l
  | some i, some j, some k, some l =>
      (if i=k ∧ j=l then t.c else 0) + t.d * cup i j * cup k l
  | _,_,_,_ => 0

noncomputable def act (t : TileWeights) : ℕ → DiluteState → DiluteState
  | 0, f, x::y::xs => ∑ a : Spin, ∑ b : Spin, tile t x y a b * f (a::b::xs)
  | 0, _, _ => 0
  | i+1, f, x::xs => act t i (fun ys => f (x::ys)) xs
  | _+1, _, [] => 0

lemma act_add (t : TileWeights) (i : ℕ) (f g : DiluteState) :
    act t i (fun xs => f xs + g xs) = fun xs => act t i f xs + act t i g xs := by
  induction i generalizing f g with
  | zero =>
    funext xs
    cases xs with
    | nil => simp [act]
    | cons a xs => cases xs <;> simp [act, mul_add, Finset.sum_add_distrib]
  | succ i ih =>
    funext xs
    cases xs with
    | nil => simp [act]
    | cons a xs => exact congrFun (ih (fun ys => f (a::ys)) (fun ys => g (a::ys))) xs
lemma act_smul (t : TileWeights) (i : ℕ) (z : ℂ) (f : DiluteState) :
    act t i (fun xs => z * f xs) = fun xs => z * act t i f xs := by
  induction i generalizing f with
  | zero =>
    funext xs
    cases xs with
    | nil => simp [act]
    | cons a xs => cases xs <;> simp [act, mul_left_comm, mul_add]
  | succ i ih =>
    funext xs
    cases xs with
    | nil => simp [act]
    | cons a xs => exact congrFun (ih (fun ys => f (a::ys))) xs
lemma act_zero (t : TileWeights) (i : ℕ) : act t i (fun _ => 0) = fun _ => 0 := by
  simpa only [zero_mul] using act_smul t i 0 (fun _ => 0)

lemma act_empty_pair (t : TileWeights) (o : List Bool) (f : State) :
    act t 0 (embed (false::false::o) f) = fun xs =>
      embed (false::false::o) f xs + t.h * embed (true::true::o) (create 0 f) xs := by
  funext xs
  cases xs with
  | nil => simp [act]
  | cons x xs =>
    cases xs with
    | nil => cases x <;> simp [act]
    | cons y xs =>
      fin_cases x <;> fin_cases y <;>
        simp [act, tile, Fintype.sum_option, create, embed, occupancy, orientations, mul_assoc] 

lemma act_left_pair (t : TileWeights) (o : List Bool) (f : State) :
    act t 0 (embed (true::false::o) f) = fun xs =>
      t.a * embed (true::false::o) f xs + t.v * embed (false::true::o) f xs := by
  funext xs
  cases xs with
  | nil => simp [act]
  | cons x xs =>
    cases xs with
    | nil => cases x <;> simp [act]
    | cons y xs =>
      fin_cases x <;> fin_cases y <;>
        simp [act, tile, Fintype.sum_option, embed, occupancy, orientations] 

lemma act_right_pair (t : TileWeights) (o : List Bool) (f : State) :
    act t 0 (embed (false::true::o) f) = fun xs =>
      t.a * embed (false::true::o) f xs + t.v * embed (true::false::o) f xs := by
  funext xs
  cases xs with
  | nil => simp [act]
  | cons x xs =>
    cases xs with
    | nil => cases x <;> simp [act]
    | cons y xs =>
      fin_cases x <;> fin_cases y <;>
        simp [act, tile, Fintype.sum_option, embed, occupancy, orientations] 

lemma act_full_pair (t : TileWeights) (o : List Bool) (f : State) :
    act t 0 (embed (true::true::o) f) = fun xs =>
      t.c * embed (true::true::o) f xs +
      t.h * embed (false::false::o) (contract 0 f) xs +
      t.d * embed (true::true::o) (create 0 (contract 0 f)) xs := by
  funext xs
  cases xs with
  | nil => simp [act]
  | cons x xs =>
    cases xs with
    | nil => cases x <;> simp [act]
    | cons y xs =>
      fin_cases x <;> fin_cases y <;>
        simp [act, tile, Fintype.sum_option, contract, create,
          Finset.sum_add_distrib, add_mul, mul_assoc, embed, occupancy, orientations] <;> split_ifs <;> ring


lemma act_empty_at (t : TileWeights) (pre o : List Bool) (f : State) :
    act t pre.length (embed (pre ++ false::false::o) f) = fun xs =>
      embed (pre ++ false::false::o) f xs +
      t.h * embed (pre ++ true::true::o) (create (pre.count true) f) xs := by
  induction pre generalizing f with
  | nil => exact act_empty_pair t o f
  | cons b pre ih =>
    funext xs
    cases xs with
    | nil => simp [act]
    | cons x xs =>
      cases b <;> cases x with
      | none => simp [act, ih, act_zero]
      | some a =>
        simp [act, create_prefix, act_zero, ih]

lemma act_left_at (t : TileWeights) (pre o : List Bool) (f : State) :
    act t pre.length (embed (pre ++ true::false::o) f) = fun xs =>
      t.a * embed (pre ++ true::false::o) f xs +
      t.v * embed (pre ++ false::true::o) f xs := by
  induction pre generalizing f with
  | nil => exact act_left_pair t o f
  | cons b pre ih =>
    funext xs
    cases xs with
    | nil => simp [act]
    | cons x xs =>
      cases b <;> cases x with
      | none => simp [act, ih, act_zero]
      | some a =>
        simp [act, act_zero, ih]

lemma act_right_at (t : TileWeights) (pre o : List Bool) (f : State) :
    act t pre.length (embed (pre ++ false::true::o) f) = fun xs =>
      t.a * embed (pre ++ false::true::o) f xs +
      t.v * embed (pre ++ true::false::o) f xs := by
  induction pre generalizing f with
  | nil => exact act_right_pair t o f
  | cons b pre ih =>
    funext xs
    cases xs with
    | nil => simp [act]
    | cons x xs =>
      cases b <;> cases x with
      | none => simp [act, ih, act_zero]
      | some a =>
        simp [act, act_zero, ih]

lemma act_full_at (t : TileWeights) (pre o : List Bool) (f : State) :
    act t pre.length (embed (pre ++ true::true::o) f) = fun xs =>
      t.c * embed (pre ++ true::true::o) f xs +
      t.h * embed (pre ++ false::false::o) (contract (pre.count true) f) xs +
      t.d * embed (pre ++ true::true::o) (create (pre.count true) (contract (pre.count true) f)) xs := by
  induction pre generalizing f with
  | nil => exact act_full_pair t o f
  | cons b pre ih =>
    funext xs
    cases xs with
    | nil => simp [act]
    | cons x xs =>
      cases b <;> cases x with
      | none => simp [act, ih, act_zero]
      | some a =>
        simp [act, create_prefix, contract_prefix, act_zero, ih]


/-- Finite linear combinations of sliced planar diagrams with no incoming
occupied strand. The count equality fixes the exact frontier arity. -/
inductive PlanarSpan (n : ℕ) : DiluteState → Prop
  | zero : PlanarSpan n (fun _ => 0)
  | basis (o : List Bool) (k : ℕ) (w : PlanarWord 0 k)
      (hl : o.length = n) (hc : o.count true = 2*k) :
      PlanarSpan n (embed o (w.eval (fun _ => 1)))
  | add {f g : DiluteState} (hf : PlanarSpan n f) (hg : PlanarSpan n g) :
      PlanarSpan n (fun xs => f xs + g xs)
  | smul (z : ℂ) {f : DiluteState} (hf : PlanarSpan n f) :
      PlanarSpan n (fun xs => z * f xs)

lemma two_at (o : List Bool) (i : ℕ) (hi : i+1 < o.length) :
    ∃ pre : List Bool, ∃ a b : Bool, ∃ post : List Bool,
      o = pre ++ a::b::post ∧ pre.length = i := by
  induction i generalizing o with
  | zero =>
    cases o with
    | nil => simp at hi
    | cons a o =>
      cases o with
      | nil => simp at hi
      | cons b post => exact ⟨[],a,b,post,rfl,rfl⟩
  | succ i ih =>
    cases o with
    | nil => simp at hi
    | cons a o =>
      obtain ⟨pre,b,c,post,ho,hpre⟩ := ih o (by simpa using hi)
      exact ⟨a::pre,b,c,post,by simp [ho],by simp [hpre]⟩

lemma act_span (t : TileWeights) {n i : ℕ} (hi : i+1<n)
    {f : DiluteState} (hf : PlanarSpan n f) : PlanarSpan n (act t i f) := by
  induction hf with
  | zero => rw [act_zero]; exact .zero
  | add hf hg ihf ihg => rw [act_add]; exact .add ihf ihg
  | smul z hf ihf => rw [act_smul]; exact .smul z ihf
  | basis o k w hl hc =>
    obtain ⟨pre,a,b,post,rfl,hpre⟩ := two_at o i (by omega)
    subst i
    cases a <;> cases b
    · rw [act_empty_at]
      apply PlanarSpan.add (.basis _ k w hl hc)
      apply PlanarSpan.smul
      have hip : pre.count true ≤ 0+2*k := by simp [List.count_append] at hc; omega
      exact .basis _ (k+1) (.insert w (pre.count true) hip)
        (by simpa using hl) (by simp_all [List.count_append]; omega)
    · rw [act_right_at]
      exact .add (.smul _ (.basis _ k w hl hc))
        (.smul _ (.basis _ k w (by simpa using hl)
          (by simpa [List.count_append, List.count_cons] using hc)))
    · rw [act_left_at]
      exact .add (.smul _ (.basis _ k w hl hc))
        (.smul _ (.basis _ k w (by simpa using hl)
          (by simpa [List.count_append, List.count_cons] using hc)))
    · have hk : 0<k := by simp [List.count_append] at hc; omega
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
      have hip : pre.count true ≤ 0+2*k := by simp [List.count_append] at hc ⊢; omega
      rw [act_full_at]
      apply PlanarSpan.add
      · apply PlanarSpan.add
        · exact .smul _ (.basis _ (k+1) w hl hc)
        · apply PlanarSpan.smul
          exact .basis _ k (.erase w (pre.count true) hip) (by simpa using hl)
            (by simp [List.count_append] at hc ⊢; omega)
      · apply PlanarSpan.smul
        exact .basis _ (k+1) (.insert (.erase w (pre.count true) hip) (pre.count true) hip) hl hc

lemma embed_vacuum_pos (o : List Bool) (f : State) (n : ℕ)
    (hc : 0 < o.count true) : embed o f (List.replicate n none) = 0 := by
  have hne : List.replicate n false ≠ o := by
    intro h
    have hh := congrArg (List.count true) h
    have hcnt : (List.replicate n false).count true = 0 := by simp [List.count_replicate]
    rw [hcnt] at hh
    omega
  simp [embed, occupancy, hne]

lemma embed_vacuum_zero (n : ℕ) (o : List Bool) (f : State) (hz : f [] = 0) :
    embed o f (List.replicate n none) = 0 := by
  simp [embed, orientations, hz]

lemma erased_empty (w : PlanarWord 0 1) (i : ℕ) (hi : i ≤ 0+2*0) :
    contract i (w.eval (fun _ => 1)) [] = 0 := by
  exact closed_word_zero (.erase w i hi) (by intro h; cases h) (fun _ => 1)

lemma act_basis_vacuum (t : TileWeights) {n i : ℕ} (hi : i+1<n)
    (o : List Bool) (k : ℕ) (w : PlanarWord 0 k)
    (hl : o.length=n) (hc : o.count true=2*k) :
    act t i (embed o (w.eval (fun _ => 1))) (List.replicate n none) =
      embed o (w.eval (fun _ => 1)) (List.replicate n none) := by
  obtain ⟨pre,a,b,post,rfl,hpre⟩ := two_at o i (by omega)
  subst i
  cases a <;> cases b
  · rw [act_empty_at]
    simp only
    rw [embed_vacuum_pos (pre ++ true::true::post) _ n (by simp [List.count_append])]
    ring
  · rw [act_right_at]
    simp only
    rw [embed_vacuum_pos _ _ n (by simp [List.count_append])]
    rw [embed_vacuum_pos _ _ n (by simp [List.count_append])]
    ring
  · rw [act_left_at]
    simp only
    rw [embed_vacuum_pos _ _ n (by simp [List.count_append])]
    rw [embed_vacuum_pos _ _ n (by simp [List.count_append])]
    ring
  · rw [act_full_at]
    simp only
    have hpos : 0 < (pre ++ true::true::post).count true := by simp [List.count_append]
    simp only [embed_vacuum_pos (pre ++ true::true::post) _ n hpos]
    have hzero : embed (pre ++ false::false::post)
        (contract (pre.count true) (w.eval (fun _ => 1))) (List.replicate n none)=0 := by
      by_cases hp : 0<(pre ++ false::false::post).count true
      · exact embed_vacuum_pos _ _ n hp
      · apply embed_vacuum_zero
        have he : (pre ++ false::false::post).count true = pre.count true + post.count true := by simp
        have ht : (pre ++ true::true::post).count true = pre.count true + post.count true + 2 := by simp; omega
        rw [he] at hp
        rw [ht] at hc
        have hk : k=1 := by omega
        subst k
        apply erased_empty
        omega
    rw [hzero]
    ring

lemma act_vacuum (t : TileWeights) {n i : ℕ} (hi : i+1<n)
    {f : DiluteState} (hf : PlanarSpan n f) :
    act t i f (List.replicate n none) = f (List.replicate n none) := by
  induction hf with
  | zero => simp [act_zero]
  | basis o k w hl hc => exact act_basis_vacuum t hi o k w hl hc
  | add hf hg ihf ihg => simp only [act_add, ihf, ihg]
  | smul z hf ihf => simp only [act_smul, ihf]

/-- A sequence of arbitrary nearest-neighbor dilute planar tiles cannot
change the vacuum-to-vacuum coefficient. Nonempty closed diagrams cancel;
this is the finite-network statement used in the physical crossing proof. -/
theorem circuit_vacuum (n : ℕ) (gates : List (TileWeights × ℕ))
    (hg : ∀ g ∈ gates, g.2+1<n) :
    (gates.foldl (fun f g => act g.1 g.2 f)
      (embed (List.replicate n false) (fun _ => 1))) (List.replicate n none) = 1 := by
  have general : ∀ (gs : List (TileWeights × ℕ)) (f : DiluteState),
      (∀ g ∈ gs, g.2+1<n) → PlanarSpan n f →
      gs.foldl (fun f g => act g.1 g.2 f) f (List.replicate n none) =
        f (List.replicate n none) := by
    intro gs
    induction gs with
    | nil => intro f _ _; rfl
    | cons g gs ih =>
      intro f hg hf
      rw [List.foldl_cons, ih _ (by aesop) (act_span g.1 (hg g (by simp)) hf)]
      exact act_vacuum g.1 (hg g (by simp)) hf
  have hf : PlanarSpan n (embed (List.replicate n false) (fun _ => 1)) :=
    PlanarSpan.basis (List.replicate n false) 0 .start (by simp) (by simp [List.count_replicate])
  rw [general gates _ hg hf]
  simp [embed, occupancy]


/-- The manuscript's spin order is +,0,-; vacancies are not weighted. -/
def spinIndex : Spin → Fin 3
  | none => 1
  | some false => 0
  | some true => 2

noncomputable def sourcePhase : ℂ :=
  Complex.exp (((2*(Real.pi/8):ℝ):ℂ)*Complex.I)
lemma sourcePhase_eq : sourcePhase = phase := by
  unfold sourcePhase phase
  congr 3
  ring

/-- Verbatim source local R entries. -/
noncomputable def sourceR (t : TileWeights) (p q : Fin 3 × Fin 3) : ℂ :=
  match p.1.val, p.2.val, q.1.val, q.2.val with
  | 0, 0, 0, 0 => t.c
  | 2, 2, 2, 2 => t.c
  | 0, 1, 0, 1 | 1, 0, 1, 0 | 2, 1, 2, 1 | 1, 2, 1, 2 => t.v
  | 0, 1, 1, 0 | 1, 0, 0, 1 | 2, 1, 1, 2 | 1, 2, 2, 1 => t.a
  | 0, 2, 0, 2 => t.d
  | 0, 2, 1, 1 => t.h / sourcePhase
  | 0, 2, 2, 0 => t.c+t.d/sourcePhase^2
  | 1, 1, 0, 2 => t.h*sourcePhase
  | 1, 1, 1, 1 => 1
  | 1, 1, 2, 0 => t.h/sourcePhase
  | 2, 0, 0, 2 => t.c+t.d*sourcePhase^2
  | 2, 0, 1, 1 => t.h*sourcePhase
  | 2, 0, 2, 0 => t.d
  | _, _, _, _ => 0

/-- The circuit tiles are exactly P R, not a substituted planar model. -/
theorem tile_eq_sourceR (t : TileWeights) (i j k l : Spin) :
    tile t i j k l = sourceR t (spinIndex j, spinIndex i) (spinIndex k, spinIndex l) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [tile, sourceR, spinIndex, cup, sourcePhase_eq, phase_ne_zero, div_eq_mul_inv] <;>
    ring


/-- Introduce two vacant auxiliary wires at the input boundary. -/
noncomputable def addAux (f : DiluteState) : DiluteState
  | none::none::xs => f xs
  | _ => 0

/-- Cap two vacant auxiliary wires at the output boundary. Boundary K is
implemented by one adjacent tile before this cap. -/
noncomputable def removeAux (f : DiluteState) : DiluteState :=
  fun xs => f (xs ++ [none,none])

lemma addAux_embed (o : List Bool) (f : State) :
    addAux (embed o f) = embed (false::false::o) f := by
  funext xs
  cases xs with
  | nil => simp [addAux]
  | cons x xs =>
    cases xs with
    | nil => cases x <;> simp [addAux]
    | cons y xs => cases x <;> cases y <;> simp [addAux]

lemma removeAux_embed (o : List Bool) (a b : Bool) (f : State) :
    removeAux (embed (o ++ [a,b]) f) =
      if a=false ∧ b=false then embed o f else fun _ => 0 := by
  funext xs
  have heq : occupancy (xs ++ [none,none]) = o ++ [a,b] ↔
      occupancy xs = o ∧ a=false ∧ b=false := by
    simp only [occupancy, List.map_append]
    constructor
    · intro h
      have hh := List.append_inj' h (by simp)
      simpa using hh
    · rintro ⟨rfl,rfl,rfl⟩
      rfl
  simp only [removeAux,embed,heq,orientations,List.filterMap_append]
  cases a <;> cases b <;> simp [embed,orientations]

lemma addAux_span {n : ℕ} {f : DiluteState} (hf : PlanarSpan n f) :
    PlanarSpan (n+2) (addAux f) := by
  induction hf with
  | zero =>
    have h : addAux (fun _ => 0) = fun _ => 0 := by
      funext xs; cases xs with
      | nil => rfl
      | cons x xs => cases xs with
        | nil => cases x <;> rfl
        | cons y xs => cases x <;> cases y <;> rfl
    rw [h]; exact .zero
  | basis o k w hl hc =>
    rw [addAux_embed]
    exact .basis _ k w (by simp [hl]) (by simpa using hc)
  | add hf hg ihf ihg =>
    have h : ∀ f g, addAux (fun xs => f xs + g xs) =
        fun xs => addAux f xs + addAux g xs := by
      intro f g; funext xs; cases xs with
      | nil => simp [addAux]
      | cons x xs => cases xs with
        | nil => cases x <;> simp [addAux]
        | cons y xs => cases x <;> cases y <;> simp [addAux]
    rw [h]; exact .add ihf ihg
  | smul z hf ihf =>
    have h : ∀ f, addAux (fun xs => z * f xs) = fun xs => z * addAux f xs := by
      intro f; funext xs; cases xs with
      | nil => simp [addAux]
      | cons x xs => cases xs with
        | nil => cases x <;> simp [addAux]
        | cons y xs => cases x <;> cases y <;> simp [addAux]
    rw [h]; exact .smul z ihf

lemma removeAux_span {n : ℕ} {f : DiluteState} (hf : PlanarSpan (n+2) f) :
    PlanarSpan n (removeAux f) := by
  induction hf with
  | zero => exact .zero
  | add hf hg ihf ihg => exact .add ihf ihg
  | smul z hf ihf => exact .smul z ihf
  | basis o k w hl hc =>
    obtain ⟨pre,a,b,post,rfl,hpre⟩ := two_at o n (by omega)
    have hp : post=[] := List.length_eq_zero_iff.mp (by simp at hl; omega)
    subst post
    rw [removeAux_embed]
    split_ifs with hab
    · rcases hab with ⟨rfl,rfl⟩
      exact .basis _ k w hpre (by simpa using hc)
    · exact .zero

lemma gates_span {n : ℕ} (gs : List (TileWeights × ℕ))
    (hg : ∀ g ∈ gs, g.2+1<n) {f : DiluteState} (hf : PlanarSpan n f) :
    PlanarSpan n (gs.foldl (fun f g => act g.1 g.2 f) f) := by
  induction gs generalizing f with
  | nil => exact hf
  | cons g gs ih => exact ih (by aesop) (act_span g.1 (hg g (by simp)) hf)

lemma gates_vacuum {n : ℕ} (gs : List (TileWeights × ℕ))
    (hg : ∀ g ∈ gs, g.2+1<n) {f : DiluteState} (hf : PlanarSpan n f) :
    gs.foldl (fun f g => act g.1 g.2 f) f (List.replicate n none) =
      f (List.replicate n none) := by
  induction gs generalizing f with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (by aesop) (act_span g.1 (hg g (by simp)) hf)]
    exact act_vacuum g.1 (hg g (by simp)) hf

noncomputable def auxNetwork (gs : List (TileWeights × ℕ)) (f : DiluteState) : DiluteState :=
  removeAux (gs.foldl (fun f g => act g.1 g.2 f) (addAux f))

lemma auxNetwork_span {n : ℕ} (gs : List (TileWeights × ℕ))
    (hg : ∀ g ∈ gs, g.2+1<n+2) {f : DiluteState} (hf : PlanarSpan n f) :
    PlanarSpan n (auxNetwork gs f) :=
  removeAux_span (gates_span gs hg (addAux_span hf))

/-- Inserting and then removing the two auxiliary wires preserves the
same vacuum coefficient, so products of double-row networks do as well. -/
theorem auxNetwork_vacuum {n : ℕ} (gs : List (TileWeights × ℕ))
    (hg : ∀ g ∈ gs, g.2+1<n+2) {f : DiluteState} (hf : PlanarSpan n f) :
    auxNetwork gs f (List.replicate n none) = f (List.replicate n none) := by
  unfold auxNetwork removeAux
  have hh : List.replicate n (none : Spin) ++ [none,none] = List.replicate (n+2) none := by
    rw [List.replicate_add]; rfl
  rw [hh,gates_vacuum gs hg (addAux_span hf)]
  have hh' : List.replicate (n+2) (none : Spin) = none::none::List.replicate n none := by
    rw [show n+2=2+n by omega, List.replicate_add]; rfl
  rw [hh']; rfl

noncomputable def boundaryWeights (k : ℂ) : TileWeights := ⟨0,k,0,0,0⟩
noncomputable def K (k : ℂ) : Spin → Spin → ℂ
  | none,none => 1
  | some a,some b => k * cup a b
  | _,_ => 0

lemma boundary_input (k : ℂ) (a b : Spin) :
    tile (boundaryWeights k) a b none none = K k a b := by
  cases a <;> cases b <;> rfl
lemma boundary_output (k : ℂ) (a b : Spin) :
    tile (boundaryWeights k) none none a b = K k a b := by
  cases a <;> cases b <;> rfl


/-- The unswapped source R matrix, in the vacant/occupied encoding. -/
noncomputable def rEntry (t : TileWeights) (a b p q : Spin) : ℂ :=
  sourceR t (spinIndex a, spinIndex b) (spinIndex p, spinIndex q)

/-- Source R_{aux,i}: the auxiliary is the first wire, physical site i
is at position i+1. All other wires are spectators. -/
noncomputable def rAux (t : TileWeights) : ℕ → DiluteState → DiluteState
  | 0, f, a::b::xs => ∑ p : Spin, ∑ q : Spin, rEntry t a b p q * f (p::q::xs)
  | 0, _, _ => 0
  | i+1, f, a::b::xs =>
      rAux t i (fun zs => match zs with
        | p::ys => f (p::b::ys)
        | [] => 0) (a::xs)
  | _+1, _, _ => 0

/-- Move the auxiliary from the front to position i, preserving the
order of all physical sites. This is only a permutation, not a trace. -/
noncomputable def moveAux : ℕ → DiluteState → DiluteState
  | 0, f => f
  | i+1, f => fun xs => match xs with
    | x::ys => moveAux i (fun zs => match zs with
      | a::ws => f (a::x::ws)
      | [] => 0) ys
    | [] => 0

lemma rAux_nil (t : TileWeights) (i : ℕ) (f : DiluteState) :
    rAux t i f [] = 0 := by cases i <;> rfl
lemma rAux_singleton (t : TileWeights) (i : ℕ) (f : DiluteState) (a : Spin) :
    rAux t i f [a] = 0 := by cases i <;> rfl

/-- The exact local permutation identity behind the planar row drawing. -/
theorem act_moveAux (t : TileWeights) (i : ℕ) (f : DiluteState) :
    act t i (moveAux i f) = moveAux (i+1) (rAux t i f) := by
  induction i generalizing f with
  | zero =>
    funext xs
    cases xs with
    | nil => rfl
    | cons a xs => cases xs with
      | nil => rfl
      | cons b xs =>
        simp only [act,moveAux,rAux,rEntry]
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro q hq
        rw [tile_eq_sourceR]
  | succ i ih =>
    funext xs
    cases xs with
    | nil => rfl
    | cons x xs =>
      simp only [act,moveAux]
      rw [ih]
      congr 1

/-- Apply a row in visiting order; source U is this composition with
its physical sites listed N,...,1, since the rightmost matrix acts first. -/
noncomputable def unswappedRow : ℕ → List TileWeights → DiluteState → DiluteState
  | _, [], f => f
  | i, t::ts, f => unswappedRow (i+1) ts (rAux t i f)

noncomputable def planarRow : ℕ → List TileWeights → DiluteState → DiluteState
  | _, [], f => f
  | i, t::ts, f => planarRow (i+1) ts (act t i f)

/-- A whole row of adjacent P R gates is exactly the source row of R
matrices followed by moving its auxiliary wire to the output. -/
theorem planarRow_eq (i : ℕ) (ts : List TileWeights) (f : DiluteState) :
    planarRow i ts (moveAux i f) =
      moveAux (i+ts.length) (unswappedRow i ts f) := by
  induction ts generalizing i f with
  | nil => rfl
  | cons t ts ih =>
    simp only [planarRow,unswappedRow,List.length_cons]
    rw [act_moveAux,ih]
    congr 1
    omega


lemma moveAux_at (pre : List Spin) (a : Spin) (post : List Spin) (f : DiluteState) :
    moveAux pre.length f (pre ++ a::post) = f (a::(pre++post)) := by
  induction pre generalizing f with
  | nil => rfl
  | cons x pre ih =>
    simp only [List.length_cons,List.cons_append,moveAux]
    rw [ih]

lemma rAux_at (t : TileWeights) (pre : List Spin) (a b : Spin)
    (post : List Spin) (f : DiluteState) :
    rAux t pre.length f (a::(pre++b::post)) =
      ∑ p : Spin, ∑ q : Spin, rEntry t a b p q * f (p::(pre++q::post)) := by
  induction pre generalizing f with
  | nil => rfl
  | cons x pre ih =>
    simp only [List.length_cons,List.cons_append,rAux]
    rw [ih]

lemma act_at (t : TileWeights) (pre : List Spin) (a b : Spin)
    (post : List Spin) (f : DiluteState) :
    act t pre.length f (pre++a::b::post) =
      ∑ p : Spin, ∑ q : Spin, tile t a b p q * f (pre++p::q::post) := by
  induction pre generalizing f with
  | nil => rfl
  | cons x pre ih =>
    simpa only [List.length_cons,List.cons_append,act] using
      ih (fun xs => f (x::xs))

/-- Lift an operator through a spectator wire. -/
noncomputable def behind (F : DiluteState → DiluteState) (f : DiluteState) : DiluteState
  | a::xs => F (fun ys => f (a::ys)) xs
  | [] => 0

lemma act_behind (t : TileWeights) (i : ℕ) (F : DiluteState → DiluteState)
    (f : DiluteState) :
    act t (i+1) (behind F f) = behind (fun g => act t i (F g)) f := by
  funext xs
  cases xs <;> rfl

lemma planarRow_behind (i : ℕ) (ts : List TileWeights)
    (F : DiluteState → DiluteState) (f : DiluteState) :
    planarRow (i+1) ts (behind F f) = behind (fun g => planarRow i ts (F g)) f := by
  induction ts generalizing i F f with
  | nil => rfl
  | cons t ts ih =>
    simp only [planarRow,act_behind]
    rw [ih]

/-- Equivalence of coordinates when B is moved past n physical sites,
with the A auxiliary fixed at the front. -/
def BCoordinates (n : ℕ) (f g : DiluteState) : Prop :=
  ∀ (a b : Spin) (xs : List Spin), xs.length=n →
    f (a::(xs++[b])) = g (a::b::xs)

lemma behind_move_B (n : ℕ) (f : DiluteState) :
    BCoordinates n (behind (moveAux n) f) f := by
  intro a b xs hx
  simp only [behind]
  rw [← hx,moveAux_at]
  simp

lemma one_at {α : Type*} (xs : List α) (i : ℕ) (hi : i<xs.length) :
    ∃ pre : List α, ∃ x : α, ∃ post : List α,
      xs = pre++x::post ∧ pre.length=i := by
  induction i generalizing xs with
  | zero =>
    cases xs with
    | nil => simp at hi
    | cons x xs => exact ⟨[],x,xs,rfl,rfl⟩
  | succ i ih =>
    cases xs with
    | nil => simp at hi
    | cons x xs =>
      obtain ⟨pre,y,post,hp,hl⟩ := ih xs (by simpa using hi)
      exact ⟨x::pre,y,post,by simp [hp],by simp [hl]⟩

lemma rAux_BCoordinates {n i : ℕ} (hi : i<n) (t : TileWeights)
    {f g : DiluteState} (h : BCoordinates n f g) :
    BCoordinates n (rAux t i f) (rAux t (i+1) g) := by
  intro a b xs hx
  obtain ⟨pre,x,post,rfl,hpre⟩ := one_at xs i (by omega)
  rw [← hpre]
  simp only [List.cons_append,List.append_assoc]
  change rAux t pre.length f (a::(pre++x::(post++[b]))) =
    rAux t (b::pre).length g (a::((b::pre)++x::post))
  rw [rAux_at,rAux_at]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  simpa only [List.cons_append,List.append_assoc] using
    h p b (pre++q::post) (by simpa using hx)

lemma unswappedRow_BCoordinates {n i : ℕ} (ts : List TileWeights)
    (hi : i+ts.length≤n) {f g : DiluteState} (h : BCoordinates n f g) :
    BCoordinates n (unswappedRow i ts f) (unswappedRow (i+1) ts g) := by
  induction ts generalizing i f g with
  | nil => exact h
  | cons t ts ih =>
    exact ih (by simp at hi; omega) (rAux_BCoordinates (by simp at hi; omega) t h)

lemma planarRow_under (i : ℕ) (ts : List TileWeights) (f : DiluteState)
    (a : Spin) (xs : List Spin) :
    planarRow (i+1) ts f (a::xs) = planarRow i ts (fun ys => f (a::ys)) xs := by
  induction ts generalizing i f with
  | nil => rfl
  | cons t ts ih =>
    simpa only [planarRow,act] using ih (i+1) (act t (i+1) f)

lemma planarRow_BCoordinates (ts : List TileWeights) {n : ℕ} (hn : ts.length=n)
    (f : DiluteState) :
    BCoordinates n (planarRow 1 ts f) (behind (unswappedRow 0 ts) f) := by
  intro a b xs hx
  rw [planarRow_under 0]
  change planarRow 0 ts (moveAux 0 (fun ys => f (a::ys))) (xs++[b]) = _
  rw [planarRow_eq]
  simp only [Nat.zero_add]
  rw [hn,←hx,moveAux_at]
  simp [behind]

/-- Source U_A U_B in its original, unswapped spin labels A,B,sites. -/
noncomputable def sourceTwoRows (tsA tsB : List TileWeights) (f : DiluteState) : DiluteState :=
  unswappedRow 1 tsA (behind (unswappedRow 0 tsB) f)

lemma two_rows_eq {n : ℕ} (tsA tsB : List TileWeights)
    (hA : tsA.length=n) (hB : tsB.length=n) (f : DiluteState)
    (xs : List Spin) (hx : xs.length=n) (a b : Spin) :
    planarRow 0 tsA (planarRow 1 tsB f) (xs++[a,b]) =
      sourceTwoRows tsA tsB f (a::b::xs) := by
  change planarRow 0 tsA (moveAux 0 (planarRow 1 tsB f)) (xs++[a,b]) = _
  rw [planarRow_eq]
  simp only [Nat.zero_add]
  rw [hA,←hx,moveAux_at]
  exact unswappedRow_BCoordinates tsA (by omega)
    (planarRow_BCoordinates tsB hB f) a b xs hx

end CriticalHoneycomb.Transfer.PlanarNormalization

end OAI
