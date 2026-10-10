import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import OAI.Computability.BinPacking.Packing.FractionWidth
import OAI.Computability.BinPacking.Packing.PrimaryLoss

namespace OAI

noncomputable section

namespace BinPackingGap

section

open scoped BigOperators

inductive Role
  | x
  | anchor
  | «global»
  | «local»
  | flag
  deriving DecidableEq

instance : Fintype Role where
  elems := {.x, .anchor, .«global», .«local», .flag}
  complete := by intro r; cases r <;> simp

inductive Subclass
  | tp
  | tm
  | s
  | z
  | y
  | up
  | um
  | w
  | dm
  | dg
  | ft
  | fm
  | fg
  deriving DecidableEq

instance : Fintype Subclass where
  elems := {.tp, .tm, .s, .z, .y, .up, .um, .w, .dm, .dg, .ft, .fm, .fg}
  complete := by intro subclass; cases subclass <;> simp

inductive Pattern
  | plusTree
  | minusTree
  | mainJob
  | edgeJob
  deriving DecidableEq

instance : Fintype Pattern where
  elems := {.plusTree, .minusTree, .mainJob, .edgeJob}
  complete := by intro p; cases p <;> simp

namespace Role

def index : Role → Fin 5
  | .x => 0
  | .anchor => 1
  | .«global» => 2
  | .«local» => 3
  | .flag => 4

theorem index_injective : Function.Injective index := by
  intro r s
  cases r <;> cases s <;> decide

theorem sum_univ {A : Type*} [AddCommMonoid A] (f : Role → A) :
    (∑ r, f r) = f .x + f .anchor + f .«global» + f .«local» + f .flag := by
  have h : (Finset.univ : Finset Role) =
      {.x, .anchor, .«global», .«local», .flag} := by decide
  rw [h]
  simp [add_assoc]

end Role

def Subclass.role : Subclass → Role
  | .tp | .tm | .s => .x
  | .z | .y => .anchor
  | .up | .um | .w => .«global»
  | .dm | .dg => .«local»
  | .ft | .fm | .fg => .flag

@[simp] theorem role_eq_x_iff (c : Subclass) :
    c.role = Role.x ↔ c = .tp ∨ c = .tm ∨ c = .s := by
  cases c <;> simp [Subclass.role]

@[simp] theorem role_eq_anchor_iff (c : Subclass) :
    c.role = Role.anchor ↔ c = .z ∨ c = .y := by
  cases c <;> simp [Subclass.role]

@[simp] theorem role_eq_global_iff (c : Subclass) :
    c.role = Role.«global» ↔ c = .up ∨ c = .um ∨ c = .w := by
  cases c <;> simp [Subclass.role]

@[simp] theorem role_eq_local_iff (c : Subclass) :
    c.role = Role.«local» ↔ c = .dm ∨ c = .dg := by
  cases c <;> simp [Subclass.role]

@[simp] theorem role_eq_flag_iff (c : Subclass) :
    c.role = Role.flag ↔ c = .ft ∨ c = .fm ∨ c = .fg := by
  cases c <;> simp [Subclass.role]

def patternSubclass : Pattern → Role → Subclass
  | .plusTree, .x => .tp
  | .plusTree, .anchor => .z
  | .plusTree, .«global» => .up
  | .plusTree, .«local» => .dm
  | .plusTree, .flag => .ft
  | .minusTree, .x => .tm
  | .minusTree, .anchor => .z
  | .minusTree, .«global» => .um
  | .minusTree, .«local» => .dm
  | .minusTree, .flag => .ft
  | .mainJob, .x => .s
  | .mainJob, .anchor => .z
  | .mainJob, .«global» => .up
  | .mainJob, .«local» => .dm
  | .mainJob, .flag => .fm
  | .edgeJob, .x => .s
  | .edgeJob, .anchor => .y
  | .edgeJob, .«global» => .w
  | .edgeJob, .«local» => .dg
  | .edgeJob, .flag => .fg

@[simp] theorem patternSubclass_role (p : Pattern) (r : Role) :
    (patternSubclass p r).role = r := by
  cases p <;> cases r <;> rfl

theorem patternSubclass_injective (p : Pattern) :
    Function.Injective (patternSubclass p) := by
  intro r s h
  simpa only [patternSubclass_role] using congrArg Subclass.role h

theorem patternSubclass_function_injective : Function.Injective patternSubclass := by
  intro p q hpq
  have hx := congrFun hpq Role.x
  have hf := congrFun hpq Role.flag
  cases p <;> cases q <;> simp_all [patternSubclass]

@[simp] theorem card_role : Fintype.card Role = 5 := by decide

@[simp] theorem card_subclass : Fintype.card Subclass = 13 := by decide

@[simp] theorem card_pattern : Fintype.card Pattern = 4 := by decide

def IsPatternTuple (t : Fin 5 → Subclass) : Prop :=
  ∃ p : Pattern, ∃ e : Fin 5 ≃ Role, ∀ i, t i = patternSubclass p (e i)

theorem existsUnique_role_of_pattern {t : Fin 5 → Subclass}
    (ht : IsPatternTuple t) (r : Role) : ∃! i : Fin 5, (t i).role = r := by
  obtain ⟨p, e, he⟩ := ht
  refine ⟨e.symm r, ?_, ?_⟩
  · change (t (e.symm r)).role = r
    rw [he, patternSubclass_role, e.apply_symm_apply]
  · intro i hi
    apply e.injective
    simpa only [he, patternSubclass_role, e.apply_symm_apply] using hi

theorem pattern_eq_of_tuple {t : Fin 5 → Subclass} {p q : Pattern}
    {e f : Fin 5 ≃ Role}
    (hp : ∀ i, t i = patternSubclass p (e i))
    (hq : ∀ i, t i = patternSubclass q (f i)) : p = q := by
  have hef : e = f := by
    apply Equiv.ext
    intro i
    simpa only [patternSubclass_role] using
      congrArg Subclass.role ((hp i).symm.trans (hq i))
  apply patternSubclass_function_injective
  funext r
  simpa only [← hef, e.apply_symm_apply] using
    (hp (e.symm r)).symm.trans (hq (e.symm r))

end

section

def labelWeight {n : ℕ} (v : Fin n) : ℤ := 3 ^ (v.val + 1)

def labelSecondary {n : ℕ} (x d a : Fin n) : ℤ :=
  labelWeight x + labelWeight d - 2 * labelWeight a

theorem labelWeight_pos {n : ℕ} (v : Fin n) : 0 < labelWeight v := by
  exact pow_pos (by norm_num : (0 : ℤ) < 3) _

theorem labelWeight_le {n : ℕ} (v : Fin n) : labelWeight v ≤ (3 : ℤ) ^ n := by
  unfold labelWeight
  exact pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 3)
    (Nat.succ_le_of_lt v.isLt)

theorem labelWeight_strictMono {n : ℕ} : StrictMono (@labelWeight n) := by
  intro x y hxy
  change (3 : ℤ) ^ (x.val + 1) < (3 : ℤ) ^ (y.val + 1)
  exact pow_lt_pow_right₀ (by norm_num : (1 : ℤ) < 3)
    (Nat.add_lt_add_right hxy 1)

theorem labelWeight_mono {n : ℕ} {x a : Fin n} (h : x ≤ a) :
    labelWeight x ≤ labelWeight a :=
  labelWeight_strictMono.monotone h

theorem labelWeight_gap {n : ℕ} {a x : Fin n} (h : a < x) :
    3 * labelWeight a ≤ labelWeight x := by
  have hax : a.val + 1 ≤ x.val := Nat.succ_le_of_lt h
  have hpow : (3 : ℤ) ^ ((a.val + 1) + 1) ≤ (3 : ℤ) ^ (x.val + 1) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 3)
      (Nat.add_le_add_right hax 1)
  calc
    3 * labelWeight a = (3 : ℤ) ^ ((a.val + 1) + 1) := by
      change (3 : ℤ) * (3 : ℤ) ^ (a.val + 1) = _
      rw [pow_succ (3 : ℤ) (a.val + 1), mul_comm]
    _ ≤ labelWeight x := hpow

theorem labelSecondary_nonpos_bounds {n : ℕ} {x d a : Fin n}
    (hq : labelSecondary x d a ≤ 0) : x ≤ a ∧ d ≤ a := by
  have ha := labelWeight_pos a
  have hx := labelWeight_pos x
  have hd := labelWeight_pos d
  change labelWeight x + labelWeight d - 2 * labelWeight a ≤ 0 at hq
  constructor
  · by_contra hxa
    have hgap := labelWeight_gap (lt_of_not_ge hxa)
    linarith
  · by_contra hda
    have hgap := labelWeight_gap (lt_of_not_ge hda)
    linarith

theorem labelSecondary_nonpos_iff {n : ℕ} {x d a : Fin n} :
    labelSecondary x d a ≤ 0 ↔ x ≤ a ∧ d ≤ a := by
  constructor
  · exact labelSecondary_nonpos_bounds
  · rintro ⟨hx, hd⟩
    have hqx := labelWeight_mono hx
    have hqd := labelWeight_mono hd
    unfold labelSecondary
    linarith

@[simp] theorem labelSecondary_self {n : ℕ} (a : Fin n) :
    labelSecondary a a a = 0 := by
  unfold labelSecondary
  linarith

theorem labelSecondary_eq_zero_iff {n : ℕ} {x d a : Fin n} :
    labelSecondary x d a = 0 ↔ x = a ∧ d = a := by
  constructor
  · intro hq
    obtain ⟨hx, hd⟩ := labelSecondary_nonpos_bounds (le_of_eq hq)
    have hqx := labelWeight_mono hx
    have hqd := labelWeight_mono hd
    change labelWeight x + labelWeight d - 2 * labelWeight a = 0 at hq
    constructor
    · rcases lt_or_eq_of_le hx with hxa | hxa
      · have hlt := labelWeight_strictMono hxa
        linarith
      · exact hxa
    · rcases lt_or_eq_of_le hd with hda | hda
      · have hlt := labelWeight_strictMono hda
        linarith
      · exact hda
  · rintro ⟨rfl, rfl⟩
    exact labelSecondary_self _

open scoped BigOperators

def subclassIndicator (a b : Subclass) : ℤ := if a = b then 1 else 0

def primaryCoeff (j : Fin 10) (subclass : Subclass) : ℤ :=
  match j.val with
  | 0 => 5 * (if subclass.role = .x then 1 else 0) - 1
  | 1 => 5 * (if subclass.role = .anchor then 1 else 0) - 1
  | 2 => 5 * (if subclass.role = .«global» then 1 else 0) - 1
  | 3 => 5 * (if subclass.role = .«local» then 1 else 0) - 1
  | 4 => 5 * (if subclass.role = .flag then 1 else 0) - 1
  | 5 => subclassIndicator subclass .tp + subclassIndicator subclass .tm - subclassIndicator subclass .ft
  | 6 => subclassIndicator subclass .z - subclassIndicator subclass .ft - subclassIndicator subclass .fm
  | 7 => subclassIndicator subclass .up + subclassIndicator subclass .um -
      subclassIndicator subclass .ft - subclassIndicator subclass .fm
  | 8 => subclassIndicator subclass .dm - subclassIndicator subclass .ft - subclassIndicator subclass .fm
  | 9 => subclassIndicator subclass .tm - subclassIndicator subclass .um
  | _ => 0

def primaryScore (subclass : Subclass) : ℤ :=
  ∑ j : Fin 10, (100 : ℤ) ^ j.val * primaryCoeff j subclass

def primaryBound : ℕ := 100 ^ 11

def roleCoeffIndex (r : Role) : Fin 10 :=
  ⟨r.index.val, lt_trans r.index.isLt (by decide)⟩

theorem primaryCoeff_role (r : Role) (subclass : Subclass) :
    primaryCoeff (roleCoeffIndex r) subclass = 5 * (if subclass.role = r then 1 else 0) - 1 := by
  cases r <;> cases subclass <;> decide

theorem primaryCoeff_abs_le (j : Fin 10) (subclass : Subclass) :
    |primaryCoeff j subclass| ≤ 4 := by
  fin_cases j <;> cases subclass <;> decide

theorem primaryScore_abs_lt (subclass : Subclass) :
    |primaryScore subclass| < (primaryBound : ℤ) := by
  cases subclass <;>
    norm_num [primaryScore, primaryCoeff, subclassIndicator, Subclass.role,
      primaryBound, Fin.sum_univ_succ]

theorem sum_primaryScore_eq {I : Type*} [Fintype I] (t : I → Subclass) :
    (∑ i, primaryScore (t i)) =
      ∑ j : Fin 10, (100 : ℤ) ^ j.val * (∑ i, primaryCoeff j (t i)) := by
  simp only [primaryScore, Finset.mul_sum]
  exact Finset.sum_comm

def roleCount {I : Type*} [Fintype I] (t : I → Subclass) (r : Role) : ℤ :=
  ∑ i, if (t i).role = r then 1 else 0

def subclassCount {I : Type*} [Fintype I] (t : I → Subclass) (subclass : Subclass) : ℤ :=
  ∑ i, subclassIndicator (t i) subclass

theorem sum_primaryCoeff_role {I : Type*} [Fintype I]
    (t : I → Subclass) (r : Role) :
    (∑ i, primaryCoeff (roleCoeffIndex r) (t i)) =
      5 * roleCount t r - (Fintype.card I : ℤ) := by
  simp only [primaryCoeff_role, Finset.sum_sub_distrib, ← Finset.mul_sum,
    roleCount, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

theorem sum_primaryCoeff_five {I : Type*} [Fintype I] (t : I → Subclass) :
    (∑ i, primaryCoeff 5 (t i)) =
      subclassCount t .tp + subclassCount t .tm - subclassCount t .ft := by
  simp [primaryCoeff, subclassCount, Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem sum_primaryCoeff_six {I : Type*} [Fintype I] (t : I → Subclass) :
    (∑ i, primaryCoeff 6 (t i)) =
      subclassCount t .z - subclassCount t .ft - subclassCount t .fm := by
  simp [primaryCoeff, subclassCount, Finset.sum_sub_distrib]

theorem sum_primaryCoeff_seven {I : Type*} [Fintype I] (t : I → Subclass) :
    (∑ i, primaryCoeff 7 (t i)) =
      subclassCount t .up + subclassCount t .um -
        subclassCount t .ft - subclassCount t .fm := by
  simp [primaryCoeff, subclassCount, Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem sum_primaryCoeff_eight {I : Type*} [Fintype I] (t : I → Subclass) :
    (∑ i, primaryCoeff 8 (t i)) =
      subclassCount t .dm - subclassCount t .ft - subclassCount t .fm := by
  simp [primaryCoeff, subclassCount, Finset.sum_sub_distrib]

theorem sum_primaryCoeff_nine {I : Type*} [Fintype I] (t : I → Subclass) :
    (∑ i, primaryCoeff 9 (t i)) = subclassCount t .tm - subclassCount t .um := by
  simp [primaryCoeff, subclassCount, Finset.sum_sub_distrib]

theorem radix100_eq_zero_iff {n : ℕ} (a : Fin n → ℤ)
    (ha : ∀ i, |a i| < 100) :
    (∑ i, (100 : ℤ) ^ i.val * a i) = 0 ↔ ∀ i, a i = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      constructor
      · intro hs
        have hsplit : a 0 + 100 * (∑ i : Fin n, (100 : ℤ) ^ i.val * a i.succ) = 0 := by
          calc
            a 0 + 100 * (∑ i : Fin n, (100 : ℤ) ^ i.val * a i.succ) =
                ∑ i : Fin (n + 1), (100 : ℤ) ^ i.val * a i := by
              rw [Fin.sum_univ_succ]
              simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ]
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              rw [pow_succ]
              ring
            _ = 0 := hs
        have hfirst := abs_lt.mp (ha 0)
        have hz : a 0 = 0 := by omega
        have htail : (∑ i : Fin n, (100 : ℤ) ^ i.val * a i.succ) = 0 := by omega
        have hrest := (ih (fun i => a i.succ) (fun i => ha i.succ)).mp htail
        intro i
        exact Fin.cases hz (fun k => hrest k) i
      · intro hz
        simp [hz]

theorem primaryCoeff_total_abs_lt (t : Fin 5 → Subclass) (j : Fin 10) :
    |∑ i, primaryCoeff j (t i)| < 100 := by
  calc
    |∑ i, primaryCoeff j (t i)| ≤ ∑ i, |primaryCoeff j (t i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 5, (4 : ℤ) :=
      Finset.sum_le_sum (fun i _ => primaryCoeff_abs_le j (t i))
    _ < 100 := by norm_num

theorem sum_primaryScore_eq_zero_iff_coefficients (t : Fin 5 → Subclass) :
    (∑ i, primaryScore (t i)) = 0 ↔ ∀ j : Fin 10, (∑ i, primaryCoeff j (t i)) = 0 := by
  rw [sum_primaryScore_eq]
  exact radix100_eq_zero_iff _ (primaryCoeff_total_abs_lt t)

theorem pattern_primaryCoeff_sum (p : Pattern) (j : Fin 10) :
    (∑ r : Role, primaryCoeff j (patternSubclass p r)) = 0 := by
  cases p <;> fin_cases j <;>
    norm_num [Role.sum_univ, patternSubclass, primaryCoeff, subclassIndicator,
      Subclass.role]

private theorem sum_role_subclassIndicator (v : Role → Subclass)
    (hrole : ∀ r, (v r).role = r) (c : Subclass) :
    (∑ r : Role, subclassIndicator (v r) c) = subclassIndicator (v c.role) c := by
  classical
  apply Finset.sum_eq_single c.role
  · intro r _ hr
    have hne : v r ≠ c := by
      intro he
      exact hr ((hrole r).symm.trans (congrArg Subclass.role he))
    simp [subclassIndicator, hne]
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem roleTuple_eq_pattern (v : Role → Subclass)
    (hrole : ∀ r, (v r).role = r)
    (hcoeff : ∀ j : Fin 10, (∑ r, primaryCoeff j (v r)) = 0) :
    ∃ p : Pattern, ∀ r, v r = patternSubclass p r := by
  have hx := (role_eq_x_iff _).mp (hrole .x)
  have ha := (role_eq_anchor_iff _).mp (hrole .anchor)
  have hu := (role_eq_global_iff _).mp (hrole .«global»)
  have hd := (role_eq_local_iff _).mp (hrole .«local»)
  have hf := (role_eq_flag_iff _).mp (hrole .flag)
  have h5 := hcoeff 5
  have h6 := hcoeff 6
  have h7 := hcoeff 7
  have h8 := hcoeff 8
  have h9 := hcoeff 9
  rw [sum_primaryCoeff_five] at h5
  rw [sum_primaryCoeff_six] at h6
  rw [sum_primaryCoeff_seven] at h7
  rw [sum_primaryCoeff_eight] at h8
  rw [sum_primaryCoeff_nine] at h9
  simp only [subclassCount, sum_role_subclassIndicator v hrole, Subclass.role]
    at h5 h6 h7 h8 h9
  rcases hf with hf | hf | hf
  all_goals
    rcases ha with ha | ha <;> rcases hd with hd | hd
  all_goals
    simp +decide [subclassIndicator, ha, hd, hf] at h6 h8
  all_goals
    rcases hx with hx | hx | hx <;> rcases hu with hu | hu | hu
  all_goals
    simp +decide [subclassIndicator, hx, hu, hf] at h5 h7 h9
  · refine ⟨.plusTree, ?_⟩
    intro r
    cases r <;> simp [patternSubclass, hx, ha, hu, hd, hf]
  · refine ⟨.minusTree, ?_⟩
    intro r
    cases r <;> simp [patternSubclass, hx, ha, hu, hd, hf]
  · refine ⟨.mainJob, ?_⟩
    intro r
    cases r <;> simp [patternSubclass, hx, ha, hu, hd, hf]
  · refine ⟨.edgeJob, ?_⟩
    intro r
    cases r <;> simp [patternSubclass, hx, ha, hu, hd, hf]

theorem sum_primaryScore_eq_zero_iff_pattern (t : Fin 5 → Subclass) :
    (∑ i, primaryScore (t i)) = 0 ↔ IsPatternTuple t := by
  classical
  rw [sum_primaryScore_eq_zero_iff_coefficients]
  constructor
  · intro hc
    have hcount (r : Role) : roleCount t r = 1 := by
      have h := hc (roleCoeffIndex r)
      rw [sum_primaryCoeff_role] at h
      norm_num at h
      omega
    have hsurj : Function.Surjective (fun i : Fin 5 => (t i).role) := by
      intro r
      by_contra hno
      have hne : ∀ i : Fin 5, (t i).role ≠ r := fun i hi => hno ⟨i, hi⟩
      have hh := hcount r
      simp [roleCount, hne] at hh
    let e₀ : Fin 5 ≃ Role := Fintype.equivOfCardEq (by simp)
    have hinj : Function.Injective (fun i : Fin 5 => (t i).role) :=
      (Finite.injective_iff_surjective_of_equiv e₀).mpr hsurj
    let e : Fin 5 ≃ Role := Equiv.ofBijective _ ⟨hinj, hsurj⟩
    let v : Role → Subclass := fun r => t (e.symm r)
    have hvrole (r : Role) : (v r).role = r := by
      change e (e.symm r) = r
      exact e.apply_symm_apply r
    have hvcoeff (j : Fin 10) : (∑ r : Role, primaryCoeff j (v r)) = 0 := by
      calc
        (∑ r : Role, primaryCoeff j (v r)) =
            ∑ i : Fin 5, primaryCoeff j (v (e i)) := (e.sum_comp _).symm
        _ = 0 := by simpa [v] using hc j
    obtain ⟨p, hp⟩ := roleTuple_eq_pattern v hvrole hvcoeff
    refine ⟨p, e, ?_⟩
    intro i
    simpa [v] using hp (e i)
  · rintro ⟨p, e, he⟩ j
    calc
      (∑ i, primaryCoeff j (t i)) =
          ∑ i : Fin 5, primaryCoeff j (patternSubclass p (e i)) := by simp only [he]
      _ = ∑ r : Role, primaryCoeff j (patternSubclass p r) :=
        e.sum_comp (fun r : Role => primaryCoeff j (patternSubclass p r))
      _ = 0 := pattern_primaryCoeff_sum p j

theorem sum_primaryScore_eq_zero_of_coefficients {I : Type*} [Fintype I]
    (t : I → Subclass) (h : ∀ j : Fin 10, (∑ i, primaryCoeff j (t i)) = 0) :
    (∑ i, primaryScore (t i)) = 0 := by
  rw [sum_primaryScore_eq]
  simp [h]

end

section

def secondaryScore {n : ℕ} (subclass : Subclass) (label : Option (Fin n)) : ℤ :=
  let q := label.elim 0 labelWeight
  match subclass.role with
  | .x => q
  | .anchor => -2 * q
  | .«global» => 0
  | .«local» => q
  | .flag => 0

@[simp] theorem secondaryScore_none {n : ℕ} (subclass : Subclass) :
    secondaryScore subclass (none : Option (Fin n)) = 0 := by
  cases hs : subclass.role <;> simp [secondaryScore, hs]

def tableRoleLabel {n : ℕ} (x d a : Fin n) : Role → Option (Fin n)
  | .x => some x
  | .anchor => some a
  | .«global» => none
  | .«local» => some d
  | .flag => none

def gamma : ℚ := 1 / (1000 * (primaryBound : ℚ))

def mu (n : ℕ) : ℚ := gamma / (1000 * (3 : ℚ) ^ n)

def nu (n : ℕ) : ℚ := mu n / 1000

def encodedSize {n : ℕ} (subclass : Subclass) (label : Option (Fin n)) (w : ℚ) : ℚ :=
  1 / 5 + gamma * (primaryScore subclass : ℚ) +
    mu n * (secondaryScore subclass label : ℚ) + nu n * w

theorem gamma_pos : 0 < gamma := by
  norm_num [gamma, primaryBound]

theorem gamma_le_one : gamma ≤ 1 := by
  norm_num [gamma, primaryBound]

theorem gamma_mul_primaryBound : gamma * (primaryBound : ℚ) = 1 / 1000 := by
  norm_num [gamma, primaryBound]

theorem mu_pos (n : ℕ) : 0 < mu n := by
  exact div_pos gamma_pos (mul_pos (by norm_num) (pow_pos (by norm_num) n))

theorem nu_pos (n : ℕ) : 0 < nu n := div_pos (mu_pos n) (by norm_num)

theorem mu_mul_labelBound (n : ℕ) : mu n * (3 : ℚ) ^ n = gamma / 1000 := by
  unfold mu
  have hn : (3 : ℚ) ^ n ≠ 0 := pow_ne_zero n (by norm_num)
  field_simp [hn]

theorem mu_le_gamma_div (n : ℕ) : mu n ≤ gamma / 1000 := by
  have hn : (1 : ℚ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  have h := mul_le_mul_of_nonneg_left hn (mu_pos n).le
  rw [mul_one, mu_mul_labelBound] at h
  exact h

theorem nu_le_gamma_div (n : ℕ) : nu n ≤ gamma / 1000000 := by
  have h := div_le_div_of_nonneg_right (mu_le_gamma_div n) (by norm_num : (0 : ℚ) ≤ 1000)
  simpa only [nu, div_div, show (1000 : ℚ) * 1000 = 1000000 by norm_num] using h

theorem secondaryScore_abs_le {n : ℕ} (subclass : Subclass) (label : Option (Fin n)) :
    |secondaryScore subclass label| ≤ 2 * (3 : ℤ) ^ n := by
  cases label with
  | none =>
      cases hs : subclass.role <;> simp [secondaryScore, hs]
  | some v =>
      have hv0 := labelWeight_pos v
      have hv := labelWeight_le v
      cases hs : subclass.role <;>
        norm_num [secondaryScore, hs, abs_mul, abs_of_pos hv0] <;> linarith

theorem secondaryScore_rat_abs_le {n : ℕ} (subclass : Subclass) (label : Option (Fin n)) :
    |(secondaryScore subclass label : ℚ)| ≤ 2 * (3 : ℚ) ^ n := by
  exact_mod_cast secondaryScore_abs_le subclass label

theorem primaryScore_rat_abs_le (subclass : Subclass) :
    |(primaryScore subclass : ℚ)| ≤ (primaryBound : ℚ) := by
  exact_mod_cast (primaryScore_abs_lt subclass).le

private theorem perturbation_triangle (g m v p q w : ℚ)
    (hg : 0 ≤ g) (hm : 0 ≤ m) (hv : 0 ≤ v) :
    |(1 / 5 + g * p + m * q + v * w) - 1 / 5| ≤
      g * |p| + m * |q| + v * |w| := by
  have heq : (1 / 5 + g * p + m * q + v * w) - 1 / 5 =
      g * p + m * q + v * w := by ring
  rw [heq]
  have hp : |g * p| = g * |p| := by rw [abs_mul, abs_of_nonneg hg]
  have hq : |m * q| = m * |q| := by rw [abs_mul, abs_of_nonneg hm]
  have hw : |v * w| = v * |w| := by rw [abs_mul, abs_of_nonneg hv]
  have hfirst : |g * p + m * q| ≤ |g * p| + |m * q| :=
    abs_add_le (g * p) (m * q)
  have hsecond : |g * p + m * q + v * w| ≤ |g * p + m * q| + |v * w| :=
    abs_add_le (g * p + m * q) (v * w)
  rw [hp, hq] at hfirst
  rw [hw] at hsecond
  linarith only [hfirst, hsecond]

private theorem perturbation_small (g m v p q w : ℚ)
    (hg : 0 ≤ g) (hm : 0 ≤ m) (hv : 0 ≤ v) (hg1 : g ≤ 1)
    (hp : g * |p| ≤ 1 / 1000) (hq : m * |q| ≤ 2 * g / 1000)
    (hw : v * |w| ≤ v * 6) (hnu : v ≤ g / 1000000) :
    |(1 / 5 + g * p + m * q + v * w) - 1 / 5| ≤ 1 / 100 := by
  have hsum := perturbation_triangle g m v p q w hg hm hv
  nlinarith only [hsum, hg1, hp, hq, hw, hnu]

theorem encodedSize_perturbation_bound {n : ℕ} (subclass : Subclass)
    (label : Option (Fin n)) (w : ℚ) (hw : |w| ≤ 6) :
    |encodedSize subclass label w - 1 / 5| ≤ 1 / 100 := by
  have hp := mul_le_mul_of_nonneg_left (primaryScore_rat_abs_le subclass) gamma_pos.le
  rw [gamma_mul_primaryBound] at hp
  have hq := mul_le_mul_of_nonneg_left (secondaryScore_rat_abs_le subclass label) (mu_pos n).le
  have hq' : mu n * |(secondaryScore subclass label : ℚ)| ≤ 2 * gamma / 1000 := by
    calc
      _ ≤ mu n * (2 * (3 : ℚ) ^ n) := hq
      _ = 2 * gamma / 1000 := by
        rw [← mul_assoc, mul_comm (mu n) 2, mul_assoc, mu_mul_labelBound]
        ring
  have hw' := mul_le_mul_of_nonneg_left hw (nu_pos n).le
  exact perturbation_small gamma (mu n) (nu n) (primaryScore subclass)
    (secondaryScore subclass label) w gamma_pos.le (mu_pos n).le (nu_pos n).le
    gamma_le_one hp hq' hw' (nu_le_gamma_div n)

theorem encodedSize_mem_interval {n : ℕ} (subclass : Subclass)
    (label : Option (Fin n)) (w : ℚ) (hw : |w| ≤ 6) :
    1 / 6 < encodedSize subclass label w ∧ encodedSize subclass label w < 1 := by
  have hb := abs_le.mp (encodedSize_perturbation_bound subclass label w hw)
  constructor <;> linarith

theorem primary_tail_lt (n : ℕ) :
    mu n * (10 * (3 : ℚ) ^ n) + nu n * 30 < gamma := by
  have heq : mu n * (10 * (3 : ℚ) ^ n) = 10 * gamma / 1000 := by
    rw [← mul_assoc, mul_comm (mu n) 10, mul_assoc, mu_mul_labelBound]
    ring
  rw [heq]
  have hn := nu_le_gamma_div n
  have hg := gamma_pos
  nlinarith

theorem secondary_tail_lt (n : ℕ) : nu n * 30 < mu n := by
  have hμ := mu_pos n
  unfold nu
  nlinarith

open scoped BigOperators

namespace Packing

variable {I : Instance} {b : ℕ}

def primaryTotal (p : Packing I b) (subclass : I.Item → Subclass) (j : Fin b) : ℤ :=
  ∑ i ∈ p.binItems j, primaryScore (subclass i)

def IsTableBin (p : Packing I b) (subclass : I.Item → Subclass) (j : Fin b) : Prop :=
  (p.binItems j).card = 5 ∧ p.primaryTotal subclass j = 0

abbrev TableBin (p : Packing I b) (subclass : I.Item → Subclass) :=
  {j : Fin b // p.IsTableBin subclass j}

instance (p : Packing I b) (subclass : I.Item → Subclass) :
    Fintype (p.TableBin subclass) := Fintype.ofFinite _

instance (p : Packing I b) (subclass : I.Item → Subclass) :
    DecidableEq (p.TableBin subclass) := Classical.decEq _

theorem table_pattern (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) :
    ∃ pat : Pattern, ∃ e : Role ≃ p.binItems t.val,
      ∀ r, subclass (e r).val = patternSubclass pat r := by
  classical
  let e : Fin 5 ≃ p.binItems t.val :=
    (Finset.equivFinOfCardEq t.property.1).symm
  have hz : (∑ i : Fin 5, primaryScore (subclass (e i).val)) = 0 := by
    rw [e.sum_comp (fun i : p.binItems t.val => primaryScore (subclass i.val))]
    change (∑ i ∈ (p.binItems t.val).attach, primaryScore (subclass i.val)) = 0
    rw [Finset.sum_attach (p.binItems t.val) (fun i => primaryScore (subclass i))]
    exact t.property.2
  obtain ⟨pat, perm, hp⟩ :=
    (sum_primaryScore_eq_zero_iff_pattern (fun i => subclass (e i).val)).mp hz
  refine ⟨pat, perm.symm.trans e, ?_⟩
  intro r
  simpa using hp (perm.symm r)

def tablePattern (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) : Pattern :=
  Classical.choose (p.table_pattern subclass t)

def tableEquiv (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) : Role ≃ p.binItems t.val :=
  Classical.choose (Classical.choose_spec (p.table_pattern subclass t))

theorem tableEquiv_subclass (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) (r : Role) :
    subclass (p.tableEquiv subclass t r).val =
      patternSubclass (p.tablePattern subclass t) r :=
  Classical.choose_spec (Classical.choose_spec (p.table_pattern subclass t)) r

def itemAtRole (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) (r : Role) : I.Item :=
  (p.tableEquiv subclass t r).val

theorem itemAtRole_mem (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) (r : Role) :
    p.itemAtRole subclass t r ∈ p.binItems t.val :=
  (p.tableEquiv subclass t r).property

theorem itemAtRole_subclass (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) (r : Role) :
    subclass (p.itemAtRole subclass t r) =
      patternSubclass (p.tablePattern subclass t) r :=
  p.tableEquiv_subclass subclass t r

@[simp] theorem itemAtRole_role (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) (r : Role) :
    (subclass (p.itemAtRole subclass t r)).role = r := by
  rw [p.itemAtRole_subclass subclass t r, patternSubclass_role]

theorem itemAtRole_injective (p : Packing I b) (subclass : I.Item → Subclass)
    (r : Role) : Function.Injective (fun t => p.itemAtRole subclass t r) :=
  p.chosen_injective Subtype.val Subtype.val_injective
    (fun t => p.itemAtRole subclass t r) (fun t => p.itemAtRole_mem subclass t r)

theorem itemAtRole_joint_injective (p : Packing I b) (subclass : I.Item → Subclass) :
    Function.Injective (fun tr : p.TableBin subclass × Role =>
      p.itemAtRole subclass tr.1 tr.2) := by
  intro x y h
  have hr : x.2 = y.2 := by
    have := congrArg (fun i => (subclass i).role) h
    simpa only [itemAtRole_role] using this
  have ht : x.1 = y.1 := by
    apply p.itemAtRole_injective subclass x.2
    simpa only [hr] using h
  exact Prod.ext ht hr

theorem mem_table_bin_iff (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) (i : I.Item) :
    i ∈ p.binItems t.val ↔ ∃ r, p.itemAtRole subclass t r = i := by
  constructor
  · intro hi
    refine ⟨(p.tableEquiv subclass t).symm ⟨i, hi⟩, ?_⟩
    simp [itemAtRole]
  · rintro ⟨r, rfl⟩
    exact p.itemAtRole_mem subclass t r

theorem itemAtRole_eq_of_mem (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) (r : Role) (i : I.Item)
    (hi : i ∈ p.binItems t.val) (hr : (subclass i).role = r) :
    p.itemAtRole subclass t r = i := by
  obtain ⟨s, hs⟩ := (p.mem_table_bin_iff subclass t i).mp hi
  have hsr : s = r := by
    rw [← hs, p.itemAtRole_role] at hr
    exact hr
  simpa only [hsr] using hs

def IsGoodTableBin (p : Packing I b) (subclass : I.Item → Subclass)
    {n : ℕ} (label : I.Item → Option (Fin n)) (t : p.TableBin subclass) : Prop :=
  label (p.itemAtRole subclass t .x) = label (p.itemAtRole subclass t .anchor) ∧
    label (p.itemAtRole subclass t .«local») =
      label (p.itemAtRole subclass t .anchor)

abbrev GoodTableBin (p : Packing I b) (subclass : I.Item → Subclass)
    {n : ℕ} (label : I.Item → Option (Fin n)) :=
  {t : p.TableBin subclass // p.IsGoodTableBin subclass label t}

instance (p : Packing I b) (subclass : I.Item → Subclass)
    {n : ℕ} (label : I.Item → Option (Fin n)) :
    Fintype (p.GoodTableBin subclass label) := Fintype.ofFinite _

abbrev GoodM (p : Packing I b) (subclass : I.Item → Subclass)
    {n : ℕ} (label : I.Item → Option (Fin n)) :=
  {t : p.GoodTableBin subclass label // p.tablePattern subclass t.val ≠ .edgeJob}

abbrev GoodG (p : Packing I b) (subclass : I.Item → Subclass)
    {n : ℕ} (label : I.Item → Option (Fin n)) :=
  {t : p.GoodTableBin subclass label // p.tablePattern subclass t.val = .edgeJob}

instance (p : Packing I b) (subclass : I.Item → Subclass)
    {n : ℕ} (label : I.Item → Option (Fin n)) :
    Fintype (p.GoodM subclass label) := Fintype.ofFinite _

instance (p : Packing I b) (subclass : I.Item → Subclass)
    {n : ℕ} (label : I.Item → Option (Fin n)) :
    Fintype (p.GoodG subclass label) := Fintype.ofFinite _

end Packing

end

open scoped BigOperators

def primaryTotal (s : Fin 5 → Subclass) : ℤ := ∑ i, primaryScore (s i)

def secondaryTotal {n : ℕ} (s : Fin 5 → Subclass)
    (label : Fin 5 → Option (Fin n)) : ℤ := ∑ i, secondaryScore (s i) (label i)

def coordinateTotal (w : Fin 5 → ℚ) : ℚ := ∑ i, w i

theorem encodedSize_sum {n : ℕ} (s : Fin 5 → Subclass)
    (label : Fin 5 → Option (Fin n)) (w : Fin 5 → ℚ) :
    (∑ i, encodedSize (s i) (label i) (w i)) =
      1 + gamma * (primaryTotal s : ℚ) +
        mu n * (secondaryTotal s label : ℚ) + nu n * coordinateTotal w := by
  simp [encodedSize, primaryTotal, secondaryTotal, coordinateTotal,
    Finset.sum_add_distrib, Finset.mul_sum]

theorem secondaryTotal_rat_abs_le {n : ℕ} (s : Fin 5 → Subclass)
    (label : Fin 5 → Option (Fin n)) :
    |(secondaryTotal s label : ℚ)| ≤ 10 * (3 : ℚ) ^ n := by
  calc
    _ = |∑ i, (secondaryScore (s i) (label i) : ℚ)| := by simp [secondaryTotal]
    _ ≤ ∑ i, |(secondaryScore (s i) (label i) : ℚ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 5, 2 * (3 : ℚ) ^ n :=
      Finset.sum_le_sum (fun i _ => secondaryScore_rat_abs_le (s i) (label i))
    _ = _ := by norm_num; ring

theorem coordinateTotal_abs_le (w : Fin 5 → ℚ) (hw : ∀ i, |w i| ≤ 6) :
    |coordinateTotal w| ≤ 30 := by
  calc
    _ ≤ ∑ i, |w i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 5, (6 : ℚ) := Finset.sum_le_sum (fun i _ => hw i)
    _ = _ := by norm_num

theorem sum_primary_nonpos_of_feasible {n : ℕ} (s : Fin 5 → Subclass)
    (label : Fin 5 → Option (Fin n)) (w : Fin 5 → ℚ)
    (hw : ∀ i, |w i| ≤ 6)
    (hfeas : (∑ i, encodedSize (s i) (label i) (w i)) ≤ 1) :
    primaryTotal s ≤ 0 := by
  by_contra h
  have hp : (1 : ℤ) ≤ primaryTotal s :=
    Int.add_one_le_iff.mpr (lt_of_not_ge h)
  have hpQ : (1 : ℚ) ≤ (primaryTotal s : ℚ) := by exact_mod_cast hp
  have hp' := mul_le_mul_of_nonneg_left hpQ gamma_pos.le
  have hq := mul_le_mul_of_nonneg_left
    (abs_le.mp (secondaryTotal_rat_abs_le s label)).1 (mu_pos n).le
  have hw' := mul_le_mul_of_nonneg_left
    (abs_le.mp (coordinateTotal_abs_le w hw)).1 (nu_pos n).le
  have htail := primary_tail_lt n
  rw [encodedSize_sum] at hfeas
  nlinarith only [hfeas, hp', hq, hw', htail]

theorem sum_secondary_nonpos_of_feasible {n : ℕ} (s : Fin 5 → Subclass)
    (label : Fin 5 → Option (Fin n)) (w : Fin 5 → ℚ)
    (hw : ∀ i, |w i| ≤ 6) (hp : primaryTotal s = 0)
    (hfeas : (∑ i, encodedSize (s i) (label i) (w i)) ≤ 1) :
    secondaryTotal s label ≤ 0 := by
  by_contra h
  have hq : (1 : ℤ) ≤ secondaryTotal s label :=
    Int.add_one_le_iff.mpr (lt_of_not_ge h)
  have hqQ : (1 : ℚ) ≤ (secondaryTotal s label : ℚ) := by exact_mod_cast hq
  have hq' := mul_le_mul_of_nonneg_left hqQ (mu_pos n).le
  have hw' := mul_le_mul_of_nonneg_left
    (abs_le.mp (coordinateTotal_abs_le w hw)).1 (nu_pos n).le
  have htail := secondary_tail_lt n
  rw [encodedSize_sum, hp] at hfeas
  norm_num only [Int.cast_zero, mul_zero, add_zero] at hfeas
  nlinarith only [hfeas, hq', hw', htail]

theorem feasible_iff_coordinateSum_nonpos {n : ℕ} (s : Fin 5 → Subclass)
    (label : Fin 5 → Option (Fin n)) (w : Fin 5 → ℚ)
    (hp : primaryTotal s = 0) (hq : secondaryTotal s label = 0) :
    ((∑ i, encodedSize (s i) (label i) (w i)) ≤ 1) ↔ coordinateTotal w ≤ 0 := by
  rw [encodedSize_sum, hp, hq]
  norm_num only [Int.cast_zero, mul_zero, add_zero]
  constructor
  · intro h
    have hmul : nu n * coordinateTotal w ≤ nu n * 0 := by linarith
    exact le_of_mul_le_mul_left hmul (nu_pos n)
  · intro h
    have hmul := mul_le_mul_of_nonneg_left h (nu_pos n).le
    linarith

theorem secondaryTotal_eq_labelSecondary {n : ℕ} (s : Fin 5 → Subclass)
    (label : Fin 5 → Option (Fin n)) (e : Fin 5 ≃ Role) (x d a : Fin n)
    (hs : ∀ i, (s i).role = e i)
    (hl : ∀ i, label i = tableRoleLabel x d a (e i)) :
    secondaryTotal s label = labelSecondary x d a := by
  let f : Role → ℤ := fun r => match r with
    | .x => labelWeight x
    | .anchor => -2 * labelWeight a
    | .«global» => 0
    | .«local» => labelWeight d
    | .flag => 0
  calc
    secondaryTotal s label = ∑ i, f (e i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [secondaryScore, hs i, hl i]
      cases he : e i <;> rfl
    _ = ∑ r, f r := e.sum_comp f
    _ = labelSecondary x d a := by
      rw [Role.sum_univ]
      simp only [f, labelSecondary]
      ring

theorem secondaryTotal_nonpos_iff_labels {n : ℕ} (s : Fin 5 → Subclass)
    (label : Fin 5 → Option (Fin n)) (e : Fin 5 ≃ Role) (x d a : Fin n)
    (hs : ∀ i, (s i).role = e i)
    (hl : ∀ i, label i = tableRoleLabel x d a (e i)) :
    secondaryTotal s label ≤ 0 ↔ x ≤ a ∧ d ≤ a := by
  rw [secondaryTotal_eq_labelSecondary s label e x d a hs hl]
  exact labelSecondary_nonpos_iff

theorem secondaryTotal_eq_zero_iff_labels {n : ℕ} (s : Fin 5 → Subclass)
    (label : Fin 5 → Option (Fin n)) (e : Fin 5 ≃ Role) (x d a : Fin n)
    (hs : ∀ i, (s i).role = e i)
    (hl : ∀ i, label i = tableRoleLabel x d a (e i)) :
    secondaryTotal s label = 0 ↔ x = a ∧ d = a := by
  rw [secondaryTotal_eq_labelSecondary s label e x d a hs hl]
  exact labelSecondary_eq_zero_iff

namespace Packing

variable {I : Instance} {b n : ℕ}

def fiveEquiv (p : Packing I b) (j : Fin b) (hc : (p.binItems j).card = 5) :
    Fin 5 ≃ p.binItems j := (Finset.equivFinOfCardEq hc).symm

theorem sum_fiveEquiv (p : Packing I b) (j : Fin b) (hc : (p.binItems j).card = 5)
    {M : Type*} [AddCommMonoid M] (f : I.Item → M) :
    (∑ i : Fin 5, f (p.fiveEquiv j hc i).val) = ∑ i ∈ p.binItems j, f i := by
  rw [(p.fiveEquiv j hc).sum_comp (fun i : p.binItems j => f i.val)]
  change (∑ i ∈ (p.binItems j).attach, f i.val) = ∑ i ∈ p.binItems j, f i
  exact Finset.sum_attach (p.binItems j) f

theorem full_primary_nonpos (p : Packing I b)
    (subclass : I.Item → Subclass) (label : I.Item → Option (Fin n))
    (coordinate : I.Item → ℚ)
    (hsize : ∀ i, I.size i = encodedSize (subclass i) (label i) (coordinate i))
    (hw : ∀ i, |coordinate i| ≤ 6)
    (j : Fin b) (hc : (p.binItems j).card = 5) :
    p.primaryTotal subclass j ≤ 0 := by
  let e := p.fiveEquiv j hc
  have hcap : (∑ i : Fin 5,
      encodedSize (subclass (e i).val) (label (e i).val) (coordinate (e i).val)) ≤ 1 := by
    simp_rw [← hsize]
    rw [p.sum_fiveEquiv]
    exact p.bin_capacity j
  have hp := sum_primary_nonpos_of_feasible
    (fun i => subclass (e i).val) (fun i => label (e i).val)
    (fun i => coordinate (e i).val) (fun i => hw _) hcap
  change (∑ i : Fin 5, primaryScore (subclass (p.fiveEquiv j hc i).val)) ≤ 0 at hp
  rw [p.sum_fiveEquiv j hc (fun i => primaryScore (subclass i))] at hp
  exact hp

theorem table_secondary_nonpos (p : Packing I b)
    (subclass : I.Item → Subclass) (label : I.Item → Option (Fin n))
    (coordinate : I.Item → ℚ)
    (hsize : ∀ i, I.size i = encodedSize (subclass i) (label i) (coordinate i))
    (hw : ∀ i, |coordinate i| ≤ 6) (t : p.TableBin subclass) :
    (∑ i ∈ p.binItems t.val, secondaryScore (subclass i) (label i)) ≤ 0 := by
  let e := p.fiveEquiv t.val t.property.1
  have hp : BinPackingGap.primaryTotal (fun i => subclass (e i).val) = 0 := by
    change (∑ i : Fin 5,
      primaryScore (subclass (p.fiveEquiv t.val t.property.1 i).val)) = 0
    rw [p.sum_fiveEquiv t.val t.property.1 (fun i => primaryScore (subclass i))]
    exact t.property.2
  have hcap : (∑ i : Fin 5,
      encodedSize (subclass (e i).val) (label (e i).val) (coordinate (e i).val)) ≤ 1 := by
    simp_rw [← hsize]
    rw [p.sum_fiveEquiv]
    exact p.bin_capacity t.val
  have hq := sum_secondary_nonpos_of_feasible
    (fun i => subclass (e i).val) (fun i => label (e i).val)
    (fun i => coordinate (e i).val) (fun i => hw _) hp hcap
  change (∑ i : Fin 5,
    secondaryScore (subclass (p.fiveEquiv t.val t.property.1 i).val)
      (label (p.fiveEquiv t.val t.property.1 i).val)) ≤ 0 at hq
  rw [p.sum_fiveEquiv t.val t.property.1
    (fun i => secondaryScore (subclass i) (label i))] at hq
  exact hq

theorem sum_itemAtRole (p : Packing I b) (subclass : I.Item → Subclass)
    (t : p.TableBin subclass) {M : Type*} [AddCommMonoid M] (f : I.Item → M) :
    (∑ r : Role, f (p.itemAtRole subclass t r)) = ∑ i ∈ p.binItems t.val, f i := by
  change (∑ r : Role, f (p.tableEquiv subclass t r).val) =
    ∑ i ∈ p.binItems t.val, f i
  rw [(p.tableEquiv subclass t).sum_comp (fun i : p.binItems t.val => f i.val)]
  change (∑ i ∈ (p.binItems t.val).attach, f i.val) = ∑ i ∈ p.binItems t.val, f i
  exact Finset.sum_attach (p.binItems t.val) f

theorem table_secondary_eq (p : Packing I b)
    (subclass : I.Item → Subclass) (label : I.Item → Option (Fin n))
    (t : p.TableBin subclass) (x d a : Fin n)
    (hl : ∀ r, label (p.itemAtRole subclass t r) = tableRoleLabel x d a r) :
    (∑ i ∈ p.binItems t.val, secondaryScore (subclass i) (label i)) =
      labelSecondary x d a := by
  rw [← p.sum_itemAtRole subclass t]
  simp only [secondaryScore, p.itemAtRole_role, hl]
  rw [Role.sum_univ]
  simp [tableRoleLabel, labelSecondary]
  ring

theorem table_labels_le_anchor (p : Packing I b)
    (subclass : I.Item → Subclass) (label : I.Item → Option (Fin n))
    (coordinate : I.Item → ℚ)
    (hsize : ∀ i, I.size i = encodedSize (subclass i) (label i) (coordinate i))
    (hw : ∀ i, |coordinate i| ≤ 6) (t : p.TableBin subclass)
    (x d a : Fin n)
    (hl : ∀ r, label (p.itemAtRole subclass t r) = tableRoleLabel x d a r) :
    x ≤ a ∧ d ≤ a := by
  have hq := p.table_secondary_nonpos subclass label coordinate hsize hw t
  rw [p.table_secondary_eq subclass label t x d a hl] at hq
  exact labelSecondary_nonpos_iff.mp hq

theorem table_coordinate_nonpos (p : Packing I b)
    (subclass : I.Item → Subclass) (label : I.Item → Option (Fin n))
    (coordinate : I.Item → ℚ)
    (hsize : ∀ i, I.size i = encodedSize (subclass i) (label i) (coordinate i))
    (t : p.TableBin subclass)
    (hq : (∑ i ∈ p.binItems t.val, secondaryScore (subclass i) (label i)) = 0) :
    (∑ i ∈ p.binItems t.val, coordinate i) ≤ 0 := by
  let e := p.fiveEquiv t.val t.property.1
  have hp : BinPackingGap.primaryTotal (fun i => subclass (e i).val) = 0 := by
    change (∑ i : Fin 5,
      primaryScore (subclass (p.fiveEquiv t.val t.property.1 i).val)) = 0
    rw [p.sum_fiveEquiv t.val t.property.1 (fun i => primaryScore (subclass i))]
    exact t.property.2
  have hq' : secondaryTotal (fun i => subclass (e i).val)
      (fun i => label (e i).val) = 0 := by
    change (∑ i : Fin 5,
      secondaryScore (subclass (p.fiveEquiv t.val t.property.1 i).val)
        (label (p.fiveEquiv t.val t.property.1 i).val)) = 0
    rw [p.sum_fiveEquiv t.val t.property.1
      (fun i => secondaryScore (subclass i) (label i))]
    exact hq
  have hcap : (∑ i : Fin 5,
      encodedSize (subclass (e i).val) (label (e i).val) (coordinate (e i).val)) ≤ 1 := by
    simp_rw [← hsize]
    rw [p.sum_fiveEquiv]
    exact p.bin_capacity t.val
  have hw := (feasible_iff_coordinateSum_nonpos
    (fun i => subclass (e i).val) (fun i => label (e i).val)
    (fun i => coordinate (e i).val) hp hq').mp hcap
  change (∑ i : Fin 5, coordinate (p.fiveEquiv t.val t.property.1 i).val) ≤ 0 at hw
  rw [p.sum_fiveEquiv t.val t.property.1 coordinate] at hw
  exact hw

theorem table_coordinate_nonpos_of_same_label (p : Packing I b)
    (subclass : I.Item → Subclass) (label : I.Item → Option (Fin n))
    (coordinate : I.Item → ℚ)
    (hsize : ∀ i, I.size i = encodedSize (subclass i) (label i) (coordinate i))
    (t : p.TableBin subclass) (v : Fin n)
    (hl : ∀ r, label (p.itemAtRole subclass t r) = tableRoleLabel v v v r) :
    (∑ r : Role, coordinate (p.itemAtRole subclass t r)) ≤ 0 := by
  rw [p.sum_itemAtRole]
  apply p.table_coordinate_nonpos subclass label coordinate hsize t
  rw [p.table_secondary_eq subclass label t v v v hl]
  simp [labelSecondary]
  ring

def outsideTableItems (p : Packing I b) (subclass : I.Item → Subclass) :
    Finset I.Item := by
  classical
  exact Finset.univ.filter fun i => ¬ p.IsTableBin subclass (p.assignment i)

theorem outsideTableItems_card_lt (p : Packing I b)
    (subclass : I.Item → Subclass) (label : I.Item → Option (Fin n))
    (coordinate : I.Item → ℚ)
    (hsize : ∀ i, I.size i = encodedSize (subclass i) (label i) (coordinate i))
    (hw : ∀ i, |coordinate i| ≤ 6) (B c : ℕ)
    (hcard : I.n = 5 * B) (hb : b ≤ B + c)
    (htotal : (∑ i, primaryScore (subclass i)) = 0) :
    (p.outsideTableItems subclass).card <
      25 * (c + 1) * (1 + 5 * primaryBound) := by
  classical
  have hlarge (i : I.Item) : (1 / 6 : ℚ) < I.size i := by
    rw [hsize]
    exact (encodedSize_mem_interval _ _ _ (hw i)).1
  have hcap := p.bin_card_le_five hlarge
  have hfull (j : Fin b) (hc : (PrimaryLoss.fiber p.assignment j).card = 5) :
      PrimaryLoss.binPrimary p.assignment (fun i => primaryScore (subclass i)) j ≤ 0 := by
    exact p.full_primary_nonpos subclass label coordinate hsize hw j hc
  have h := PrimaryLoss.primary_loss_bound p.assignment
    (fun i => primaryScore (subclass i)) B c primaryBound
    (by simpa using hcard) hcap hb (fun i => primaryScore_abs_lt (subclass i)) htotal hfull
  have hsets : p.outsideTableItems subclass =
      PrimaryLoss.outsideZeroFullItems p.assignment (fun i => primaryScore (subclass i)) := by
    ext i
    constructor
    · intro hi
      have hi' := (Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi'⟩
    · intro hi
      have hi' := (Finset.mem_filter.mp hi).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi'⟩
  rw [hsets]
  exact h.2.2.2

end Packing

end BinPackingGap

end

end OAI
