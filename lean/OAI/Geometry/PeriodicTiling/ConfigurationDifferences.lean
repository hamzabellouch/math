import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Abel

namespace OAI

universe uG uA uι

namespace PeriodicTilingThree

variable {G : Type uG} {A : Type uA} [AddCommGroup G] [AddCommGroup A]

def configDiff (v : G) (f : G → A) : G → A :=
  fun x => f (x + v) - f x

@[simp] theorem configDiff_apply (v : G) (f : G → A) (x : G) :
    configDiff v f x = f (x + v) - f x := rfl

@[simp] theorem configDiff_zero (v : G) : configDiff v (0 : G → A) = 0 := by
  ext x
  simp [configDiff]

@[simp] theorem configDiff_const (v : G) (a : A) :
    configDiff v (fun _ : G => a) = 0 := by
  ext x
  simp [configDiff]

theorem configDiff_add (v : G) (f g : G → A) :
    configDiff v (f + g) = configDiff v f + configDiff v g := by
  ext x
  simp only [configDiff_apply, Pi.add_apply]
  abel

theorem configDiff_sub (v : G) (f g : G → A) :
    configDiff v (f - g) = configDiff v f - configDiff v g := by
  ext x
  simp only [configDiff_apply, Pi.sub_apply]
  abel

theorem configDiff_comm (v w : G) (f : G → A) :
    configDiff v (configDiff w f) = configDiff w (configDiff v f) := by
  ext x
  have h : x + v + w = x + w + v := by abel
  simp only [configDiff_apply, h]
  abel

theorem configDiff_eq_zero_iff (v : G) (f : G → A) :
    configDiff v f = 0 ↔ Function.Periodic f v := by
  constructor
  · intro h x
    have hx := congrFun h x
    exact sub_eq_zero.mp hx
  · intro h
    ext x
    exact sub_eq_zero.mpr (h x)

theorem configDiff_add_period (v p : G) (f : G → A)
    (hp : Function.Periodic f p) : configDiff (v + p) f = configDiff v f := by
  ext x
  simp only [configDiff_apply, ← add_assoc, hp (x + v)]

theorem configDiff_preserves_period (v p : G) (f : G → A)
    (hp : Function.Periodic f p) : Function.Periodic (configDiff v f) p := by
  apply (configDiff_eq_zero_iff p _).mp
  rw [configDiff_comm, (configDiff_eq_zero_iff p f).mpr hp, configDiff_zero]

theorem configDiff_sum {ι : Type uι} (s : Finset ι) (v : G) (f : ι → G → A) :
    configDiff v (∑ i ∈ s, f i) = ∑ i ∈ s, configDiff v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, configDiff_add, ih]

def configDiffs : List G → (G → A) → (G → A)
  | [], f => f
  | v :: vs, f => configDiff v (configDiffs vs f)

@[simp] theorem configDiffs_nil (f : G → A) : configDiffs [] f = f := rfl

@[simp] theorem configDiffs_cons (v : G) (vs : List G) (f : G → A) :
    configDiffs (v :: vs) f = configDiff v (configDiffs vs f) := rfl

@[simp] theorem configDiffs_zero (vs : List G) :
    configDiffs vs (0 : G → A) = 0 := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [configDiffs_cons, ih, configDiff_zero]

theorem configDiff_configDiffs (v : G) (vs : List G) (f : G → A) :
    configDiff v (configDiffs vs f) = configDiffs vs (configDiff v f) := by
  induction vs with
  | nil => rfl
  | cons w vs ih =>
      simp only [configDiffs_cons, configDiff_comm v w, ih]

theorem configDiffs_add (vs : List G) (f g : G → A) :
    configDiffs vs (f + g) = configDiffs vs f + configDiffs vs g := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [configDiffs_cons, ih, configDiff_add]

theorem configDiffs_sub (vs : List G) (f g : G → A) :
    configDiffs vs (f - g) = configDiffs vs f - configDiffs vs g := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [configDiffs_cons, ih, configDiff_sub]

theorem configDiffs_sum {ι : Type uι} (s : Finset ι) (vs : List G)
    (f : ι → G → A) :
    configDiffs vs (∑ i ∈ s, f i) = ∑ i ∈ s, configDiffs vs (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, configDiffs_add, ih]

theorem configDiffs_eq_zero_of_mem {v : G} {vs : List G} (hv : v ∈ vs)
    (f : G → A) (hf : configDiff v f = 0) : configDiffs vs f = 0 := by
  induction vs with
  | nil => simp at hv
  | cons w vs ih =>
      rcases List.mem_cons.mp hv with h | h
      · subst w
        rw [configDiffs_cons, configDiff_configDiffs, hf, configDiffs_zero]
      · rw [configDiffs_cons, ih h, configDiff_zero]

theorem configDiffs_const {vs : List G} (hvs : vs ≠ []) (a : A) :
    configDiffs vs (fun _ : G => a) = 0 := by
  cases vs with
  | nil => exact (hvs rfl).elim
  | cons v vs =>
      rw [configDiffs_cons, configDiff_configDiffs, configDiff_const,
        configDiffs_zero]

theorem configDiffs_preserves_period (vs : List G) (p : G) (f : G → A)
    (hp : Function.Periodic f p) : Function.Periodic (configDiffs vs f) p := by
  apply (configDiff_eq_zero_iff p _).mp
  rw [configDiff_configDiffs, (configDiff_eq_zero_iff p f).mpr hp,
    configDiffs_zero]

theorem configDiffs_replicate (n : ℕ) (v : G) (f : G → A) :
    configDiffs (List.replicate n v) f = (configDiff v)^[n] f := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.replicate_succ, configDiffs_cons, ih,
        Function.iterate_succ_apply']

end PeriodicTilingThree

end OAI
