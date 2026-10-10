import Mathlib
import OAI.NumberTheory.PiExponent.Cohomology.ProjectiveMonomialCechHigher

namespace OAI

namespace PiExponent.ProjectiveMonomialFinite
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open ProjectiveMonomialCech ProjectiveMonomialCechHigher

variable {ι K : Type*} [Fintype ι]

def AllNegative {d : ℤ} (a : Monomial ι d) : Prop := ∀ i, a.val i < 0

theorem allNegative_coordinate_bounds {d : ℤ} {a : Monomial ι d}
    (ha : AllNegative a) (i : ι) : d ≤ a.val i ∧ a.val i ≤ 0 := by
  classical
  refine ⟨?_, le_of_lt (ha i)⟩
  calc
    d = ∑ j, a.val j := a.property.symm
    _ ≤ a.val i := by
      simpa using Finset.sum_le_sum_of_subset_of_nonpos
        (f := a.val) (show ({i} : Finset ι) ⊆ Finset.univ by simp)
        (fun j _ _ => le_of_lt (ha j))

instance allNegative_finite (d : ℤ) : Finite {a : Monomial ι d // AllNegative a} := by
  let f : {a : Monomial ι d // AllNegative a} → (ι → Set.Icc d 0) :=
    fun a i => ⟨a.val.val i, allNegative_coordinate_bounds a.property i⟩
  exact Finite.of_injective f (by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i))

instance allNonnegative_finite (d : ℤ) :
    Finite {a : Monomial ι d // ∀ i, 0 ≤ a.val i} := by
  classical
  have hb (a : Monomial ι d) (ha : ∀ i, 0 ≤ a.val i) (i : ι) :
      a.val i ∈ Set.Icc 0 d := by
    refine ⟨ha i, ?_⟩
    calc
      a.val i ≤ ∑ j, a.val j := Finset.single_le_sum (fun j _ => ha j) (by simp)
      _ = d := a.property
  let f : {a : Monomial ι d // ∀ i, 0 ≤ a.val i} → (ι → Set.Icc 0 d) :=
    fun a i => ⟨a.val.val i, hb a.val a.property i⟩
  exact Finite.of_injective f (by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i))

instance monomial_subsingleton [Subsingleton ι] (d : ℤ) : Subsingleton (Monomial ι d) := by
  classical
  constructor
  intro a b
  apply Subtype.ext
  funext i
  have hi : (Finset.univ : Finset ι) = {i} := by
    ext j
    simp [Subsingleton.elim j i]
  have ha : a.val i = d := by simpa only [hi, Finset.sum_singleton] using a.property
  have hb : b.val i = d := by simpa only [hi, Finset.sum_singleton] using b.property
  exact ha.trans hb.symm

variable [AddCommGroup K]

def filterCochain {d : ℤ} {q : ℕ} (p : Monomial ι d → Prop)
    (c : Cochain ι (Laurent ι K d) q) : Cochain ι (Laurent ι K d) q := by
  classical
  exact fun t => (c t).filter p

@[simp] theorem filterCochain_apply {d : ℤ} {q : ℕ} (p : Monomial ι d → Prop)
    (c : Cochain ι (Laurent ι K d) q) (t : Fin (q + 1) → ι)
    (a : Monomial ι d) : filterCochain p c t a = if p a then c t a else 0 := by
  classical
  rfl

theorem filterCochain_regular {d : ℤ} {q : ℕ} (p : Monomial ι d → Prop)
    (c : Cochain ι (Laurent ι K d) q) (hc : Regular c) :
    Regular (filterCochain p c) := by
  classical
  intro t a ha i hi
  have hn : c t a ≠ 0 := by
    intro hz
    simp [filterCochain_apply, hz] at ha
  exact hc t a hn i hi

theorem differential_filterCochain {d : ℤ} {q : ℕ}
    (p : Monomial ι d → Prop) (c : Cochain ι (Laurent ι K d) q) :
    differential (filterCochain p c) = filterCochain p (differential c) := by
  classical
  funext t
  ext a
  simp only [differential_apply, filterCochain_apply]
  by_cases h : p a
  · simp only [h, ite_true]
  · simp [differential, h]

theorem filterCochain_closed {d : ℤ} {q : ℕ} (p : Monomial ι d → Prop)
    (c : Cochain ι (Laurent ι K d) q) (hc : differential c = 0) :
    differential (filterCochain p c) = 0 := by
  rw [differential_filterCochain, hc]
  funext t
  ext a
  simp

theorem exact_of_obstruction_zero {d : ℤ} {q : ℕ}
    (c : Cochain ι (Laurent ι K d) (q + 1)) (hc : Regular c)
    (hclosed : differential c = 0)
    (hzero : ∀ t a, AllNegative a → c t a = 0) :
    ∃ b : Cochain ι (Laurent ι K d) q, Regular b ∧ differential b = c := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
      refine ⟨fun t => isEmptyElim (t 0), ?_, ?_⟩
      · intro t
        exact isEmptyElim (t 0)
      · funext t
        exact isEmptyElim (t 0)
  | inr h =>
      let pivot : Monomial ι d → ι := fun a =>
        if ha : ∃ i, 0 ≤ a.val i then Classical.choose ha else Classical.choice h
      have hpivot (a : Monomial ι d) (ha : ¬ AllNegative a) : 0 ≤ a.val (pivot a) := by
        have hex : ∃ i, 0 ≤ a.val i := by
          simpa only [AllNegative, not_forall, not_lt] using ha
        simp only [pivot, dite_eq_left hex]
        exact Classical.choose_spec hex
      refine ⟨contraction pivot c, ?_, ?_⟩
      · intro t a ha k hk
        have hn : ¬ AllNegative a := by
          intro hb
          exact ha (hzero (Fin.cons (pivot a) t) a hb)
        obtain ⟨j, hj⟩ := hc (Fin.cons (pivot a) t) a ha k hk
        cases j using Fin.cases with
        | zero =>
            simp only [Fin.cons_zero] at hj
            rw [← hj] at hk
            exact False.elim ((not_lt_of_ge (hpivot a hn)) hk)
        | succ j => exact ⟨j, by simpa only [Fin.cons_succ] using hj⟩
      · have hid := contraction_identity pivot c
        rw [hclosed] at hid
        have hz : contraction pivot (0 : Cochain ι (Laurent ι K d) (q + 2)) = 0 := by
          funext t
          ext a
          rfl
        simpa only [hz, zero_add] using hid

theorem cocycle_eq_boundary_add_negative {d : ℤ} {q : ℕ}
    (c : Cochain ι (Laurent ι K d) (q + 1)) (hc : Regular c)
    (hclosed : differential c = 0) :
    ∃ b : Cochain ι (Laurent ι K d) q,
      Regular b ∧ c = differential b + filterCochain AllNegative c := by
  classical
  let good := filterCochain (fun a => ¬ AllNegative a) c
  have hgood : Regular good := filterCochain_regular _ c hc
  have hgoodclosed : differential good = 0 := filterCochain_closed _ c hclosed
  obtain ⟨b, hb, hdb⟩ := exact_of_obstruction_zero good hgood hgoodclosed (by
    intro t a ha
    simp [good, ha])
  refine ⟨b, hb, ?_⟩
  rw [hdb]
  funext t
  ext a
  simp only [Pi.add_apply, Finsupp.add_apply, good, filterCochain_apply]
  by_cases ha : AllNegative a <;> simp [ha]

end
end PiExponent.ProjectiveMonomialFinite

end OAI
