import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Finsupp.Basic

namespace OAI

namespace PiExponent.ProjectiveMonomialCech

noncomputable section

open scoped BigOperators

variable {ι K : Type*} [Fintype ι] [AddCommGroup K]

def Monomial (ι : Type*) [Fintype ι] (d : ℤ) :=
  {a : ι → ℤ // ∑ i, a i = d}

abbrev Laurent (ι K : Type*) [Fintype ι] [Zero K] (d : ℤ) :=
  Monomial ι d →₀ K

def RegularOn {d : ℤ} (s : Set ι) (f : Laurent ι K d) : Prop :=
  ∀ a, f a ≠ 0 → ∀ k, a.val k < 0 → k ∈ s

def overlapSupport {d : ℤ} (c : ι → ι → Laurent ι K d) (i : ι) :
    Finset (Monomial ι d) := by
  classical
  exact Finset.univ.biUnion fun j => (c j i).support

def primitive {d : ℤ} (pivot : Monomial ι d → ι)
    (c : ι → ι → Laurent ι K d) (i : ι) : Laurent ι K d := by
  classical
  exact Finsupp.onFinset (overlapSupport c i)
    (fun a => c (pivot a) i a)
    (fun a ha => Finset.mem_biUnion.mpr
      ⟨pivot a, Finset.mem_univ _, Finsupp.mem_support_iff.mpr ha⟩)

@[simp] theorem primitive_apply {d : ℤ} (pivot : Monomial ι d → ι)
    (c : ι → ι → Laurent ι K d) (i : ι) (a : Monomial ι d) :
    primitive pivot c i a = c (pivot a) i a := rfl

theorem primitive_support_subset {d : ℤ} (pivot : Monomial ι d → ι)
    (c : ι → ι → Laurent ι K d) (i : ι) :
    (primitive pivot c i).support ⊆ overlapSupport c i := by
  classical
  exact Finsupp.support_onFinset_subset

theorem primitive_regular {d : ℤ} (pivot : Monomial ι d → ι)
    (hpivot : ∀ a : Monomial ι d, 0 ≤ a.val (pivot a))
    (c : ι → ι → Laurent ι K d)
    (hregular : ∀ i j, RegularOn {i, j} (c i j)) (i : ι) :
    RegularOn {i} (primitive pivot c i) := by
  intro a ha k hk
  have hmem := hregular (pivot a) i a ha k hk
  rcases hmem with h | h
  · subst k
    exact False.elim ((not_lt_of_ge (hpivot a)) hk)
  · exact h

theorem primitive_coboundary {d : ℤ} (pivot : Monomial ι d → ι)
    (c : ι → ι → Laurent ι K d)
    (hcocycle : ∀ i j k, c i j + c j k = c i k) (i j : ι) :
    c i j = primitive pivot c j - primitive pivot c i := by
  ext a
  have h := congrArg (fun f : Laurent ι K d => f a) (hcocycle (pivot a) i j)
  simp only [Finsupp.add_apply] at h
  simp only [Finsupp.sub_apply, primitive_apply]
  exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using h)

theorem exists_primitive_of_pivot {d : ℤ} (pivot : Monomial ι d → ι)
    (hpivot : ∀ a : Monomial ι d, 0 ≤ a.val (pivot a))
    (c : ι → ι → Laurent ι K d)
    (hregular : ∀ i j, RegularOn {i, j} (c i j))
    (hcocycle : ∀ i j k, c i j + c j k = c i k) :
    ∃ b : ι → Laurent ι K d,
      (∀ i, RegularOn {i} (b i)) ∧ (∀ i j, c i j = b j - b i) := by
  exact ⟨primitive pivot c, primitive_regular pivot hpivot c hregular,
    primitive_coboundary pivot c hcocycle⟩

theorem exists_nonnegative_coordinate [Nonempty ι] {d : ℤ}
    (hd : 0 ≤ d) (a : Monomial ι d) : ∃ i, 0 ≤ a.val i := by
  by_contra h
  have hneg : ∀ i, a.val i < 0 := fun i => lt_of_not_ge (fun hi => h ⟨i, hi⟩)
  have htotal : (∑ i, a.val i) < 0 :=
    Finset.sum_neg (fun i _ => hneg i) Finset.univ_nonempty
  rw [a.property] at htotal
  exact (not_lt_of_ge hd) htotal

theorem nonnegative_twist_cech_exact {d : ℤ} (hd : 0 ≤ d)
    (c : ι → ι → Laurent ι K d)
    (hregular : ∀ i j, RegularOn {i, j} (c i j))
    (hcocycle : ∀ i j k, c i j + c j k = c i k) :
    ∃ b : ι → Laurent ι K d,
      (∀ i, RegularOn {i} (b i)) ∧ (∀ i j, c i j = b j - b i) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h => exact ⟨fun i => isEmptyElim i, fun i => isEmptyElim i, fun i => isEmptyElim i⟩
  | inr h =>
      let pivot : Monomial ι d → ι :=
        fun a => Classical.choose (exists_nonnegative_coordinate hd a)
      have hpivot : ∀ a : Monomial ι d, 0 ≤ a.val (pivot a) :=
        fun a => Classical.choose_spec (exists_nonnegative_coordinate hd a)
      exact exists_primitive_of_pivot pivot hpivot c hregular hcocycle

end
end PiExponent.ProjectiveMonomialCech

end OAI
