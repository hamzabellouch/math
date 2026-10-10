import OAI.Algebra.FormulaHitting.Model
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Lean.Elab.Tactic.Omega

namespace OAI

namespace NCHitting

theorem convolution_eq_sum {F : Type*} {n : ℕ} [Semiring F]
    (f g : WordSeries F n) (w : Word n) :
    convolution f g w =
      ∑ k ∈ Finset.range (w.length + 1), f (w.take k) * g (w.drop k) := by
  induction w generalizing f with
  | nil => simp [convolution]
  | cons i w ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.take_zero, List.drop_zero, List.take_succ_cons,
      List.drop_succ_cons]
    rw [convolution, ih]
    exact add_comm _ _

namespace Formula

theorem size_pos {F : Type*} {n : ℕ} (f : Formula F n) : 0 < f.size := by
  cases f <;> simp [size]

theorem size_le_one_iff {F : Type*} {n : ℕ} (f : Formula F n) :
    f.size ≤ 1 ↔ (∃ a, f = scalar a) ∨ (∃ i, f = var i) := by
  cases f with
  | scalar a => simp [size]
  | var i => simp [size]
  | add f g =>
    have hf := size_pos f
    have hg := size_pos g
    constructor
    · intro h
      simp only [size] at h
      omega
    · rintro (⟨a, h⟩ | ⟨i, h⟩) <;> cases h
  | mul f g =>
    have hf := size_pos f
    have hg := size_pos g
    constructor
    · intro h
      simp only [size] at h
      omega
    · rintro (⟨a, h⟩ | ⟨i, h⟩) <;> cases h

theorem eval_one_ne_zero_of_size_le_one {F : Type*} {n : ℕ}
    [Semiring F] [Nontrivial F] (f : Formula F n) (hs : f.size ≤ 1)
    (hf : f.coeff ≠ 0) : f.eval id (fun _ => 1) ≠ 0 := by
  rcases (size_le_one_iff f).mp hs with ⟨a, rfl⟩ | ⟨i, rfl⟩
  · intro ha
    apply hf
    funext w
    simp only [eval, id_eq] at ha
    simp [coeff, ha]
  · simp [eval]

theorem coeff_eq_zero_of_length_gt {F : Type*} {n : ℕ} [Semiring F]
    (f : Formula F n) (w : Word n) (hw : f.size < w.length) :
    f.coeff w = 0 := by
  induction f generalizing w with
  | scalar a =>
    simp only [size] at hw
    have : w ≠ [] := by intro h; simp [h] at hw
    simp [coeff, this]
  | var i =>
    simp only [size] at hw
    have : w ≠ [i] := by intro h; simp [h] at hw
    simp [coeff, this]
  | add f g ihf ihg =>
    simp only [size] at hw
    have hf : f.size < w.length := by omega
    have hg : g.size < w.length := by omega
    simp [coeff, ihf w hf, ihg w hg]
  | mul f g ihf ihg =>
    simp only [size] at hw
    rw [coeff, convolution_eq_sum]
    apply Finset.sum_eq_zero
    intro k hk
    have hk' : k ≤ w.length := by
      have hk'' := Finset.mem_range.mp hk
      omega
    by_cases hf : f.size < (w.take k).length
    · rw [ihf _ hf, zero_mul]
    · have hg : g.size < (w.drop k).length := by
        simp only [List.length_take, List.length_drop, Nat.min_eq_left hk'] at hf ⊢
        omega
      rw [ihg _ hg, mul_zero]

end Formula

def wordsOfLength (n : ℕ) : ℕ → Finset (Word n)
  | 0 => {[]}
  | k + 1 => Finset.univ.biUnion fun i => (wordsOfLength n k).image (List.cons i)

theorem mem_wordsOfLength {n k : ℕ} (w : Word n) :
    w ∈ wordsOfLength n k ↔ w.length = k := by
  induction k generalizing w with
  | zero => simp [wordsOfLength]
  | succ k ih =>
    cases w with
    | nil => simp [wordsOfLength]
    | cons i w => simp [wordsOfLength, ih]

theorem sum_wordsOfLength_succ {M : Type*} [AddCommMonoid M]
    {n : ℕ} (k : ℕ) (f : Word n → M) :
    (∑ w ∈ wordsOfLength n (k + 1), f w) =
      ∑ i : Fin n, ∑ w ∈ wordsOfLength n k, f (i :: w) := by
  rw [wordsOfLength, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_image (by
      intro a _ b _ h
      exact (List.cons.inj h).2)
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro w hi hj
    rcases Finset.mem_image.mp hi with ⟨v, _, hv⟩
    rcases Finset.mem_image.mp hj with ⟨v', _, hv'⟩
    exact hij (List.cons.inj (hv.trans hv'.symm)).1

theorem Formula.coeff_support_finite {F : Type*} {n : ℕ} [Semiring F]
    (f : Formula F n) : (Function.support f.coeff).Finite := by
  classical
  let bound := (Finset.range (f.size + 1)).biUnion (wordsOfLength n)
  apply Set.Finite.subset bound.finite_toSet
  intro w hw
  have hlen : w.length ≤ f.size := by
    by_contra h
    exact hw (f.coeff_eq_zero_of_length_gt w (by omega))
  exact Finset.mem_biUnion.mpr ⟨w.length, Finset.mem_range.mpr (by omega),
    (mem_wordsOfLength w).mpr rfl⟩

noncomputable def Formula.polynomial {F : Type*} {n : ℕ} [Semiring F]
    (f : Formula F n) : Word n →₀ F :=
  Finsupp.ofSupportFinite f.coeff f.coeff_support_finite

@[simp] theorem Formula.polynomial_apply {F : Type*} {n : ℕ} [Semiring F]
    (f : Formula F n) (w : Word n) : f.polynomial w = f.coeff w := rfl

end NCHitting

end OAI
