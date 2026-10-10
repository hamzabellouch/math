import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.Unitary
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Complex.Basic

namespace OAI

noncomputable section
namespace Invariant233.TowerMatrixUnits

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

def spanStarAlgebra (s : Set A) (h1 : (1 : A) ∈ Submodule.span ℂ s)
    (hmul : ∀ x ∈ s, ∀ y ∈ s, x * y ∈ Submodule.span ℂ s)
    (hstar : ∀ x ∈ s, star x ∈ Submodule.span ℂ s) : StarSubalgebra ℂ A where
  toSubalgebra := (Submodule.span ℂ s).toSubalgebra h1 (by
    intro x y hx hy
    induction hx, hy using Submodule.span_induction₂ with
    | mem_mem x y hx hy => exact hmul x hx y hy
    | zero_left y hy => simp
    | zero_right x hx => simp
    | add_left x y z hx hy hz h1 h2 =>
        simpa only [add_mul] using (Submodule.span ℂ s).add_mem h1 h2
    | add_right x y z hx hy hz h1 h2 =>
        simpa only [mul_add] using (Submodule.span ℂ s).add_mem h1 h2
    | smul_left r x y hx hy h =>
        simpa only [smul_mul_assoc] using (Submodule.span ℂ s).smul_mem r h
    | smul_right r x y hx hy h =>
        simpa only [mul_smul_comm] using (Submodule.span ℂ s).smul_mem r h)
  star_mem' := by
    intro x hx
    change star x ∈ Submodule.span ℂ s
    change x ∈ Submodule.span ℂ s at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hstar x hx
    | zero => simp
    | add x y hx hy hx' hy' =>
        simpa only [star_add] using (Submodule.span ℂ s).add_mem hx' hy'
    | smul r x hx hx' =>
        simpa only [star_smul] using (Submodule.span ℂ s).smul_mem (star r) hx'

@[simp] theorem mem_spanStarAlgebra (s : Set A) (h1 hmul hstar) (x : A) :
    x ∈ spanStarAlgebra s h1 hmul hstar ↔ x ∈ Submodule.span ℂ s := Iff.rfl

theorem spanStarAlgebra_finiteDimensional (s : Set A) (hs : s.Finite) (h1 hmul hstar) :
    FiniteDimensional ℂ (spanStarAlgebra s h1 hmul hstar) := by
  let : FiniteDimensional ℂ (Submodule.span ℂ s) := FiniteDimensional.span_of_finite ℂ hs
  have : FiniteDimensional ℂ
      (spanStarAlgebra s h1 hmul hstar).toSubalgebra.toSubmodule := by
    change FiniteDimensional ℂ (Submodule.span ℂ s)
    infer_instance
  exact (spanStarAlgebra s h1 hmul hstar).toSubalgebra.toSubmoduleEquiv.finiteDimensional

theorem spanStarAlgebra_le (s : Set A) (h1 hmul hstar) (B : StarSubalgebra ℂ A)
    (hs : s ⊆ B) : spanStarAlgebra s h1 hmul hstar ≤ B := by
  change Submodule.span ℂ s ≤ B.toSubalgebra.toSubmodule
  exact Submodule.span_le.mpr hs

theorem spanStarAlgebra_eq_adjoin (s : Set A) (h1 hmul hstar) :
    spanStarAlgebra s h1 hmul hstar = StarAlgebra.adjoin ℂ s := by
  apply le_antisymm
  · exact spanStarAlgebra_le s h1 hmul hstar _ (StarAlgebra.subset_adjoin ℂ s)
  · exact StarAlgebra.adjoin_le (fun _ hx => Submodule.subset_span hx)

variable {ι : Type*} [DecidableEq ι]

structure IsMatrixUnitFamily (e : ι → ι → A) : Prop where
  mul : ∀ i j k l, e i j * e k l = if j = k then e i l else 0
  star : ∀ i j, star (e i j) = e j i

def matrixGenerators (e : ι → ι → A) : Set A :=
  insert 1 (Set.range fun ij : ι × ι => e ij.1 ij.2)

omit [StarRing A] [StarModule ℂ A] [DecidableEq ι] in
theorem matrixUnit_mem_span (e : ι → ι → A) (i j : ι) :
    e i j ∈ Submodule.span ℂ (matrixGenerators e) :=
  Submodule.subset_span (Set.mem_insert_of_mem _ ⟨(i, j), rfl⟩)

omit [StarModule ℂ A] in
theorem matrixGenerators_mul (e : ι → ι → A) (he : IsMatrixUnitFamily e) :
    ∀ x ∈ matrixGenerators e, ∀ y ∈ matrixGenerators e,
      x * y ∈ Submodule.span ℂ (matrixGenerators e) := by
  rintro x (rfl | ⟨⟨i, j⟩, rfl⟩) y hy
  · simpa using Submodule.subset_span hy
  · rcases hy with rfl | ⟨⟨k, l⟩, rfl⟩
    · simpa using matrixUnit_mem_span e i j
    · rw [he.mul]
      split_ifs
      · exact matrixUnit_mem_span e i l
      · exact Submodule.zero_mem _

omit [StarModule ℂ A] in
theorem matrixGenerators_star (e : ι → ι → A) (he : IsMatrixUnitFamily e) :
    ∀ x ∈ matrixGenerators e, star x ∈ Submodule.span ℂ (matrixGenerators e) := by
  rintro x (rfl | ⟨⟨i, j⟩, rfl⟩)
  · simpa using (Submodule.subset_span (Set.mem_insert 1 _) :
      (1 : A) ∈ Submodule.span ℂ (matrixGenerators e))
  · rw [he.star]
    exact matrixUnit_mem_span e j i

def matrixAlgebra (e : ι → ι → A) (he : IsMatrixUnitFamily e) : StarSubalgebra ℂ A :=
  spanStarAlgebra (matrixGenerators e) (Submodule.subset_span (Set.mem_insert 1 _))
    (matrixGenerators_mul e he) (matrixGenerators_star e he)

theorem matrixAlgebra_finiteDimensional [Finite ι] (e : ι → ι → A)
    (he : IsMatrixUnitFamily e) : FiniteDimensional ℂ (matrixAlgebra e he) :=
  spanStarAlgebra_finiteDimensional _ ((Set.finite_range _).insert 1) _ _ _

theorem matrixAlgebra_le (e : ι → ι → A) (he : IsMatrixUnitFamily e)
    (B : StarSubalgebra ℂ A) (heB : ∀ i j, e i j ∈ B) : matrixAlgebra e he ≤ B := by
  apply spanStarAlgebra_le
  rintro x (rfl | ⟨⟨i, j⟩, rfl⟩)
  · exact B.one_mem
  · exact heB i j

@[simp] theorem matrixUnit_mem_matrixAlgebra (e : ι → ι → A)
    (he : IsMatrixUnitFamily e) (i j : ι) : e i j ∈ matrixAlgebra e he :=
  matrixUnit_mem_span e i j

theorem matrixAlgebra_eq_adjoin (e : ι → ι → A) (he : IsMatrixUnitFamily e) :
    matrixAlgebra e he = StarAlgebra.adjoin ℂ (Set.range fun ij : ι × ι => e ij.1 ij.2) := by
  apply le_antisymm
  · apply matrixAlgebra_le
    intro i j
    exact StarAlgebra.subset_adjoin ℂ _ ⟨(i, j), rfl⟩
  · apply StarAlgebra.adjoin_le
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact matrixUnit_mem_matrixAlgebra e he i j

def towerEntry (u : ι → A) (p : A) (i j : ι) : A := u i * p * star (u j)

omit [Algebra ℂ A] [StarModule ℂ A] [DecidableEq ι] in
theorem towerEntry_star (u : ι → A) {p : A} (hp : IsStarProjection p) (i j : ι) :
    star (towerEntry u p i j) = towerEntry u p j i := by
  simp only [towerEntry, star_mul, star_star, hp.isSelfAdjoint.star_eq, mul_assoc]

omit [Algebra ℂ A] [StarModule ℂ A] [DecidableEq ι] in
theorem compressed_eq_zero_of_orthogonal (u : ι → A)
    (hu : ∀ i, u i ∈ unitary A) (p : A) (i j : ι)
    (h : towerEntry u p i i * towerEntry u p j j = 0) :
    p * star (u i) * u j * p = 0 := by
  have h' := congrArg (fun x : A => star (u i) * x * u j) h
  have hi := Unitary.star_mul_self_of_mem (hu i)
  have hj := Unitary.star_mul_self_of_mem (hu j)
  simp only [towerEntry, ← mul_assoc, hi, one_mul, mul_zero, zero_mul] at h'
  simpa only [mul_assoc, hj, mul_one] using h'

omit [Algebra ℂ A] [StarModule ℂ A] in
theorem towerEntry_isMatrixUnitFamily (u : ι → A)
    (hu : ∀ i, u i ∈ unitary A) {p : A} (hp : IsStarProjection p)
    (horth : ∀ i j, i ≠ j → towerEntry u p i i * towerEntry u p j j = 0) :
    IsMatrixUnitFamily (towerEntry u p) := by
  refine ⟨?_, towerEntry_star u hp⟩
  intro i j k l
  by_cases hjk : j = k
  · subst k
    rw [ite_eq_left rfl]
    have huj := Unitary.star_mul_self_of_mem (hu j)
    have hpp : p * p = p := hp.isIdempotentElem
    calc
      towerEntry u p i j * towerEntry u p j l =
          u i * (p * (star (u j) * u j) * p) * star (u l) := by
        simp only [towerEntry, mul_assoc]
      _ = towerEntry u p i l := by rw [huj, mul_one, hpp]; rfl
  · rw [ite_eq_right hjk]
    have hzero := compressed_eq_zero_of_orthogonal u hu p j k (horth j k hjk)
    calc
      towerEntry u p i j * towerEntry u p k l =
          u i * (p * star (u j) * u k * p) * star (u l) := by
        simp only [towerEntry, mul_assoc]
      _ = 0 := by rw [hzero, mul_zero, zero_mul]

theorem exists_finiteDimensional_towerAlgebra [Finite ι] (u : ι → A)
    (hu : ∀ i, u i ∈ unitary A) {p : A} (hp : IsStarProjection p)
    (horth : ∀ i j, i ≠ j → towerEntry u p i i * towerEntry u p j j = 0)
    (B : StarSubalgebra ℂ A) (hpB : p ∈ B) (huB : ∀ i, u i ∈ B) :
    ∃ C : StarSubalgebra ℂ A, C ≤ B ∧ FiniteDimensional ℂ C ∧
      (∀ i j, towerEntry u p i j ∈ C) ∧
      (C.toSubalgebra.toSubmodule = Submodule.span ℂ (matrixGenerators (towerEntry u p))) := by
  let he := towerEntry_isMatrixUnitFamily u hu hp horth
  refine ⟨matrixAlgebra (towerEntry u p) he, ?_,
    matrixAlgebra_finiteDimensional _ he, matrixUnit_mem_matrixAlgebra _ he, rfl⟩
  apply matrixAlgebra_le
  intro i j
  exact B.mul_mem (B.mul_mem (huB i) hpB) (B.star_mem' (huB j))

end Invariant233.TowerMatrixUnits

end

end OAI
