import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialMatrixScalarExtension
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.GroupTheory.Finiteness

namespace OAI

/-! # A finitely generated field of coefficients for a finitely generated matrix group -/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

theorem exists_finite_coefficient_field
    {K G : Type} [Field K] [CharZero K] [Group G] [Group.FG G] {n : ℕ}
    (ι : G →* PolynomialMatrixGroup K n) :
    ∃ L : IntermediateField ℚ K, L.FG ∧ ∀ g i j, entries (ι g) i j ∈ L := by
  classical
  obtain ⟨s, hs⟩ := Monoid.FG.fg_top (M := G)
  let c : s × Fin n × Fin n → K := fun a => entries (ι a.1) a.2.1 a.2.2
  let L := IntermediateField.adjoin ℚ (Set.range c)
  refine ⟨L, IntermediateField.fg_adjoin_of_finite (Set.finite_range c), ?_⟩
  intro g
  have hg : g ∈ Submonoid.closure (s : Set G) := by rw [hs]; trivial
  induction hg using Submonoid.closure_induction with
  | mem g hg =>
    intro i j
    exact IntermediateField.subset_adjoin ℚ _ ⟨(⟨g, hg⟩, i, j), rfl⟩
  | one =>
    intro i j
    rw [map_one]
    change (if i = j then (1 : K) else 0) ∈ L
    split_ifs <;> simp
  | mul g h _ _ hg hh =>
    intro i j
    rw [map_mul, entries_mul, Matrix.mul_apply]
    exact L.sum_mem fun k _ => L.mul_mem (hg i k) (hh k j)

def restrictCoefficientField
    {K G : Type} [Field K] [CharZero K] [Group G] {n : ℕ}
    (ι : G →* PolynomialMatrixGroup K n) (L : IntermediateField ℚ K)
    (hL : ∀ g i j, entries (ι g) i j ∈ L) : G →* PolynomialMatrixGroup L n := by
  let A (g : G) : Matrix (Fin n) (Fin n) L := fun i j => ⟨entries (ι g) i j, hL g i j⟩
  let F : Matrix (Fin n) (Fin n) L →+* Matrix (Fin n) (Fin n) K :=
    RingHom.mapMatrix (algebraMap L K)
  have hF : Function.Injective F := by
    intro x y he
    funext i j
    apply Subtype.ext
    exact congrArg (fun M : Matrix (Fin n) (Fin n) K => M i j) he
  have hA (g : G) : F (A g) = entries (ι g) := rfl
  have hmul (g h : G) : A (g * h) = A g * A h := by
    apply hF
    rw [map_mul, hA, hA, hA, map_mul, entries_mul]
  have hone : A 1 = 1 := by
    apply hF
    rw [hA, map_one, map_one]
    rfl
  let U (g : G) : Matrix.GeneralLinearGroup (Fin n) L := {
    val := A g
    inv := A g⁻¹
    val_inv := by rw [← hmul, mul_inv_cancel, hone]
    inv_val := by rw [← hmul, inv_mul_cancel, hone] }
  exact {
    toFun g := ⟨U g⟩
    map_one' := PolynomialMatrixGroup.ext (Units.ext hone)
    map_mul' g h := PolynomialMatrixGroup.ext (Units.ext (hmul g h)) }

@[simp] theorem restrictCoefficientField_entries
    {K G : Type} [Field K] [CharZero K] [Group G] {n : ℕ}
    (ι : G →* PolynomialMatrixGroup K n) (L : IntermediateField ℚ K)
    (hL : ∀ g i j, entries (ι g) i j ∈ L) (g : G) (i j : Fin n) :
    (entries (K := L) (restrictCoefficientField ι L hL g) i j : K) = entries (ι g) i j := rfl

theorem restrictCoefficientField_injective
    {K G : Type} [Field K] [CharZero K] [Group G] {n : ℕ}
    (ι : G →* PolynomialMatrixGroup K n) (L : IntermediateField ℚ K)
    (hL : ∀ g i j, entries (ι g) i j ∈ L) (hι : Function.Injective ι) :
    Function.Injective (restrictCoefficientField ι L hL) := by
  intro g h he
  apply hι
  apply PolynomialMatrixGroup.ext
  apply Units.ext
  ext i j
  exact congrArg (fun a : PolynomialMatrixGroup L n => (entries (K := L) a i j : K)) he

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI
