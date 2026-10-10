import OAI.NumberTheory.Ostmann.Characters.SparsePrimitiveExpansion
import OAI.NumberTheory.Ostmann.Characters.SparseWeightUnitMean

namespace OAI

/-! # The principal coefficient is the exact unit-residue mean -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable local instance {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

theorem sparsePrimitiveCoefficient_principal {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (E : ∀ i, Finset (ZMod (p i))) (t : ℝ) (K : ℕ) :
    sparsePrimitiveCoefficient p E t K none =
      sparseTruncatedMellinCoefficient p E t K (fun _ => 1) := by
  have hlabel : sparsePrimitiveLabel p (fun _ => 1) = none := by
    simp [sparsePrimitiveLabel, sparseProductCharacter, primitiveCharacterReduction]
  rw [← hlabel]
  exact injectiveCoefficient_apply _ (sparsePrimitiveLabel_injective p hc) _ _

theorem productCharacter_unit_sum {n : ℕ} (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (χ : ∀ i, MulChar (ZMod (p i)) ℂ) :
    (∑ x : (∀ i, (ZMod (p i))ˣ), ∏ i, χ i (x i)) =
      if χ = (fun _ => 1) then ∏ i, (Fintype.card (ZMod (p i))ˣ : ℂ) else 0 := by
  rw [← Fintype.prod_sum (fun i (x : (ZMod (p i))ˣ) => χ i x)]
  simp_rw [sum_mulChar_units_eq_ite]
  by_cases hχ : χ = (fun _ => 1)
  · subst χ
    simp
  · rw [ite_eq_right hχ]
    obtain ⟨i, hi⟩ : ∃ i, χ i ≠ 1 := by
      by_contra! hh
      exact hχ (funext hh)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem sparsePrimitiveCoefficient_unit_mean {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (E : ∀ i, Finset (ZMod (p i))) (t : ℝ) (K : ℕ) :
    sparsePrimitiveCoefficient p E t K none =
      (∏ i, (Fintype.card (ZMod (p i))ˣ : ℂ)⁻¹) *
        ∑ x : (∀ i, (ZMod (p i))ˣ),
          elementaryTruncation (fun i => sparseAdditiveKernel (E i) t (x i)) K ^ 2 := by
  have hsum : (∑ x : (∀ i, (ZMod (p i))ˣ),
      elementaryTruncation (fun i => sparseAdditiveKernel (E i) t (x i)) K ^ 2) =
      sparseTruncatedMellinCoefficient p E t K (fun _ => 1) *
        ∏ i, (Fintype.card (ZMod (p i))ˣ : ℂ) := by
    simp_rw [sparseWeight_mellin_expansion]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, productCharacter_unit_sum]
    simp
  rw [hsum, sparsePrimitiveCoefficient_principal p hc, Finset.prod_inv_distrib]
  have hd : (∏ i, (Fintype.card (ZMod (p i))ˣ : ℂ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact_mod_cast Fintype.card_ne_zero
  field_simp

noncomputable def unitNonzeroResidueEquiv (p : ℕ) [Fact p.Prime] :
    (ZMod p)ˣ ≃ NonzeroResidue p where
  toFun u := ⟨u, Finset.mem_erase.mpr ⟨Units.ne_zero u, Finset.mem_univ _⟩⟩
  invFun x := Units.mk0 x.val (Finset.mem_erase.mp x.property).1
  left_inv u := by apply Units.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

theorem sparsePrimitiveCoefficient_tensor_mean {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (E : ∀ i, Finset (ZMod (p i))) (t : ℝ) (K : ℕ) :
    sparsePrimitiveCoefficient p E t K none =
      tensorUnitMean p (fun x => elementaryTruncation
        (fun i => sparseAdditiveKernel (E i) t (x i)) K ^ 2) := by
  rw [sparsePrimitiveCoefficient_unit_mean p hc]
  unfold tensorUnitMean
  have hcard (i : Fin n) : (Fintype.card (ZMod (p i))ˣ : ℂ) = (p i : ℂ) - 1 := by
    rw [ZMod.card_units, Nat.cast_sub (Fact.out : (p i).Prime).one_lt.le, Nat.cast_one]
  simp only [hcard]
  congr 1
  let e := Equiv.piCongrRight (fun i : Fin n => unitNonzeroResidueEquiv (p i))
  have he := e.sum_comp (fun x => elementaryTruncation
    (fun i => sparseAdditiveKernel (E i) t ((x i : NonzeroResidue (p i)) : ZMod (p i))) K ^ 2)
  exact he

theorem sparsePrimitiveCoefficient_real_mean {n : ℕ} (p : Fin n → ℕ)
    [∀ i, Fact (p i).Prime] [NeZero (∏ i, p i)]
    (hc : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (K : ℕ) :
    sparsePrimitiveCoefficient p (fun i => largeTransformSpectrum (normalizedResidueTransform (S i)))
      (17 / 20) K none = (tensorRealUnitMean p (sparseSubsetWeight p S K) : ℂ) := by
  rw [sparsePrimitiveCoefficient_tensor_mean p hc, ← tensorUnitMean_ofReal]
  apply congrArg (tensorUnitMean p)
  funext x
  exact (sparseSubsetWeight_complex p S K x).symm

end Ostmann

end OAI
