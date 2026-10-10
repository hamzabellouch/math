import OAI.Analysis.KadisonKastler.TypeIIIProjectionComparison
import OAI.Analysis.KadisonKastler.FiniteInnerComposition

namespace OAI

/-! # Exact averaging of projections with two infinite sides -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- Complementary equivalences assemble to a unitary in the original algebra. -/
theorem exists_unitary_conjugacy_of_equivalent_complements
    (p q : AlgebraProjection M) (hpq : p.Equivalent q)
    (hc : AlgebraProjection.Equivalent
      (⟨1 - p.val, p.property.one_sub⟩ : AlgebraProjection M)
      (⟨1 - q.val, q.property.one_sub⟩ : AlgebraProjection M)) :
    ∃ u : unitary (Algebra M), (u : Algebra M) * p.val * star (u : Algebra M) = q.val := by
  obtain ⟨v, hv, hvt⟩ := hpq
  obtain ⟨w, hw, hwt⟩ := hc
  have hi : v.support.val * w.support.val = 0 := by
    rw [hv, hw]
    exact p.property.mul_one_sub_self
  have hf : v.target.val * w.target.val = 0 := by
    rw [hvt, hwt]
    exact q.property.mul_one_sub_self
  let a := v.patch w hi hf
  have hai : star a.val * a.val = 1 := by
    rw [a.initial]
    change v.support.val + w.support.val = 1
    rw [hv, hw]
    change p.val + (1 - p.val) = 1
    abel
  have haf : a.val * star a.val = 1 := by
    change a.target.val = 1
    rw [PartialIsometry.patch_target, hvt, hwt]
    change q.val + (1 - q.val) = 1
    abel
  let u : unitary (Algebra M) := ⟨a.val, hai, haf⟩
  have hup : (u : Algebra M) * p.val = v.val := by
    rw [← hv]
    exact v.le_patch w hi hf
  have he : (u : Algebra M) * p.val * star (u : Algebra M) =
      ((u : Algebra M) * p.val) * star ((u : Algebra M) * p.val) := by
    rw [star_mul, p.property.isSelfAdjoint.star_eq]
    calc
      _ = (u : Algebra M) * (p.val * p.val) * star (u : Algebra M) := by
        rw [p.property.isIdempotentElem.eq]
      _ = _ := by simp only [mul_assoc]
  refine ⟨u, ?_⟩
  rw [he, hup]
  exact congrArg Subtype.val hvt

/-- A projection and its infinite complement can be interchanged in a
separably represented factor. -/
theorem exists_unitary_swap_of_infinite_sides [TopologicalSpace.SeparableSpace H]
    (hM : ScalarCenter M) (p : AlgebraProjection M)
    (hp : ¬ FiniteProjectionIn M p.val)
    (hc : ¬ FiniteProjectionIn M (1 - p.val)) :
    ∃ u : unitary (Algebra M),
      (u : Algebra M) * p.val * star (u : Algebra M) = 1 - p.val := by
  let q : AlgebraProjection M := ⟨1 - p.val, p.property.one_sub⟩
  have hpe := projection_equivalent_one_of_not_finite hM p hp
  have hqe := projection_equivalent_one_of_not_finite hM q hc
  have he : p.Equivalent q := AlgebraProjection.equivalent_trans hpe
    (AlgebraProjection.equivalent_symm hqe)
  apply exists_unitary_conjugacy_of_equivalent_complements p q he
  have hqq : (⟨1 - q.val, q.property.one_sub⟩ : AlgebraProjection M) = p := by
    apply Subtype.ext
    change 1 - (1 - p.val) = p.val
    abel
  rw [hqq]
  exact AlgebraProjection.equivalent_symm he

/-- The identity and a swapping unitary give the exact scalar one-half average. -/
theorem exists_half_average_of_infinite_sides [TopologicalSpace.SeparableSpace H]
    (hM : ScalarCenter M) (p : AlgebraProjection M)
    (hp : ¬ FiniteProjectionIn M p.val)
    (hc : ¬ FiniteProjectionIn M (1 - p.val)) :
    ∃ A : FiniteInnerAverage M,
      A.apply p.val.val = (1 / 2 : ℂ) • (1 : H →L[ℂ] H) := by
  obtain ⟨u, hu⟩ := exists_unitary_swap_of_infinite_sides hM p hp hc
  let A : FiniteInnerAverage M := {
    Index := Bool
    fintype := inferInstance
    nonempty := inferInstance
    unitary b := if b then u else 1 }
  have hu' : unitaryConj (ambientAlgebraUnitary u) p.val.val = 1 - p.val.val :=
    congrArg Subtype.val hu
  refine ⟨A, ?_⟩
  change (Fintype.card Bool : ℂ)⁻¹ •
    (∑ b : Bool, unitaryConj (ambientAlgebraUnitary (if b then u else 1)) p.val.val) = _
  rw [Fintype.sum_bool]
  simp only [Bool.false_eq_true, ↓reduceIte, hu']
  have h1 : unitaryConj (ambientAlgebraUnitary (1 : unitary (Algebra M))) p.val.val = p.val.val := by
    change (1 : H →L[ℂ] H) * p.val.val * star (1 : H →L[ℂ] H) = _
    simp
  rw [h1]
  have hs : (1 : H →L[ℂ] H) - p.val.val + p.val.val = 1 := sub_add_cancel _ _
  rw [hs]
  norm_num

end

end KadisonKastler

end OAI
