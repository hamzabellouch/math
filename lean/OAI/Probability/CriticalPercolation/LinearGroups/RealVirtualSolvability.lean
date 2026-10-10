import Mathlib
import OAI.Probability.CriticalPercolation.LinearGroups.AlgebraicVirtualSolvability

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical Cardinal

namespace CriticalPercolation.LinearGrowth

lemma countable_finiteType_int (D : Type) [CommRing D] [Algebra ℤ D]
    [Algebra.FiniteType ℤ D] : Countable D := by
  obtain ⟨n,f,hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial).mp
    (inferInstance : Algebra.FiniteType ℤ D)
  let : Countable (MvPolynomial n ℤ) := by
    apply Function.Injective.countable (f := AddMonoidAlgebra.coeff)
    intro x y h
    cases x; cases y; cases h; rfl
  exact Function.Surjective.countable hf

lemma countable_fraction (D : Type) [CommRing D] [Countable D] : Countable (FractionRing D) := by
  apply Cardinal.mk_le_aleph0_iff.mp
  rw [Cardinal.mk_fractionRing]
  exact Cardinal.mk_le_aleph0

lemma countable_algebraicClosure (F : Type) [Field F] [Countable F] :
    Countable (AlgebraicClosure F) := by
  have h := Algebraic.countable F (AlgebraicClosure F)
  have he : {x : AlgebraicClosure F | IsAlgebraic F x}=Set.univ :=
    Set.eq_univ_of_forall (fun _ => Algebra.IsAlgebraic.isAlgebraic _)
  rw [he] at h
  exact Set.countable_univ_iff.mp h

lemma matrixRepresentation_injective {K G n : Type} [Field K] [Group G]
    [Fintype n] [DecidableEq n] (ρ : G →* GL n K) (hρ : Injective ρ) :
    Injective (matrixRepresentation ρ) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (n → K)).injective.comp
    (Matrix.GeneralLinearGroup.toLin.injective.comp hρ)

lemma virtually_solvable_real_matrix {G n : Type} [Group G] [DecidableEq G]
    [Fintype n] [DecidableEq n] (ρ : G →* GL n ℝ) (hρ : Injective ρ)
    {degree : ℕ} (hg : SparseGrowth.HasPolynomialDegree G degree) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H := by
  let := hg.fg
  obtain ⟨D,hD,hm⟩ := exists_finiteType_matrix_ring ρ
  let := hD
  let : Countable D := countable_finiteType_int D
  let F := FractionRing D
  let K := AlgebraicClosure F
  let : Countable F := countable_fraction D
  let : Countable K := countable_algebraicClosure F
  let f : D →+* K := (algebraMap F K).comp (algebraMap D F)
  have hf : Injective f := (algebraMap F K).injective.comp (IsFractionRing.injective D F)
  let σ := liftMatrixGroup ρ D hm
  let τ := (Matrix.GeneralLinearGroup.map f).comp σ
  have hσ : Injective σ := liftMatrixGroup_injective ρ D hm hρ
  have hτ : Injective τ := by
    intro x y h
    apply hσ
    apply Units.ext
    apply Matrix.ext
    intro i j
    apply hf
    exact congrArg (fun M : GL n K => M i j) h
  exact virtually_solvable_linear K (n → K) G (matrixRepresentation τ)
    (matrixRepresentation_injective τ hτ) hg

lemma virtually_solvable_real_linear {G V : Type} [Group G] [DecidableEq G]
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (ρ : G →* (V ≃ₗ[ℝ] V)) (hρ : Injective ρ)
    {degree : ℕ} (hg : SparseGrowth.HasPolynomialDegree G degree) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H := by
  let τ := (linearMatrixEquiv (K:=ℝ) (V:=V)).toMonoidHom.comp ρ
  exact virtually_solvable_real_matrix τ (linearMatrixEquiv.injective.comp hρ) hg

end CriticalPercolation.LinearGrowth

namespace CriticalPercolation.LinearGrowth
lemma virtually_solvable_real_linear_general {G V : Type*} [Group G] [DecidableEq G]
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (ρ : G →* (V ≃ₗ[ℝ] V)) (hρ : Injective ρ)
    {degree : ℕ} (hg : SparseGrowth.HasPolynomialDegree G degree) :
    ∃ H : Subgroup G, H.FiniteIndex ∧ Group.IsSolvable H := by
  let τ := (linearMatrixEquiv (K:=ℝ) (V:=V)).toMonoidHom.comp ρ
  have hτ : Injective τ := linearMatrixEquiv.injective.comp hρ
  have hgτ := hg.of_surjective τ.rangeRestrict τ.rangeRestrict_surjective
  obtain ⟨P,hPi,hPs⟩ := virtually_solvable_real_matrix τ.range.subtype Subtype.val_injective hgτ
  let := hPi
  let := hPs
  let H := P.comap τ.rangeRestrict
  have hHi : H.FiniteIndex := finiteIndex_comap_surjective τ.rangeRestrict τ.rangeRestrict_surjective P
  let ψ : H →* P := (τ.rangeRestrict.comp H.subtype).codRestrict P (fun h => h.property)
  have hψ : Injective ψ := by
    intro x y he
    apply Subtype.ext
    apply hτ
    exact congrArg (fun z : P => (z.val : GL (Fin (finrank ℝ V)) ℝ)) he
  exact ⟨H,hHi,Group.isSolvable_of_isSolvable_injective hψ⟩
end CriticalPercolation.LinearGrowth
end
end

end OAI
