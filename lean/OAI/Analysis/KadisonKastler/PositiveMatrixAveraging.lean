import OAI.Analysis.KadisonKastler.PositiveConeQuadraticSupport
import OAI.Analysis.KadisonKastler.PositiveConeFaithfulApproximation
import OAI.Analysis.KadisonKastler.MatrixCentralCone

namespace OAI

/-! # Faithfulness of finite matrix averaging on the positive cone

The explicit central-vector projection preserves separation. Positivity
prevents cancellation between its matrix-unit quadratic summands, and
the diagonal matrix units sum to the identity.
-/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

local instance positiveMatrixAverageRealInner : InnerProductSpace ℝ H := InnerProductSpace.complexToReal

variable (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
  (ξ : H) (hξ : J ξ = ξ)
  (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))

include hJ hright hξ hpos in
theorem positiveCone_projection_kills_sum {ι : Type*} (s : Finset ι) (v : ι → H)
    (hv : ∀ i ∈ s, v i ∈ modularPositiveCone (M := M) J ξ)
    (p : AlgebraProjection M) (hp : p.val.val (∑ i ∈ s, v i) = 0) :
    ∀ i ∈ s, p.val.val (v i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi] at hp
    have hh := positiveCone_projection_kills_summands J hJ hright ξ hξ hpos
      (hv i (Finset.mem_insert_self i s))
      (modularPositiveCone_sum_mem J ξ s v
        (fun j hj => hv j (Finset.mem_insert_of_mem hj))) p hp
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hh.1
    · exact ih (fun k hk => hv k (Finset.mem_insert_of_mem hk)) hh.2 j hj

include hJ hright hξ hpos in
theorem positiveCone_projection_kills_quadratic
    {η : H} (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (p : AlgebraProjection M) (a : Algebra M)
    (hp : p.val.val (modularQuadratic J a η) = 0) : p.val.val (a.val η) = 0 := by
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp (hright p.val) p.val.val p.val.property
  have hz : modularQuadratic J (p.val*a) η = 0 := by
    rw [← modularQuadratic_mul J hJ hright]
    change (p.val.val * conjugationOperator J p.val.val) (modularQuadratic J a η) = 0
    rw [hc]
    change conjugationOperator J p.val.val (p.val.val (modularQuadratic J a η)) = 0
    rw [hp,map_zero]
  exact positiveCone_operator_kills_of_quadratic_kills J hJ hright ξ hξ hpos hη (p.val*a) hz

include hJ hright hξ hpos in
theorem matrixCentralProjection_separating
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (E : MatrixUnitSystem ι (Algebra M)) {η : H}
    (hη : η ∈ modularPositiveCone (M := M) J ξ)
    (hsep : Function.Injective (algebraVectorMap M η)) :
    Function.Injective (algebraVectorMap M
      ((centralVectorSpace (matrixUnitConcreteAlgebra E) J).starProjection η)) := by
  let ζ := (centralVectorSpace (matrixUnitConcreteAlgebra E) J).starProjection η
  have hpzero (p : AlgebraProjection M) (hp : p.val.val ζ = 0) : p.val = 0 := by
    have hsum : p.val.val (∑ i, ∑ j, modularQuadratic J (E.entry i j) η) = 0 := by
      change p.val.val ((centralVectorSpace (matrixUnitConcreteAlgebra E) J).starProjection η) = 0 at hp
      rw [matrixCentralProjection_eq E J hJ hright] at hp
      change p.val.val ((Fintype.card ι : ℂ)⁻¹ •
        ((∑ i, ∑ j, (E.entry i j).val * conjugationOperator J (E.entry i j).val) η)) = 0 at hp
      simp only [map_smul,sum_apply] at hp
      exact (smul_eq_zero.mp hp).resolve_left
        (inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
    have hkill := positiveCone_projection_kills_sum J hJ hright ξ hξ hpos Finset.univ
      (fun i => ∑ j, modularQuadratic J (E.entry i j) η)
      (fun i _ => modularPositiveCone_sum_mem J ξ Finset.univ _
        (fun j _ => modularQuadratic_preserves_positiveCone J hJ hright ξ _ hη)) p hsum
    have hdiag (i : ι) : p.val * E.entry i i = 0 := by
      have hk := positiveCone_projection_kills_sum J hJ hright ξ hξ hpos Finset.univ
        (fun j => modularQuadratic J (E.entry i j) η)
        (fun j _ => modularQuadratic_preserves_positiveCone J hJ hright ξ _ hη)
        p (hkill i (Finset.mem_univ i)) i (Finset.mem_univ i)
      have hv := positiveCone_projection_kills_quadratic J hJ hright ξ hξ hpos hη p _ hk
      exact hsep (hv.trans (map_zero (algebraVectorMap M η)).symm)
    calc
      p.val = p.val * 1 := (mul_one _).symm
      _ = ∑ i, p.val * E.entry i i := by rw [← E.total,Finset.mul_sum]
      _ = 0 := by simp only [hdiag,Finset.sum_const_zero]
  let q := vectorSupportProjection M ζ
  let p : AlgebraProjection M := ⟨1 - q.val,q.property.one_sub⟩
  have hp : p.val.val ζ = 0 := by
    change ζ - q.val.val ζ = 0
    rw [vectorSupportProjection_apply,sub_self]
  have hq : q.val = 1 := (sub_eq_zero.mp (hpzero p hp)).symm
  intro a b hab
  have hm := mul_vectorSupport_eq_zero M ζ (a-b) (sub_eq_zero.mpr hab)
  change (a-b).val * q.val.val = 0 at hm
  rw [hq,OneMemClass.coe_one,mul_one] at hm
  exact sub_eq_zero.mp (Subtype.ext hm)

end

end KadisonKastler

end OAI
