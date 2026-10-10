import OAI.Analysis.KadisonKastler.PointedPowerConfigurations

namespace OAI

/-! # Local operators on the configuration Hilbert space

Finite matrix coefficients act on one configuration coordinate. The
construction is a star homomorphism, so the local matrix-unit relations
hold as actual bounded operator identities.
-/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

section FiniteAmplification

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def finiteLocalCoefficient (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (i j : ι) : ℂ := A (EuclideanSpace.single j 1) i

private theorem finiteLocalCoefficient_mul
    (A B : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (i j : ι) :
    finiteLocalCoefficient (A * B) i j =
      ∑ k, finiteLocalCoefficient A i k * finiteLocalCoefficient B k j := by
  have h := tuple_eq_sum_single (B (EuclideanSpace.single j 1))
  change A (B (EuclideanSpace.single j 1)) i = _
  rw [h, map_sum]
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  have he : tupleSingle k (B (EuclideanSpace.single j 1) k) =
      (B (EuclideanSpace.single j 1) k) • EuclideanSpace.single k 1 := by
    ext l
    simp [tupleSingle_apply, Pi.single_apply]
  rw [he, map_smul]
  simp only [finiteLocalCoefficient, PiLp.smul_apply, smul_eq_mul, mul_comm]

private theorem finiteLocalCoefficient_star
    (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) (i j : ι) :
    finiteLocalCoefficient (star A) i j = star (finiteLocalCoefficient A j i) := by
  change (star A) (EuclideanSpace.single j 1) i = _
  rw [← EuclideanSpace.basisFun_inner]
  simp only [EuclideanSpace.basisFun_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  rw [← inner_conj_symm, ← EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_inner]
  rfl

def finiteLocalAmplificationValue
    (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :
    FiniteHilbert ι E →L[ℂ] FiniteHilbert ι E :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => E)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i =>
      ∑ j, (finiteLocalCoefficient A i j) • PiLp.proj 2 (fun _ : ι => E) j)

omit [CompleteSpace E] in
@[simp] theorem finiteLocalAmplificationValue_apply
    (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (x : FiniteHilbert ι E) (i : ι) :
    finiteLocalAmplificationValue A x i = ∑ j, finiteLocalCoefficient A i j • x j := by
  simp [finiteLocalAmplificationValue]

/-- Amplification of a finite-dimensional operator by an identity. -/
def finiteLocalAmplification :
    (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) →⋆ₐ[ℂ]
      (FiniteHilbert ι E →L[ℂ] FiniteHilbert ι E) where
  toFun := finiteLocalAmplificationValue
  map_zero' := by
    ext x i
    simp [finiteLocalCoefficient]
  map_one' := by
    ext x i
    simp [finiteLocalCoefficient]
  map_add' A B := by
    ext x i
    simp [finiteLocalCoefficient, add_smul, Finset.sum_add_distrib]
  map_mul' A B := by
    ext x i
    simp only [finiteLocalAmplificationValue_apply, finiteLocalCoefficient_mul,
      mul_apply_eq_comp, Finset.sum_smul, Finset.smul_sum, mul_smul]
    rw [Finset.sum_comm]
  commutes' z := by
    ext x i
    simp [finiteLocalCoefficient]
  map_star' A := by
    change finiteLocalAmplificationValue (star A) = star (finiteLocalAmplificationValue A)
    rw [ContinuousLinearMap.star_eq_adjoint (finiteLocalAmplificationValue (E := E) A)]
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    simp only [PiLp.inner_apply, finiteLocalAmplificationValue_apply,
      inner_sum, sum_inner, inner_smul_left, inner_smul_right,
      finiteLocalCoefficient_star, starRingEnd_apply, star_star]
    rw [Finset.sum_comm]

@[simp] theorem finiteLocalAmplification_apply
    (A : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)
    (x : FiniteHilbert ι E) (i : ι) :
    finiteLocalAmplification (ι := ι) (E := E) A x i = ∑ j, finiteLocalCoefficient A i j • x j :=
  finiteLocalAmplificationValue_apply A x i

end FiniteAmplification

/-- Apply a four-dimensional operator at one site of the Hilbert product. -/
def pointedPowerOperator (i : ℕ) :
    (EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4)) →⋆ₐ[ℂ]
      (PointedPowerHilbert →L[ℂ] PointedPowerHilbert) :=
  (pointedPowerFibreEquiv i).symm.conjStarAlgEquiv.toStarAlgHom.comp
    (finiteLocalAmplification (E := PointedPowerTailHilbert i))

theorem pointedPowerOperator_basis (i : ℕ)
    (A : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4))
    (f : PointedPowerConfiguration) :
    pointedPowerOperator i A (pointedPowerBasis f) =
      ∑ k : Fin 4, finiteLocalCoefficient A k (f i) •
        pointedPowerBasis (f.update i k) := by
  apply (pointedPowerFibreEquiv i).injective
  change (pointedPowerFibreEquiv i)
      ((pointedPowerFibreEquiv i).symm
        (finiteLocalAmplification (ι := Fin 4) (E := PointedPowerTailHilbert i) A
          ((pointedPowerFibreEquiv i) (pointedPowerBasis f)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rw [pointedPowerFibreEquiv_basis, map_sum]
  simp only [map_smul, pointedPowerFibreEquiv_basis,
    Finsupp.update_apply, ite_eq_left, Finsupp.erase_update_eq_erase]
  apply PiLp.ext
  intro k
  simp [finiteLocalAmplification_apply, tupleSingle_apply, Pi.single_apply,
    apply_ite, Finset.sum_ite_eq', Finset.sum_ite_eq]

/-- Operators on different sites commute, with no condition on their matrices. -/
theorem pointedPowerOperator_commute {i j : ℕ} (hij : i ≠ j)
    (A B : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4)) :
    Commute (pointedPowerOperator i A) (pointedPowerOperator j B) := by
  change pointedPowerOperator i A * pointedPowerOperator j B =
    pointedPowerOperator j B * pointedPowerOperator i A
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro f
  apply ContinuousLinearMap.ext
  intro c
  change (pointedPowerOperator i A) ((pointedPowerOperator j B) (lp.single 2 f c)) =
    (pointedPowerOperator j B) ((pointedPowerOperator i A) (lp.single 2 f c))
  have hsingle : (lp.single 2 f c : PointedPowerHilbert) = c • pointedPowerBasis f := by
    simp only [pointedPowerBasis, ← lp.single_smul, smul_eq_mul, mul_one]
  rw [hsingle]
  simp only [map_smul, pointedPowerOperator_basis,
    map_sum, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  simp only [Finsupp.update_apply, ite_eq_right hij, ite_eq_right (Ne.symm hij)]
  rw [Finsupp.update_comm f hij k l]
  congr 1
  ring

end

end KadisonKastler

end OAI
