import OAI.GroupTheory.PolycyclicRecognition.Geometry.AnalyticDerivationAction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CommutingLiePowerLogarithms

namespace OAI

/-! # Smooth vector actions from commuting derivations -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance] LieRing.ofAssociativeRing
variable {L I : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L] [Fintype I]

def derivationCombination (D : I → LieDerivation ℝ L L) (v : I → ℝ) :
    LieDerivation ℝ L L := ∑ i, v i • D i

omit [FiniteDimensional ℝ L] in
theorem derivationCombination_basis (D : I → LieDerivation ℝ L L) (i : I) :
    derivationCombination D ((Pi.basisFun ℝ I) i) = D i := by
  classical
  simp [derivationCombination, Pi.basisFun_apply]

omit [FiniteDimensional ℝ L] in
theorem derivationCombination_zero (D : I → LieDerivation ℝ L L) :
    derivationCombination D 0 = 0 := by simp [derivationCombination]

omit [FiniteDimensional ℝ L] in
theorem derivationCombination_add (D : I → LieDerivation ℝ L L) (s t : I → ℝ) :
    derivationCombination D (s + t) = derivationCombination D s + derivationCombination D t := by
  simp only [derivationCombination, Pi.add_apply, add_smul, Finset.sum_add_distrib]

omit [FiniteDimensional ℝ L] in
theorem derivationCombination_commute (D : I → LieDerivation ℝ L L)
    (hD : ∀ i j, Commute (D i).toLinearMap (D j).toLinearMap) (s t : I → ℝ) :
    Commute (derivationCombination D s).toLinearMap (derivationCombination D t).toLinearMap := by
  let f := (LieDerivation.toLinearMapLieHom ℝ L).toLinearMap
  change Commute (f (∑ i, s i • D i)) (f (∑ i, t i • D i))
  simp only [map_sum, map_smul]
  apply Commute.sum_left
  intro i _
  apply Commute.sum_right
  intro j _
  exact ((hD i j).smul_left (s i)).smul_right (t j)

theorem analyticDerivationCombination_add (D : I → LieDerivation ℝ L L)
    (hD : ∀ i j, Commute (D i).toLinearMap (D j).toLinearMap) (s t : I → ℝ) (x : L) :
    analyticDerivationExp (derivationCombination D (s + t)) x =
      analyticDerivationExp (derivationCombination D s)
        (analyticDerivationExp (derivationCombination D t) x) := by
  let E := Module.End.toContinuousLinearMap (𝕜 := ℝ) L
  let := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  have hc : Commute (E (derivationCombination D s).toLinearMap)
      (E (derivationCombination D t).toLinearMap) :=
    (derivationCombination_commute D hD s t).map E.toRingHom
  simp only [analyticDerivationExp_apply, derivationCombination_add]
  change NormedSpace.exp (E ((derivationCombination D s).toLinearMap +
      (derivationCombination D t).toLinearMap)) x = _
  rw [map_add, NormedSpace.exp_add_of_commute hc]
  rfl

theorem continuousLinear_derivationCombination (D : I → LieDerivation ℝ L L) (v : I → ℝ) :
    LinearMap.toContinuousLinearMap (derivationCombination D v).toLinearMap =
      ∑ i, v i • LinearMap.toContinuousLinearMap (D i).toLinearMap := by
  let f := (Module.End.toContinuousLinearMap (𝕜 := ℝ) L).toLinearMap.comp
    (LieDerivation.toLinearMapLieHom ℝ L).toLinearMap
  change f (∑ i, v i • D i) = _
  simp only [map_sum, map_smul]
  rfl

theorem contDiff_analyticDerivationCombination (D : I → LieDerivation ℝ L L) :
    ContDiff ℝ ⊤ (fun p : (I → ℝ) × L =>
      analyticDerivationExp (derivationCombination D p.1) p.2) := by
  have he : ContDiff ℝ ⊤ (NormedSpace.exp : (L →L[ℝ] L) → (L →L[ℝ] L)) :=
    contDiff_iff_contDiffAt.mpr fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  have ht : ContDiff ℝ ⊤ (fun p : (I → ℝ) × L =>
      ∑ i, p.1 i • LinearMap.toContinuousLinearMap (D i).toLinearMap) :=
    ContDiff.sum fun i _ => ((contDiff_apply ℝ ℝ i).comp contDiff_fst).smul_const _
  simp only [analyticDerivationExp_apply, continuousLinear_derivationCombination]
  exact (he.comp ht).clm_apply contDiff_snd

namespace PolynomialExponentialCoordinates
variable [P : PolynomialExponentialCoordinates L]

def commutingDerivationAction (D : I → LieDerivation ℝ L L)
    (hD : ∀ i j, Commute (D i).toLinearMap (D j).toLinearMap) :
    Multiplicative (I → ℝ) →* MulAut L where
  toFun t := groupAutomorphism (P := P) (analyticDerivationExp (derivationCombination D t.toAdd))
  map_one' := by
    apply DFunLike.ext
    intro x
    change analyticDerivationExp (derivationCombination D 0) x = x
    rw [derivationCombination_zero, analyticDerivationExp_apply]
    change NormedSpace.exp (0 : L →L[ℝ] L) x = x
    rw [NormedSpace.exp_zero]
    rfl
  map_mul' s t := by
    apply DFunLike.ext
    intro x
    exact analyticDerivationCombination_add D hD s.toAdd t.toAdd x

theorem commutingDerivationAction_smooth (D : I → LieDerivation ℝ L L)
    (hD : ∀ i j, Commute (D i).toLinearMap (D j).toLinearMap) :
    ContDiff ℝ ⊤ (fun p : (I → ℝ) × L =>
      commutingDerivationAction (P := P) D hD (Multiplicative.ofAdd p.1) p.2) :=
  contDiff_analyticDerivationCombination D

end PolynomialExponentialCoordinates
end PolycyclicRecognition

end

end OAI
