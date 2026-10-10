import OAI.GroupTheory.PolycyclicRecognition.Lattices.NilshadowHeight
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FixedLogQuotient
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CommutingDerivationAction
import OAI.GroupTheory.PolycyclicRecognition.Lattices.IntegralLatticePowerIndex

namespace OAI

/-! # The real nilshadow action preserves the actual height

The logarithms vanish on the fixed quotient section. Commutation with its
projection therefore forces the complete real action to preserve height,
not merely its integral-time values.
-/

noncomputable section
namespace PolycyclicRecognition.IntegralNilshadowData
open scoped Manifold ContDiff
attribute [local instance] LieRing.ofAssociativeRing
variable {L G : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [Group G] {n : ℕ}
  {E : GroupExtension L G (IntegralLatticeGroup n)} (D : IntegralNilshadowData E)

theorem exists_real_action :
    ∃ m : ℕ, 0 < m ∧ ∃ φ : Multiplicative (Fin n → ℝ) →* MulAut D.completion.carrier,
      ContDiff ℝ ⊤ (fun p : (Fin n → ℝ) × D.completion.carrier =>
        φ (Multiplicative.ofAdd p.1) p.2) ∧
      (∀ z x, D.completedAction (latticePowerHom n m z) x = φ (integerVectorHom n z) x) ∧
      (∀ v x, D.height (φ v x) = D.height x) ∧
      ∀ v w, φ v (D.quotientSection w) = D.quotientSection w := by
  let A := fun i : Fin n => D.completedLieAction (integralLatticeGenerator n i)
  have hA (i j : Fin n) : Commute (A i).toLinearMap (A j).toLinearMap := by
    apply LinearMap.ext
    intro x
    change A i (A j x) = A j (A i x)
    simp only [A, completedLieAction, polynomialModelLieEquiv_apply]
    exact DFunLike.congr_fun
      (((show Commute (integralLatticeGenerator n i) (integralLatticeGenerator n j)
        from Commute.all _ _).map D.completedAction).eq) x
  obtain ⟨m, hm, B, he, hc, hcomm, hfixed⟩ :=
    commuting_lie_automorphisms_have_fixed_power_logs A hA
  let φ := PolynomialExponentialCoordinates.commutingDerivationAction B hc
  have hp (i : Fin n) : D.heightProjection * (B i).toLinearMap = 0 :=
    fixed_log_projection_zero (A i) (B i) (hcomm i) (hfixed i) D.heightProjection
      (D.completedLieAction_projection _) (D.projection_completedLieAction _)
  have hbp (i : Fin n) : (B i).toLinearMap * D.heightProjection = 0 := by
    apply LinearMap.ext
    intro x
    exact hfixed i _ (D.completedLieAction_projection _ x)
  have hprod (i : Fin n) (k : ℕ) (x : D.completion.carrier) :
      ((A i).toLinearMap ^ k) x = D.completedAction ((integralLatticeGenerator n i) ^ k) x := by
    induction k generalizing x with
    | zero => simp only [pow_zero, map_one, Module.End.one_apply, MulAut.one_apply]
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', map_mul]
      exact polynomialModelLieEquiv_apply _ _ _
  have hhom : φ.comp (integerVectorHom n) = D.completedAction.comp (latticePowerHom n m) := by
    apply integralLattice_hom_ext
    intro i
    apply DFunLike.ext
    intro x
    change analyticDerivationExp
      (derivationCombination B (integerVectorMap n ((Pi.basisFun ℤ (Fin n)) i))) x =
        D.completedAction ((integralLatticeGenerator n i) ^ m) x
    rw [integerVectorMap_basis, derivationCombination_basis, analyticDerivationExp_apply]
    exact (DFunLike.congr_fun (he i) x).trans (hprod i m x)
  refine ⟨m, hm, φ, PolynomialExponentialCoordinates.commutingDerivationAction_smooth B hc,
    fun z x => (congrArg (fun F : IntegralLatticeGroup n →* MulAut D.completion.carrier => F z x)
      hhom).symm, ?_⟩
  constructor
  · intro v x
    have hpv : D.heightProjection * (derivationCombination B v.toAdd).toLinearMap = 0 := by
      let F := (LieDerivation.toLinearMapLieHom ℝ D.completion.carrier).toLinearMap
      change D.heightProjection * F (∑ i, v.toAdd i • B i) = 0
      simp only [map_sum, map_smul, Finset.mul_sum, mul_smul_comm]
      change (∑ i, v.toAdd i • (D.heightProjection * (B i).toLinearMap)) = 0
      simp only [hp, smul_zero, Finset.sum_const_zero]
    rw [← D.heightLinear_apply, ← D.heightLinear_apply]
    exact exp_preserves_projected_quotient _ _ hpv D.heightLinear D.heightLinear_projection x
  · intro v w
    have hpv : (derivationCombination B v.toAdd).toLinearMap * D.heightProjection = 0 := by
      let F := (LieDerivation.toLinearMapLieHom ℝ D.completion.carrier).toLinearMap
      change F (∑ i, v.toAdd i • B i) * D.heightProjection = 0
      simp only [map_sum, map_smul, Finset.sum_mul, smul_mul_assoc]
      change (∑ i, v.toAdd i • ((B i).toLinearMap * D.heightProjection)) = 0
      simp only [hbp, smul_zero, Finset.sum_const_zero]
    have hpw : D.heightProjection (D.quotientSection w) = D.quotientSection w := by
      change D.quotientSection (D.heightLinear (D.quotientSection w)) = _
      rw [D.heightLinear_section]
    have h := exp_fixes_projection _ _ hpv (D.quotientSection w)
    rw [hpw] at h
    exact h

end PolycyclicRecognition.IntegralNilshadowData

end

end OAI
