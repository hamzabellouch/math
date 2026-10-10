import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalizedGroupLaws
import OAI.GroupTheory.PolycyclicRecognition.Algebra.GeneratorConjugation

namespace OAI

/-! # Conjugation identities persist under coordinate limits

The exponential of the coordinate adjoint is the genuine logarithmic
conjugation map. This identity is closed in the bracket parameter and will
identify the columns of the limiting generator endpoint map.
-/

noncomputable section

namespace PolycyclicRecognition

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- The usual adjoint-exponential identity written entirely in fixed
coordinates. -/
def ExponentialConjugationLaw (m : V → V → V) (B : V →L[ℝ] V →L[ℝ] V) : Prop :=
  ∀ x y (t : ℝ), m (m (t • x) y) (-(t • x)) =
    NormedSpace.exp (t • B x) y

/-- The logarithmic conjugation identity is a closed condition. -/
theorem isClosed_exponentialConjugationLaw {c : ℕ} (a : DynkinCoefficients c 2) :
    IsClosed {B : V →L[ℝ] V →L[ℝ] V |
      ExponentialConjugationLaw (dynkinProduct a B) B} := by
  let : NormedAlgebra ℚ (V →L[ℝ] V) := NormedAlgebra.restrictScalars ℚ ℝ _
  simp only [ExponentialConjugationLaw, Set.ofPred_forall]
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro y
  apply isClosed_iInter
  intro t
  have hc : Continuous (fun B : V →L[ℝ] V →L[ℝ] V =>
      dynkinProduct a B (t • x) y) :=
    continuous_dynkinProduct (V := V) a id _ _ continuous_id continuous_const continuous_const
  apply isClosed_eq
  · exact continuous_dynkinProduct (V := V) a id _ _
      continuous_id hc continuous_const
  · exact (NormedSpace.exp_continuous.comp
      ((ContinuousLinearMap.apply ℝ (V →L[ℝ] V) x).continuous.const_smul t)).clm_apply
        continuous_const

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]

local instance coordinateConjugationNormedAddCommGroup : NormedAddCommGroup L :=
  NormedAddCommGroup.induced _ _ (Module.finBasis ℝ L).equivFun.toLinearMap
    (Module.finBasis ℝ L).equivFun.injective
local instance coordinateConjugationNormedSpace : NormedSpace ℝ L :=
  NormedSpace.induced ℝ _ _ (Module.finBasis ℝ L).equivFun.toLinearMap

/-- Coordinate change intertwines actual adjoint exponentials. -/
theorem basis_exp_adjoint {n : ℕ} (b : Module.Basis (Fin n) ℝ L)
    (x y : L) (t : ℝ) :
    b.equivFun (NormedSpace.exp (t • continuousAd x) y) =
      NormedSpace.exp (t • basisBracket b (b.equivFun x)) (b.equivFun y) := by
  let f : L →L[ℝ] (Fin n → ℝ) := b.equivFun.toContinuousLinearEquiv
  apply exp_intertwine_apply f
  intro z
  change b.equivFun (t • ⁅x, z⁆) =
    t • b.equivFun ⁅b.equivFun.symm (b.equivFun x), b.equivFun.symm (b.equivFun z)⁆
  simp only [map_smul, LinearEquiv.symm_apply_apply]

variable {G A : Type*} [Group G] [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The representation-derived conjugation formula transports to every
coordinate basis with the same binary Dynkin coefficients. -/
theorem basis_exponentialConjugationLaw {n c : ℕ} (b : Module.Basis (Fin n) ℝ L)
    (Exp : L → G) (hinj : Function.Injective Exp)
    (hneg : ∀ x, Exp (-x) = (Exp x)⁻¹)
    (a : DynkinCoefficients c 2)
    (hm : ∀ x y, Exp (finiteDynkinPolynomial a ![x, y]) = Exp x * Exp y)
    (j : L →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (hmatch : ∀ x, ρ (Exp x) = algebraExpUnit (j x)) :
    ExponentialConjugationLaw (dynkinProduct a (basisBracket b)) (basisBracket b) := by
  have hp (x y : Fin n → ℝ) :
      Exp (b.equivFun.symm (dynkinProduct a (basisBracket b) x y)) =
        Exp (b.equivFun.symm x) * Exp (b.equivFun.symm y) := by
    have he := basis_dynkinProduct b a (b.equivFun.symm x) (b.equivFun.symm y)
    simp only [LinearEquiv.apply_symm_apply] at he
    rw [he, LinearEquiv.symm_apply_apply, hm]
  intro x y t
  apply hinj.comp b.equivFun.symm.injective
  change Exp (b.equivFun.symm _) = Exp (b.equivFun.symm _)
  rw [hp, hp, map_neg, hneg, map_smul]
  have hc := basis_exp_adjoint b (b.equivFun.symm x) (b.equivFun.symm y) t
  simp only [LinearEquiv.apply_symm_apply] at hc
  have he := congrArg b.equivFun.symm hc
  simp only [LinearEquiv.symm_apply_apply] at he
  rw [← he]
  exact (exp_ad_eq_group_conjugation Exp j ρ hρ hmatch _ _ t).symm

end PolycyclicRecognition

end

end OAI
