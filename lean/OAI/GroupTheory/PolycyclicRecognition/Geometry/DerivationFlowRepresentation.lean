import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentDerivationFlow
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AnalyticNilpotentExponential
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AlgebraExponential
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace OAI

/-! # Representing a nilpotent derivation flow by conjugation

Only the given intertwining identity is used. The target operator need not
be nilpotent outside the image of the intertwiner.
-/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

local instance derivationFlowRepresentationRat : Module ℚ L :=
  Module.compHom L (algebraMap ℚ ℝ)

theorem nilpotentDerivationFlow_eq_analytic (t : ℝ) (x : L) :
    nilpotentDerivationFlow D hD t x =
      NormedSpace.exp (t • D.toLinearMap.toContinuousLinearMap) x := by
  let d := D.toLinearMap.toContinuousLinearMap
  have hd : IsNilpotent d := by
    obtain ⟨k, hk⟩ := hD
    refine ⟨k, ?_⟩
    ext y
    have he : (d ^ k).toLinearMap = D.toLinearMap ^ k :=
      map_pow ContinuousLinearMap.toLinearMapRingHom d k
    have hy := congrArg (fun f : L →ₗ[ℝ] L => f y) he
    rw [hk] at hy
    exact hy
  let : NormedAlgebra ℚ (L →L[ℝ] L) := NormedAlgebra.restrictScalars ℚ ℝ _
  rw [analytic_exp_eq_nilpotent_exp (hd.smul t)]
  have he := (hd.smul t).map_exp ContinuousLinearMap.toLinearMapRingHom
  exact (congrArg (fun f : L →ₗ[ℝ] L => f x) he).symm

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem derivationFlow_representation (f : L →ₗ[ℝ] A) (a : A)
    (hf : ∀ x, f (D x) = a * f x - f x * a) (t : ℝ) (x : L) :
    f (nilpotentDerivationFlow D hD t x) =
      NormedSpace.exp (t • a) * f x * NormedSpace.exp (-(t • a)) := by
  rw [nilpotentDerivationFlow_eq_analytic]
  have he := exp_intertwine_apply f.toContinuousLinearMap
    (t • D.toLinearMap.toContinuousLinearMap) (t • adjointOperator a)
    (by
      intro y
      change f (t • D y) = t • (a * f y - f y * a)
      rw [map_smul, hf]) x
  exact he.trans (exp_smul_adjointOperator_apply t a (f x))

variable {G T : Type*} [Group G] [LieRing T] [LieAlgebra ℝ T]
attribute [local instance 100] LieRing.ofAssociativeRing

theorem derivationFlow_group_conjugation (Exp : T → G) (ρ : G →* Aˣ)
    (hρ : Function.Injective ρ) (j : T →ₗ⁅ℝ⁆ A)
    (hexp : ∀ v, ρ (Exp v) = algebraExpUnit (j v))
    (f : L →ₗ[ℝ] T) (u : T) (hf : ∀ x, f (D x) = ⁅u, f x⁆)
    (t : ℝ) (x : L) :
    Exp (f (nilpotentDerivationFlow D hD t x)) =
      Exp (t • u) * Exp (f x) * (Exp (t • u))⁻¹ := by
  have he := derivationFlow_representation D hD (j.toLinearMap.comp f) (j u)
    (by intro y; change j (f (D y)) = _; rw [hf, j.map_lie]; rfl) t x
  apply hρ
  rw [map_mul, map_mul, map_inv, hexp, hexp, hexp, map_smul]
  rw [show j (f (nilpotentDerivationFlow D hD t x)) =
    (algebraExpUnit (t • j u) : A) * j (f x) *
      ((algebraExpUnit (t • j u))⁻¹ : Aˣ) from he]
  exact algebraExpUnit_conj _ _

end PolycyclicRecognition

end

end OAI
