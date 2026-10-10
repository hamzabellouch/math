import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKubotaConjugation
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

namespace OAI

/-! Invariance under the whole integer modular group, derived from its
proved S,T generation and the two explicit reciprocity calculations. -/
noncomputable section
open scoped MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaKubotaConjugate_one (g : cubicThetaPrincipalGroup) :
    cubicThetaKubotaConjugate 1 g = g := by
  apply Subtype.ext
  simp [cubicThetaKubotaConjugate]

lemma cubicThetaKubotaConjugate_mul (u v : SL(2,Eisenstein)) (g : cubicThetaPrincipalGroup) :
    cubicThetaKubotaConjugate (u*v) g =
      cubicThetaKubotaConjugate u (cubicThetaKubotaConjugate v g) := by
  apply Subtype.ext
  simp [cubicThetaKubotaConjugate,mul_assoc]

lemma cubicThetaKubotaConjugate_inverse (u : SL(2,Eisenstein)) (g : cubicThetaPrincipalGroup) :
    cubicThetaKubotaConjugate u (cubicThetaKubotaConjugate u⁻¹ g) = g := by
  rw [←cubicThetaKubotaConjugate_mul,mul_inv_cancel,cubicThetaKubotaConjugate_one]

def cubicThetaKubotaPreservers : Subgroup SL(2,Eisenstein) where
  carrier := {u | ∀ g : cubicThetaPrincipalGroup,
    cubicThetaKubotaValue (cubicThetaKubotaConjugate u g) = cubicThetaKubotaValue g}
  one_mem' := by intro g; rw [cubicThetaKubotaConjugate_one]
  mul_mem' := by
    intro u v hu hv g
    rw [cubicThetaKubotaConjugate_mul,hu,hv]
  inv_mem' := by
    intro u hu g
    have he := hu (cubicThetaKubotaConjugate u⁻¹ g)
    rw [cubicThetaKubotaConjugate_inverse] at he
    exact he.symm

def cubicThetaIntegerEmbedding : SL(2,ℤ) →* SL(2,Eisenstein) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom Eisenstein)

lemma cubicThetaIntegerEmbedding_S :
    cubicThetaIntegerEmbedding ModularGroup.S = cubicThetaModularS := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  change ((ModularGroup.S i j:ℤ):Eisenstein) = cubicThetaModularS i j
  fin_cases i <;> fin_cases j <;> norm_num [ModularGroup.S,cubicThetaModularS]

lemma cubicThetaIntegerEmbedding_T :
    cubicThetaIntegerEmbedding ModularGroup.T = cubicThetaModularT := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  change ((ModularGroup.T i j:ℤ):Eisenstein) = cubicThetaModularT i j
  fin_cases i <;> fin_cases j <;> norm_num [ModularGroup.T,cubicThetaModularT]

theorem cubicThetaKubotaValue_conjugate_integer (u : SL(2,ℤ)) (g : cubicThetaPrincipalGroup) :
    cubicThetaKubotaValue (cubicThetaKubotaConjugate (cubicThetaIntegerEmbedding u) g) =
      cubicThetaKubotaValue g := by
  have hgen : Subgroup.closure {ModularGroup.S,ModularGroup.T} ≤
      cubicThetaKubotaPreservers.comap cubicThetaIntegerEmbedding := by
    apply (Subgroup.closure_le _).mpr
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · change ∀ g, cubicThetaKubotaValue (cubicThetaKubotaConjugate
        (cubicThetaIntegerEmbedding ModularGroup.S) g) = cubicThetaKubotaValue g
      rw [cubicThetaIntegerEmbedding_S]
      exact cubicThetaKubotaValue_conjugate_S
    · have haT : a = ModularGroup.T := Set.mem_singleton_iff.mp ha
      subst a
      change ∀ g, cubicThetaKubotaValue (cubicThetaKubotaConjugate
        (cubicThetaIntegerEmbedding ModularGroup.T) g) = cubicThetaKubotaValue g
      rw [cubicThetaIntegerEmbedding_T]
      exact cubicThetaKubotaValue_conjugate_T
  have hu : u ∈ Subgroup.closure {ModularGroup.S,ModularGroup.T} := by
    rw [SpecialLinearGroup.SL2Z_generators]
    trivial
  exact hgen hu g

theorem cubicThetaKubotaValue_integer (g : cubicThetaPrincipalGroup) (u : SL(2,ℤ))
    (hu : g.val = cubicThetaIntegerEmbedding u) : cubicThetaKubotaValue g = 1 := by
  apply cubicThetaKubotaValue_real
  · rw [hu]
    change conjugate ((u 0 0:ℤ):Eisenstein) = ((u 0 0:ℤ):Eisenstein)
    simp
  · rw [hu]
    change conjugate ((u 1 0:ℤ):Eisenstein) = ((u 1 0:ℤ):Eisenstein)
    simp

end CubicFirstMoment

end

end OAI
