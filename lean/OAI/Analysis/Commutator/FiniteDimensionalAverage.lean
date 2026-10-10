import Mathlib
import OAI.Analysis.Commutator.Average
import OAI.Analysis.Commutator.CompactAverage
import OAI.Analysis.Commutator.MainMatrix
import OAI.Analysis.Commutator.UnitaryHaar

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap MeasureTheory

universe u

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def algebraUnitaryLift (P : VonNeumannAlgebra K) : unitary P →* unitary (K →L[ℂ] K) where
  toFun v := ⟨((v:P):K →L[ℂ] K),Unitary.map_mem P.toStarSubalgebra.subtype v.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def algebraUnitaryRepresentation (P : VonNeumannAlgebra K) : unitary P →* (K ≃ₗᵢ[ℂ] K) :=
  Unitary.linearIsometryEquiv.toMonoidHom.comp
    (algebraUnitaryLift P)

@[simp] lemma algebraUnitaryRepresentation_coe (P : VonNeumannAlgebra K) (v : unitary P) :
    (algebraUnitaryRepresentation P v : K →L[ℂ] K)=((v:P):K →L[ℂ] K) := rfl

lemma algebraUnitaryRepresentation_continuous (P : VonNeumannAlgebra K) (x : K) :
    Continuous fun v : unitary P => algebraUnitaryRepresentation P v x := by
  change Continuous fun v : unitary P => ((v:P):K →L[ℂ] K) x
  exact (continuous_subtype_val.comp continuous_subtype_val).clm_apply continuous_const

lemma commutes_algebra_of_commutes_unitaries (P : VonNeumannAlgebra K) (T : K →L[ℂ] K)
    (hT : ∀ v : unitary P,T*((v:P):K →L[ℂ] K)=((v:P):K →L[ℂ] K)*T) :
    ∀ a : P,T*(a:K →L[ℂ] K)=(a:K →L[ℂ] K)*T := by
  have hz : innerDerivation P T=0 := by
    apply ContinuousLinearMap.coe_injective
    apply LinearMap.ext_on (CStarAlgebra.span_unitary P)
    intro v hv
    exact sub_eq_zero.mpr (hT ⟨v,hv⟩)
  intro a
  exact sub_eq_zero.mp (congrArg (fun f : P →L[ℂ] (K →L[ℂ] K) => f a) hz)

lemma unitary_conjugate_distance (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) (v : unitary P) :
    ‖CompactAverage.conjugate (algebraUnitaryRepresentation P) Y v-Y‖≤commutatorSeminorm P Y := by
  let w : unitary (K →L[ℂ] K) := algebraUnitaryLift P v
  have he : CompactAverage.conjugate (algebraUnitaryRepresentation P) Y v-Y=
      (((w:K →L[ℂ] K)*Y-Y*(w:K →L[ℂ] K))*star (w:K →L[ℂ] K)) := by
    change (w:K →L[ℂ] K)*Y*star (w:K →L[ℂ] K)-Y=_
    rw [sub_mul,mul_assoc Y (w:K →L[ℂ] K) (star (w:K →L[ℂ] K)),w.property.2,mul_one]
  rw [he]
  rw [CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem w.property), norm_sub_rev]
  apply commutator_bound_unitball P Y (v:P).property
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖(w:K →L[ℂ] K) x‖≤1*‖x‖
  rw [one_mul]
  exact (Unitary.norm_map w x).le

theorem finiteDimensional_commutant_approximation (P : VonNeumannAlgebra K)
    [FiniteDimensional ℂ P] (Y : K →L[ℂ] K) :
    ∃ Y₀ : K →L[ℂ] K, (∀ a : P,Y₀*(a:K →L[ℂ] K)=(a:K →L[ℂ] K)*Y₀) ∧
      ‖Y-Y₀‖≤commutatorSeminorm P Y := by
  cases subsingleton_or_nontrivial K with
  | inl h =>
    exact ⟨Y,fun a => Subsingleton.elim _ _,by simpa using commutatorSeminorm_nonneg P Y⟩
  | inr h =>
    let := UnitaryHaar.compactUnitary P
    let : MeasurableSpace (unitary P) := borel (unitary P)
    let : BorelSpace (unitary P) := ⟨rfl⟩
    let U := algebraUnitaryRepresentation P
    have hU := algebraUnitaryRepresentation_continuous P
    let μ := UnitaryHaar.probability (unitary P)
    obtain ⟨Y₀,_,hc,hcoeff⟩ := CompactAverage.exists_average U hU Y μ
    refine ⟨Y₀,commutes_algebra_of_commutes_unitaries P Y₀ hc,?_⟩
    rw [norm_sub_rev]
    apply WeakOperatorIntegral.difference_norm μ (CompactAverage.conjugate U Y) _ Y₀ hcoeff Y
      (commutatorSeminorm_nonneg P Y) (unitary_conjugate_distance P Y)
    intro x y
    exact ((CompactAverage.conjugate_continuous U hU Y x).inner continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

end Kadison

end

end
end

end OAI
