import Mathlib
import OAI.Analysis.Commutator.PolarDecomposition

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.Polar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def leftSupport (T : H →L[ℂ] H) : H →L[ℂ] H :=
  partialIsometry T*star (partialIsometry T)

def rightSupport (T : H →L[ℂ] H) : H →L[ℂ] H := (initial T).starProjection

lemma isProjection_leftSupport (T : H →L[ℂ] H) : IsStarProjection (leftSupport T) :=
  partialIsometry_final_projection T

lemma isProjection_rightSupport (T : H →L[ℂ] H) : IsStarProjection (rightSupport T) :=
  isStarProjection_starProjection

lemma initial_mul_abs (T : H →L[ℂ] H) : rightSupport T*CFC.abs T=CFC.abs T := by
  ext x
  apply Submodule.starProjection_eq_self_iff.mpr
  exact (absToInitial T x).property

lemma abs_mul_initial (T : H →L[ℂ] H) : CFC.abs T*rightSupport T=CFC.abs T := by
  have hs : star (CFC.abs T)=CFC.abs T := (IsSelfAdjoint.of_nonneg (CFC.abs_nonneg T)).star_eq
  simpa only [star_mul,hs,(isProjection_rightSupport T).isSelfAdjoint.star_eq] using
    congrArg star (initial_mul_abs T)

lemma mul_rightSupport (T : H →L[ℂ] H) : T*rightSupport T=T := by
  calc
    _=(partialIsometry T*CFC.abs T)*rightSupport T := by rw [factorization]
    _=partialIsometry T*CFC.abs T := by rw [mul_assoc,abs_mul_initial]
    _=T := factorization T

lemma partialIsometry_triple (T : H →L[ℂ] H) :
    partialIsometry T*star (partialIsometry T)*partialIsometry T=partialIsometry T := by
  rw [mul_assoc,partialIsometry_initial,partialIsometry_mul_initial]

lemma leftSupport_mul (T : H →L[ℂ] H) : leftSupport T*T=T := by
  calc
    _=(partialIsometry T*star (partialIsometry T))*(partialIsometry T*CFC.abs T) := by
      rw [factorization]; rfl
    _=partialIsometry T*CFC.abs T := by rw [←mul_assoc,partialIsometry_triple]
    _=T := factorization T

lemma mul_partialIsometry_of_mul (T e : H →L[ℂ] H) (he : e*T=T) :
    e*partialIsometry T=partialIsometry T := by
  have h : ∀ x : initial T, e (initialMap T x)=initialMap T x := by
    intro x
    refine (absToInitial_dense T).induction_on x
      (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    intro y
    rw [initialMap_abs]
    exact congrArg (fun R : H →L[ℂ] H => R y) he
  ext x
  exact h ((initial T).orthogonalProjectionOnto x)

lemma leftSupport_le (T e : H →L[ℂ] H) (he : IsStarProjection e) (hT : e*T=T) :
    leftSupport T≤e := by
  apply ((isProjection_leftSupport T).le_iff_mul_eq_right he).mpr
  change e*(partialIsometry T*star (partialIsometry T))=_
  rw [←mul_assoc,mul_partialIsometry_of_mul T e hT]
  rfl

lemma abs_mul_of_mul (T e : H →L[ℂ] H) (hT : T*e=T) : CFC.abs T*e=CFC.abs T := by
  ext x
  have ht : T (e x-x)=0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg (fun R : H →L[ℂ] H => R x) hT)
  have ha : CFC.abs T (e x-x)=0 := by
    apply norm_eq_zero.mp
    rw [norm_abs_apply,ht,norm_zero]
  change CFC.abs T (e x)=CFC.abs T x
  exact sub_eq_zero.mp (by simpa only [map_sub] using ha)

lemma rightSupport_le (T e : H →L[ℂ] H) (he : IsStarProjection e) (hT : T*e=T) :
    rightSupport T≤e := by
  have hs : star (CFC.abs T)=CFC.abs T := (IsSelfAdjoint.of_nonneg (CFC.abs_nonneg T)).star_eq
  have hea : e*CFC.abs T=CFC.abs T := by
    simpa only [star_mul,hs,he.isSelfAdjoint.star_eq] using congrArg star (abs_mul_of_mul T e hT)
  have hfix : ∀ x : initial T, e x=x := by
    intro x
    refine (absToInitial_dense T).induction_on x
      (isClosed_eq (e.continuous.comp continuous_subtype_val) continuous_subtype_val) ?_
    intro y
    exact congrArg (fun R : H →L[ℂ] H => R y) hea
  apply ((isProjection_rightSupport T).le_iff_mul_eq_right he).mpr
  ext x
  exact hfix ⟨(initial T).starProjection x,(initial T).starProjection_apply_mem x⟩

lemma leftSupport_mem (M : VonNeumannAlgebra H) {T : H →L[ℂ] H} (hT : T∈M) :
    leftSupport T∈M :=
  M.mul_mem (partialIsometry_mem_vonNeumann M hT) (M.star_mem' (partialIsometry_mem_vonNeumann M hT))

lemma rightSupport_mem (M : VonNeumannAlgebra H) {T : H →L[ℂ] H} (hT : T∈M) :
    rightSupport T∈M := by
  rw [rightSupport,←partialIsometry_initial]
  exact M.mul_mem (M.star_mem' (partialIsometry_mem_vonNeumann M hT)) (partialIsometry_mem_vonNeumann M hT)

lemma trace_supports (τ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) (M : VonNeumannAlgebra H)
    (hτ : ∀ a∈M, ∀ b∈M, τ (a*b)=τ (b*a)) {T : H →L[ℂ] H} (hT : T∈M) :
    τ (rightSupport T)=τ (leftSupport T) := by
  rw [rightSupport,←partialIsometry_initial,leftSupport]
  exact hτ _ (M.star_mem' (partialIsometry_mem_vonNeumann M hT)) _ (partialIsometry_mem_vonNeumann M hT)

end Kadison.Polar

end

end
end

end OAI
