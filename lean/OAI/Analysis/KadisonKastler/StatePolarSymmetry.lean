import OAI.Analysis.KadisonKastler.StateSymmetry
import OAI.Analysis.KadisonKastler.TomitaMiddleCore

namespace OAI

/-! # State-preserving symmetries commute with polar conjugation

The bounded middle operator is injective. Its core formula and the
already constructed resolvent transport identify the polar conjugation
on the dense algebraic orbit, without assuming modular uniqueness.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem tomitaMiddleOperator_injective (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) :
    Function.Injective (tomitaMiddleOperator (M := M) J Ω) :=
  (tomitaGraphRoot_injective J Ω hsep hcyc).comp
    (tomitaGraphComplementRoot_injective J Ω hsep hcyc)

variable (Ω : H) (u : unitary (H →L[ℂ] H)) (hu : Conjugates u M M)
  (hfix : (u : H →L[ℂ] H) Ω=Ω)
  (hcyc : DenseRange (algebraVectorMap M Ω))

include hu hfix hcyc in
theorem stateSymmetry_middle (J : H ≃ₗᵢ⋆[ℂ] H) :
    Commute (u : H →L[ℂ] H) (tomitaMiddleOperator (M := M) J Ω) := by
  have hc : Commute (u : H →L[ℂ] H) (graphResolvent M J Ω 1) := by
    ext x
    exact stateSymmetry_resolvent Ω u hu hfix hcyc J 1 x
  have hr : Commute (u : H →L[ℂ] H) (tomitaGraphRoot (M := M) J Ω) := by
    simpa only [tomitaGraphRoot,CFC.sqrt_eq_cfc] using
      (hc.symm.cfc_nnreal NNReal.sqrt).symm
  have hq : Commute (u : H →L[ℂ] H) (tomitaGraphComplementRoot (M := M) J Ω) := by
    have hh := (Commute.one_right (u : H →L[ℂ] H)).sub_right hc
    simpa only [tomitaGraphComplementRoot,CFC.sqrt_eq_cfc] using
      (hh.symm.cfc_nnreal NNReal.sqrt).symm
  exact hr.mul_right hq

include hu hfix hcyc in
theorem stateSymmetry_polar (J : H ≃ₗᵢ⋆[ℂ] H)
    (hsep : Function.Injective (algebraVectorMap M Ω)) (x : H) :
    (u : H →L[ℂ] H) (tomitaPolarConjugation J Ω hsep hcyc x)=
      tomitaPolarConjugation J Ω hsep hcyc ((u : H →L[ℂ] H) x) := by
  have hc : Commute (u : H →L[ℂ] H) (graphResolvent M J Ω 1) := by
    ext y
    exact stateSymmetry_resolvent Ω u hu hfix hcyc J 1 y
  have hm := stateSymmetry_middle Ω u hu hfix hcyc J
  apply hcyc.induction_on (p := fun x =>
    (u : H →L[ℂ] H) (tomitaPolarConjugation J Ω hsep hcyc x)=
      tomitaPolarConjugation J Ω hsep hcyc ((u : H →L[ℂ] H) x)) x
  · exact isClosed_eq (u.val.continuous.comp (map_continuous _))
      ((map_continuous _).comp u.val.continuous)
  · intro a
    apply tomitaMiddleOperator_injective J Ω hsep hcyc
    calc
      _ = (u : H →L[ℂ] H) (tomitaMiddleOperator (M := M) J Ω
          (tomitaPolarConjugation J Ω hsep hcyc (a.val Ω))) :=
        (congrArg (fun T : H →L[ℂ] H => T (tomitaPolarConjugation J Ω hsep hcyc (a.val Ω))) hm.eq).symm
      _ = (u : H →L[ℂ] H) ((1-graphResolvent M J Ω 1) (star a.val Ω)) := by
        rw [tomitaMiddleOperator_algebra J Ω hsep hcyc a]
      _ = (1-graphResolvent M J Ω 1) ((u : H →L[ℂ] H) (star a.val Ω)) :=
        congrArg (fun T : H →L[ℂ] H => T (star a.val Ω))
          ((Commute.one_right (u : H →L[ℂ] H)).sub_right hc).eq
      _ = (1-graphResolvent M J Ω 1) (star (stateSymmetryAut u hu a).val Ω) := by
        congr 1
        have he := stateSymmetryAut_vector Ω u hu hfix (star a)
        have hs : stateSymmetryAut u hu (star a)=star (stateSymmetryAut u hu a) :=
          map_star (stateSymmetryAut u hu) a
        rw [hs] at he
        exact he.symm
      _ = tomitaMiddleOperator (M := M) J Ω
          (tomitaPolarConjugation J Ω hsep hcyc ((stateSymmetryAut u hu a).val Ω)) :=
        (tomitaMiddleOperator_algebra J Ω hsep hcyc (stateSymmetryAut u hu a)).symm
      _ = _ := by rw [stateSymmetryAut_vector Ω u hu hfix a]; rfl

end

end KadisonKastler

end OAI
