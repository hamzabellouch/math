import OAI.Analysis.KadisonKastler.TomitaPolarConjugation

namespace OAI

/-! # Polar conjugation interchanges the resolvent and its complement -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

theorem tomitaPolarCoordinates_first (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H) :
    (tomitaPolarCoordinates J Ω hsep hcyc x).val 0 = tomitaGraphRoot (M := M) J Ω x := by
  let U := tomitaPolarCoordinates J Ω hsep hcyc
  have hc : IsClosed {x : H | (U x).val 0 = tomitaGraphRoot (M := M) J Ω x} :=
    isClosed_eq ((PiLp.continuous_apply 2 (fun _ : Fin 2 => H) 0).comp
      (continuous_subtype_val.comp U.continuous)) (tomitaGraphRoot J Ω).continuous
  refine (tomitaGraphRoot_dense J Ω hsep hcyc).induction ?_ hc x
  rintro _ ⟨y, rfl⟩
  change (tomitaPolarCoordinates J Ω hsep hcyc (tomitaGraphRoot (M := M) J Ω y)).val 0 = _
  rw [tomitaPolarCoordinates_root, tomitaGraphFirst_adjoint_apply]
  change graphResolvent M J Ω 1 y = tomitaGraphRoot J Ω (tomitaGraphRoot J Ω y)
  exact (congrArg (fun T : H →L[ℂ] H => T y) (tomitaGraphRoot_square J Ω)).symm

theorem tomitaPolarCoordinates_conjugation (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H) :
    tomitaPolarCoordinates J Ω hsep hcyc (tomitaPolarConjugation J Ω hsep hcyc x) =
      tomitaGraphAntiunitary J Ω (tomitaPolarCoordinates J Ω hsep hcyc x) := by
  change (tomitaPolarCoordinates J Ω hsep hcyc)
    ((tomitaPolarCoordinates J Ω hsep hcyc).symm _) = _
  exact LinearIsometryEquiv.apply_symm_apply _ _

theorem tomitaPolarCoordinates_second (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H) :
    (tomitaPolarCoordinates J Ω hsep hcyc x).val 1 =
      J (tomitaGraphRoot (M := M) J Ω (tomitaPolarConjugation J Ω hsep hcyc x)) := by
  have he := congrArg (fun v : rescaledGraphSubspace M J Ω 1 => v.val 0)
    (tomitaPolarCoordinates_conjugation J Ω hsep hcyc x)
  rw [tomitaPolarCoordinates_first] at he
  change tomitaGraphRoot J Ω (tomitaPolarConjugation J Ω hsep hcyc x) =
    J.symm ((tomitaPolarCoordinates J Ω hsep hcyc x).val 1) at he
  rw [he, J.apply_symm_apply]

private theorem inner_tomitaGraphRoot (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H) (x y : H) :
    inner ℂ (tomitaGraphRoot (M := M) J Ω x) (tomitaGraphRoot (M := M) J Ω y) =
      inner ℂ x (graphResolvent M J Ω 1 y) := by
  rw [← ContinuousLinearMap.adjoint_inner_right]
  have hs : (tomitaGraphRoot (M := M) J Ω).adjoint = tomitaGraphRoot J Ω :=
    (tomitaGraphRoot_selfAdjoint J Ω).star_eq
  rw [hs]
  exact congrArg (inner ℂ x)
    (congrArg (fun T : H →L[ℂ] H => T y) (tomitaGraphRoot_square J Ω))

theorem tomitaPolarResolvent_inner (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) (x y : H) :
    inner ℂ x y = inner ℂ x (graphResolvent M J Ω 1 y) +
      inner ℂ x (conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc)
        (graphResolvent M J Ω 1) y) := by
  let U := tomitaPolarCoordinates J Ω hsep hcyc
  let C := tomitaPolarConjugation J Ω hsep hcyc
  have hprod : inner ℂ x y = inner ℂ (U x).val (U y).val := (U.inner_map_map x y).symm
  rw [PiLp.inner_apply, Fin.sum_univ_two] at hprod
  rw [tomitaPolarCoordinates_first, tomitaPolarCoordinates_first,
    tomitaPolarCoordinates_second, tomitaPolarCoordinates_second] at hprod
  rw [conjugateIsometry_inner, inner_tomitaGraphRoot, inner_tomitaGraphRoot] at hprod
  have hc := conjugateIsometry_inner C (C x) (graphResolvent M J Ω 1 (C y))
  rw [tomitaPolarConjugation_involutive J Ω hsep hcyc] at hc
  exact hprod.trans (congrArg (fun z : ℂ => inner ℂ x (graphResolvent M J Ω 1 y) + z) hc.symm)

/-- The polar conjugation exchanges the two endpoints of the graph spectrum. -/
theorem tomitaPolarConjugation_resolvent (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω)) :
    conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) (graphResolvent M J Ω 1) =
      1 - graphResolvent M J Ω 1 := by
  let R := graphResolvent M J Ω 1
  let C := conjugationOperator (tomitaPolarConjugation J Ω hsep hcyc) R
  have hs : R + C = 1 := by
    ext x
    apply ext_inner_left ℂ
    intro y
    change inner ℂ y (R x + C x) = inner ℂ y x
    rw [inner_add_right]
    exact (tomitaPolarResolvent_inner J Ω hsep hcyc y x).symm
  change C = 1 - R
  calc
    C = (R + C) - R := by abel
    _ = 1 - R := by rw [hs]

end

end KadisonKastler

end OAI
