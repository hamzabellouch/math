import OAI.Analysis.KadisonKastler.ModularStateCoefficients
import OAI.Analysis.KadisonKastler.ModularRootCommutation
import OAI.Analysis.KadisonKastler.TomitaCoreCoordinates
import OAI.Analysis.KadisonKastler.RegularCoreRepresentation

namespace OAI

/-! # Resolvent coordinates of the lower KMS boundary -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem modularRoot_inner_group (t : ℝ) (a b : H) :
    inner ℂ (tomitaGraphRoot (M := M) J Ω a)
      ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)
        (tomitaGraphRoot (M := M) J Ω b)) =
    inner ℂ a (graphResolvent M J Ω 1
      ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) b)) := by
  have hc := congrArg (fun T : H →L[ℂ] H => T b)
    (modularStrongGroup_commute_root J Ω hsep hcyc t).eq
  change (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)
    (tomitaGraphRoot (M := M) J Ω b) =
    tomitaGraphRoot (M := M) J Ω
      ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) b) at hc
  rw [hc, ← ContinuousLinearMap.adjoint_inner_right]
  have hs : (tomitaGraphRoot (M := M) J Ω).adjoint = tomitaGraphRoot (M := M) J Ω :=
    (tomitaGraphRoot_selfAdjoint J Ω).star_eq
  rw [hs]
  exact congrArg (inner ℂ a) (congrArg (fun T : H →L[ℂ] H =>
    T ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) b))
      (tomitaGraphRoot_square J Ω))

theorem modularState_lower_resolvent (t : ℝ) (x y : Algebra M) :
    productVectorState Ω
      (unitaryConj (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t)) x.val * y.val) =
    inner ℂ (tomitaCoreCoordinate J Ω hsep hcyc (star x))
      (graphResolvent M J Ω 1
        ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd (-t)) : H →L[ℂ] H)
          (tomitaCoreCoordinate J Ω hsep hcyc y))) := by
  rw [productVectorState_conjugate_left Ω _
    (modularStrongGroup_fixes_state J Ω hsep hcyc t)]
  have hs : star (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) =
      (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd (-t)) : H →L[ℂ] H) :=
    congrArg (fun u : unitary (H →L[ℂ] H) => (u : H →L[ℂ] H))
      (regularGroup_star_eq (modularStrongGroup J Ω hsep hcyc) t)
  rw [hs]
  have hx : star x.val Ω = tomitaGraphRoot (M := M) J Ω
      (tomitaCoreCoordinate J Ω hsep hcyc (star x)) :=
    (tomitaCoreCoordinate_first J Ω hsep hcyc (star x)).symm
  rw [hx, ← tomitaCoreCoordinate_first J Ω hsep hcyc y]
  exact modularRoot_inner_group J Ω hsep hcyc (-t) _ _

omit [TopologicalSpace.SeparableSpace H] in
private theorem polar_inner_swap (a b : H) :
    inner ℂ (tomitaPolarConjugation J Ω hsep hcyc a) b =
      inner ℂ (tomitaPolarConjugation J Ω hsep hcyc b) a := by
  let C := tomitaPolarConjugation J Ω hsep hcyc
  have h := conjugateIsometry_inner C a (C b)
  rw [tomitaPolarConjugation_involutive J Ω hsep hcyc b] at h
  exact h.trans (by
    change (starRingEnd ℂ) (inner ℂ a (C b)) = inner ℂ (C b) a
    rw [inner_conj_symm])

private theorem polar_resolvent_group (t : ℝ) (a : H) :
    tomitaPolarConjugation J Ω hsep hcyc
      (graphResolvent M J Ω 1
        ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) a)) =
    (1 - graphResolvent M J Ω 1)
      ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)
        (tomitaPolarConjugation J Ω hsep hcyc a)) := by
  let C := tomitaPolarConjugation J Ω hsep hcyc
  have hC := tomitaPolarConjugation_involutive J Ω hsep hcyc
  have h := conjugationOperator_mul C hC (graphResolvent M J Ω 1)
    (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H)
  rw [tomitaPolarConjugation_resolvent, modularStrongGroup_polar_conjugation] at h
  have hv := congrArg (fun T : H →L[ℂ] H => T (C a)) h
  change C (graphResolvent M J Ω 1
    ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t) : H →L[ℂ] H) (C (C a)))) = _ at hv
  have hCa : C (C a) = a := hC a
  rw [hCa] at hv
  exact hv

theorem modularState_upper_resolvent (t : ℝ) (x y : Algebra M) :
    productVectorState Ω
      (y.val * unitaryConj (modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t)) x.val) =
    inner ℂ (tomitaCoreCoordinate J Ω hsep hcyc (star x))
      ((1 - graphResolvent M J Ω 1)
        ((modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd (-t)) : H →L[ℂ] H)
          (tomitaCoreCoordinate J Ω hsep hcyc y))) := by
  let C := tomitaPolarConjugation J Ω hsep hcyc
  let X := tomitaCoreCoordinate J Ω hsep hcyc x
  let Y := tomitaCoreCoordinate J Ω hsep hcyc y
  let T : H →L[ℂ] H := 1 - graphResolvent M J Ω 1
  let u := modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd t)
  let v := modularStrongGroup J Ω hsep hcyc (Multiplicative.ofAdd (-t))
  have hstar : star (u : H →L[ℂ] H) = (v : H →L[ℂ] H) :=
    congrArg (fun u : unitary (H →L[ℂ] H) => (u : H →L[ℂ] H))
      (regularGroup_star_eq (modularStrongGroup J Ω hsep hcyc) t)
  have hT : T.adjoint = T :=
    ((IsSelfAdjoint.one (R := H →L[ℂ] H)).sub (graphResolvent_positive J Ω 1).isSelfAdjoint).star_eq
  have hvT : Commute (v : H →L[ℂ] H) T :=
    (Commute.one_right _).sub_right (modularStrongGroup_commute_resolvent J Ω hsep hcyc (-t))
  rw [productVectorState_conjugate_right Ω _
    (modularStrongGroup_fixes_state J Ω hsep hcyc t)]
  have hy : star y.val Ω = tomitaGraphRoot (M := M) J Ω (C Y) :=
    (tomitaCoreCoordinate_adjoint J Ω hsep hcyc y).symm
  have hx : x.val Ω = tomitaGraphRoot (M := M) J Ω X :=
    (tomitaCoreCoordinate_first J Ω hsep hcyc x).symm
  rw [hy, hx, modularRoot_inner_group J Ω hsep hcyc t, polar_inner_swap J Ω hsep hcyc,
    polar_resolvent_group J Ω hsep hcyc t]
  change inner ℂ (T ((u : H →L[ℂ] H) (C X))) Y = _
  rw [← ContinuousLinearMap.adjoint_inner_right, hT,
    ← ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (C X) (star (u : H →L[ℂ] H) (T Y)) = _
  rw [hstar]
  have he := congrArg (fun A : H →L[ℂ] H => A Y) hvT.eq
  change (v : H →L[ℂ] H) (T Y) = T ((v : H →L[ℂ] H) Y) at he
  rw [he, tomitaCoreCoordinate_star J Ω hsep hcyc x]


end

end KadisonKastler

end OAI
