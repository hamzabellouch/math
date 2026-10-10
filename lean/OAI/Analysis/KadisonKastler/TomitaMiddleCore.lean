import OAI.Analysis.KadisonKastler.TomitaCommutantCoordinates

namespace OAI

/-! # The bounded middle operator on the algebra and commutant cores

The product of the complementary graph roots replaces the unbounded modular
square root in the operator identities used below.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

def tomitaMiddleOperator : H →L[ℂ] H :=
  tomitaGraphRoot (M := M) J Ω * tomitaGraphComplementRoot (M := M) J Ω

theorem tomitaMiddleOperator_selfAdjoint :
    IsSelfAdjoint (tomitaMiddleOperator (M := M) J Ω) := by
  unfold tomitaMiddleOperator
  rw [IsSelfAdjoint, star_mul, (tomitaGraphRoot_selfAdjoint J Ω).star_eq,
    (tomitaGraphComplementRoot_nonneg J Ω).isSelfAdjoint.star_eq]
  exact (tomitaGraphRoots_commute J Ω).eq.symm

theorem tomitaMiddleOperator_polar (v : H) :
    tomitaMiddleOperator (M := M) J Ω (tomitaPolarConjugation J Ω hsep hcyc v) =
      tomitaPolarConjugation J Ω hsep hcyc (tomitaMiddleOperator (M := M) J Ω v) := by
  change tomitaGraphRoot (M := M) J Ω
      (tomitaGraphComplementRoot (M := M) J Ω (tomitaPolarConjugation J Ω hsep hcyc v)) = _
  rw [← tomitaGraphRoot_polar_apply J Ω hsep hcyc,
    tomitaGraphRoot_polar_symm J Ω hsep hcyc]
  exact congrArg (tomitaPolarConjugation J Ω hsep hcyc)
    (congrArg (fun T : H →L[ℂ] H => T v) (tomitaGraphRoots_commute J Ω).eq.symm)

theorem tomitaMiddleOperator_algebra (a : Algebra M) :
    tomitaMiddleOperator (M := M) J Ω
        (tomitaPolarConjugation J Ω hsep hcyc (a.val Ω)) =
      (1 - graphResolvent M J Ω 1) (star a.val Ω) := by
  let v := tomitaCoreCoordinate J Ω hsep hcyc (star a)
  have hr : tomitaGraphRoot (M := M) J Ω v = star a.val Ω :=
    tomitaCoreCoordinate_first J Ω hsep hcyc (star a)
  have hq : tomitaGraphComplementRoot (M := M) J Ω v =
      tomitaPolarConjugation J Ω hsep hcyc (a.val Ω) := by
    have h := tomitaCoreCoordinate_adjoint J Ω hsep hcyc (star a)
    change tomitaGraphRoot (M := M) J Ω
      (tomitaPolarConjugation J Ω hsep hcyc v) = star (star a.val) Ω at h
    rw [star_star, tomitaGraphRoot_polar_symm J Ω hsep hcyc] at h
    have h' := congrArg (tomitaPolarConjugation J Ω hsep hcyc) h
    rw [tomitaPolarConjugation_involutive J Ω hsep hcyc] at h'
    exact h'
  rw [← hq, ← hr]
  change (tomitaGraphRoot (M := M) J Ω *
      (tomitaGraphComplementRoot (M := M) J Ω * tomitaGraphComplementRoot (M := M) J Ω)) v = _
  rw [tomitaGraphComplementRoot_square J Ω hsep hcyc]
  have hc : Commute (tomitaGraphRoot (M := M) J Ω) (1 - graphResolvent M J Ω 1) := by
    rw [← tomitaGraphComplementRoot_square J Ω hsep hcyc]
    exact (tomitaGraphRoots_commute J Ω).mul_right (tomitaGraphRoots_commute J Ω)
  exact congrArg (fun T : H →L[ℂ] H => T v) hc.eq

theorem tomitaMiddleOperator_commutant (b : Algebra M.commutant) :
    tomitaMiddleOperator (M := M) J Ω
        (tomitaPolarConjugation J Ω hsep hcyc (b.val Ω)) =
      graphResolvent M J Ω 1 (star b.val Ω) := by
  obtain ⟨v, hr, hq⟩ := tomitaCommutant_root_coordinates J Ω hsep hcyc b
  rw [← hr, ← hq]
  change (tomitaGraphRoot (M := M) J Ω *
      tomitaGraphComplementRoot (M := M) J Ω * tomitaGraphRoot (M := M) J Ω) v = _
  have hc := (tomitaGraphRoots_commute (M := M) J Ω).eq
  calc
    _ = (tomitaGraphRoot (M := M) J Ω * tomitaGraphRoot (M := M) J Ω *
        tomitaGraphComplementRoot (M := M) J Ω) v := by
      rw [mul_assoc, ← hc, ← mul_assoc]
    _ = _ := by rw [tomitaGraphRoot_square]; rfl

end

end KadisonKastler

end OAI
