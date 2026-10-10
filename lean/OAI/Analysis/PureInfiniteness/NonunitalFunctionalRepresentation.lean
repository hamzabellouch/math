import OAI.Analysis.JiangSu.Nuclearity.NuclearNormApproximation

namespace OAI

/-! The finite functional representation needed in KR02 Lemma 7.18.
Real functionals on the nonunital algebra are extended by the continuous
self-adjoint second-coordinate projection of its unitization. The existing
bounded GNS domination theorem then realizes all of them in one commutant.
No faithfulness or simplicity hypothesis is used. -/

noncomputable section
open scoped InnerProductSpace ComplexOrder

namespace WeakPureInfiniteness

variable {A I : Type*} [NonUnitalCStarAlgebra A] [Fintype I]

local instance functionalUnitizationOrder : PartialOrder (Unitization ℂ A) :=
  CStarAlgebra.spectralOrder _
local instance functionalUnitizationOrdered : StarOrderedRing (Unitization ℂ A) :=
  CStarAlgebra.spectralOrderedRing _

private lemma unitizationSnd_isSelfAdjoint (x : selfAdjoint (Unitization ℂ A)) :
    IsSelfAdjoint (x : Unitization ℂ A).snd := by
  change star (x : Unitization ℂ A).snd = (x : Unitization ℂ A).snd
  have h := congrArg (fun z : Unitization ℂ A => z.snd) x.property
  simpa only [Unitization.snd_star] using h

/-- The self-adjoint second coordinate is real linear and continuous, although
it need not preserve positivity. Positivity is supplied later by domination. -/
def selfAdjointUnitizationSnd : selfAdjoint (Unitization ℂ A) →L[ℝ] selfAdjoint A where
  toFun x := ⟨(x : Unitization ℂ A).snd, unitizationSnd_isSelfAdjoint x⟩
  map_add' x y := by ext; rfl
  map_smul' c x := by ext; rfl
  cont := by
    apply Continuous.subtype_mk
    exact Unitization.continuous_snd.comp continuous_subtype_val

@[simp] lemma selfAdjointUnitizationSnd_inr (a : selfAdjoint A) :
    selfAdjointUnitizationSnd
      ⟨(a : A), a.property.map (Unitization.inrNonUnitalStarAlgHom ℂ A)⟩ = a := rfl

/-- Simultaneous commutant realization of a finite family of real functionals.
The representation acts on the unitization so its GNS vector is cyclic;
restriction to the original algebra gives precisely the requested values. -/
theorem finite_nonunital_functional_representation
    (l : I → selfAdjoint A →L[ℝ] ℝ) :
    ∃ f : Unitization ℂ A →ₚ[ℂ] ℂ, f 1 = 1 ∧
      ∃ T : I → f.GNS →L[ℂ] f.GNS,
        (∀ i, IsSelfAdjoint (T i)) ∧
        (∀ i a, Commute (T i) (f.gnsStarAlgHom a)) ∧
        ∀ i (a : selfAdjoint A), l i a =
          (⟪Pureness.stateGNSVector f,
            T i (f.gnsStarAlgHom (a : Unitization ℂ A)
              (Pureness.stateGNSVector f))⟫_ℂ).re := by
  let l' (i : I) := (l i).comp (selfAdjointUnitizationSnd (A := A))
  obtain ⟨f, C, hf, hC, hdom⟩ := NuclearNorm.finite_state_domination l'
  have hrep (i : I) : ∃ T : f.GNS →L[ℂ] f.GNS,
      IsSelfAdjoint T ∧ (∀ a, Commute T (f.gnsStarAlgHom a)) ∧
      ∀ a : selfAdjoint (Unitization ℂ A), l' i a =
        (⟪Pureness.stateGNSVector f,
          T (f.gnsStarAlgHom a (Pureness.stateGNSVector f))⟫_ℂ).re := by
    obtain ⟨T, hT, _, _, hc, hv⟩ :=
      NuclearTrace.real_functional_in_commutant f (l' i).toLinearMap C (hdom i) hC
    exact ⟨T, hT, hc, hv⟩
  choose T hT hc hv using hrep
  refine ⟨f, hf, T, hT, hc, ?_⟩
  intro i a
  exact hv i ⟨(a : A), a.property.map (Unitization.inrNonUnitalStarAlgHom ℂ A)⟩

end WeakPureInfiniteness

end

end OAI
