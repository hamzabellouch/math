import OAI.Analysis.KadisonKastler.StateSymmetryGroup

namespace OAI

/-! # Determining a vector-fixing implementation from its algebra action -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem stateGroups_eq_of_actions (Ω : H) (hcyc : DenseRange (algebraVectorMap M Ω))
    (U V : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hnU : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)
    (hnV : ∀ t a, a ∈ M → unitaryConj (V t) a ∈ M)
    (hfixU : ∀ t, (U t : H →L[ℂ] H) Ω = Ω)
    (hfixV : ∀ t, (V t : H →L[ℂ] H) Ω = Ω)
    (he : ∀ t a, a ∈ M → unitaryConj (U t) a = unitaryConj (V t) a) : U = V := by
  apply MonoidHom.ext
  intro t
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  apply hcyc.induction_on (p := fun y => (U t : H →L[ℂ] H) y = (V t : H →L[ℂ] H) y) x
  · exact isClosed_eq (U t).val.continuous (V t).val.continuous
  · intro a
    change (U t : H →L[ℂ] H) (a.val Ω) = (V t : H →L[ℂ] H) (a.val Ω)
    rw [← stateSymmetryAut_vector Ω (U t) (stateGroup_normalizes U hnU t) (hfixU t) a,
      ← stateSymmetryAut_vector Ω (V t) (stateGroup_normalizes V hnV t) (hfixV t) a]
    exact congrArg (fun A : H →L[ℂ] H => A Ω) (he t a.val a.property)

end

end KadisonKastler

end OAI
