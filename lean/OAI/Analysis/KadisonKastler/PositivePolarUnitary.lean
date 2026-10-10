import OAI.Analysis.KadisonKastler.StatePolarSymmetry
import OAI.Analysis.KadisonKastler.TomitaCoreDensity
import OAI.Analysis.KadisonKastler.TomitaPolarCorePairing

namespace OAI

/-! # Positivity removes a state-preserving polar unitary

The positive core pairing makes the unitary times the bounded middle
operator positive. Equality of the squares then determines that middle
operator uniquely, and its dense range determines the unitary.
-/

namespace KadisonKastler

open scoped ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

omit [CompleteSpace H] in
theorem operator_nonneg_of_inner_nonneg (T : H →L[ℂ] H)
    (h : ∀ x, 0 ≤ inner ℂ x (T x)) : 0 ≤ T := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  apply (LinearMap.isPositive_iff_complex T.toLinearMap).mpr
  intro x
  have hx : 0 ≤ inner ℂ (T x) x := by
    have hh := star_nonneg_iff.mpr (h x)
    change 0 ≤ (starRingEnd ℂ) (inner ℂ x (T x)) at hh
    rwa [inner_conj_symm] at hh
  exact ⟨Complex.ext rfl hx.2,hx.1⟩

theorem positive_polar_unitary_eq_one
    (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (u : unitary (H →L[ℂ] H)) (hu : Conjugates u M M)
    (hfix : (u : H →L[ℂ] H) Ω=Ω)
    (hcore : ∀ a : Algebra M, 0 ≤ inner ℂ (a.val Ω)
      ((u : H →L[ℂ] H) (tomitaPolarConjugation J Ω hsep hcyc (star a.val Ω)))) :
    (u : H →L[ℂ] H)=1 := by
  let R := tomitaGraphRoot (M := M) J Ω
  let Q := tomitaGraphComplementRoot (M := M) J Ω
  let B := tomitaMiddleOperator (M := M) J Ω
  let T : H →L[ℂ] H := (u : H →L[ℂ] H)*B
  have hcR : Commute (u : H →L[ℂ] H) R := by
    have hc : Commute (u : H →L[ℂ] H) (graphResolvent M J Ω 1) := by
      ext x
      exact stateSymmetry_resolvent Ω u hu hfix hcyc J 1 x
    simpa only [R,tomitaGraphRoot,CFC.sqrt_eq_cfc] using
      (hc.symm.cfc_nnreal NNReal.sqrt).symm
  have hT : 0 ≤ T := by
    apply operator_nonneg_of_inner_nonneg
    intro x
    apply (tomitaCoreCoordinate_dense J Ω hsep hcyc).induction_on
      (p := fun x => 0 ≤ inner ℂ x (T x)) x
    · exact isClosed_le continuous_const (continuous_id.inner T.continuous)
    · intro a
      have hh := hcore a
      rw [← tomitaCoreCoordinate_first J Ω hsep hcyc a,
        ← tomitaCoreCoordinate_complement J Ω hsep hcyc a] at hh
      have hR : R.adjoint=R := (tomitaGraphRoot_selfAdjoint J Ω).star_eq
      rw [← R.adjoint_inner_right,hR] at hh
      change 0 ≤ inner ℂ (tomitaCoreCoordinate J Ω hsep hcyc a)
        ((R*(u : H →L[ℂ] H)*Q) (tomitaCoreCoordinate J Ω hsep hcyc a)) at hh
      rw [← hcR.eq,mul_assoc] at hh
      exact hh
  have hB : 0 ≤ B := Commute.mul_nonneg (CFC.sqrt_nonneg _)
    (tomitaGraphComplementRoot_nonneg J Ω) (tomitaGraphRoots_commute J Ω)
  have hsq : T*T=B*B := by
    calc
      _ = star T*T := by rw [hT.isSelfAdjoint.star_eq]
      _ = B*(star (u : H →L[ℂ] H)*(u : H →L[ℂ] H))*B := by
        dsimp only [T]
        rw [star_mul,hB.isSelfAdjoint.star_eq]
        simp only [mul_assoc]
      _ = B*B := by rw [u.property.1,mul_one]
  have hTB : T=B := (CFC.mul_self_eq_mul_self_iff T B hT hB).mp hsq
  have hdense : DenseRange B := by
    have hs : B.adjoint=B := hB.isSelfAdjoint.star_eq
    change Dense (B.range : Set H)
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    apply Submodule.orthogonal_eq_bot_iff.mp
    rw [Submodule.orthogonal_closure,B.orthogonal_range,hs]
    exact LinearMap.ker_eq_bot.mpr (tomitaMiddleOperator_injective J Ω hsep hcyc)
  ext x
  apply hdense.induction_on (p := fun x => (u : H →L[ℂ] H) x=x) x
  · exact isClosed_eq u.val.continuous continuous_id
  · intro y
    exact congrArg (fun A : H →L[ℂ] H => A y) hTB

end

end KadisonKastler

end OAI
