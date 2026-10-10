import OAI.Analysis.KadisonKastler.StandardTracialCommutant
import OAI.Analysis.KadisonKastler.TracialOrbitClosed
import OAI.Analysis.KadisonKastler.CommonRightProjection

namespace OAI

/-! # The commutant of the tracial basic construction -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M R : VonNeumannAlgebra H}

def StandardTracialPosition.toTracialRepresentation (p : StandardTracialPosition M) :
    UltrapowerBridge.TracialRepresentation M where
  vector := p.vector
  norm_vector := p.vector_norm
  cyclic := by
    intro a b
    change inner ℂ p.vector ((a * b).val p.vector) = inner ℂ p.vector ((b * a).val p.vector)
    rw [← p.trace_eq, ← p.trace_eq]
    exact p.trace.tracial a b
  separating := by
    intro a ha
    apply p.separating
    simpa only [algebraVectorMap, LinearMap.coe_mk, AddHom.coe_mk, ZeroMemClass.coe_zero,
      zero_apply] using ha

theorem StandardTracialPosition.right_commutes_orbitProjection
    (p : StandardTracialPosition M) (hRM : R ≤ M) (r : Algebra R) :
    (vectorOrbitClosure R.toStarSubalgebra p.vector).starProjection *
        conjugationOperator p.conjugation r.val =
      conjugationOperator p.conjugation r.val *
        (vectorOrbitClosure R.toStarSubalgebra p.vector).starProjection := by
  have hinv (a : Algebra R) : ∀ x ∈ vectorOrbitClosure R.toStarSubalgebra p.vector,
      conjugationOperator p.conjugation a.val x ∈ vectorOrbitClosure R.toStarSubalgebra p.vector := by
    apply vectorOrbitClosure_invariant_of_orbit
    intro b
    exact ⟨b * star a, conjugationOperator_algebraVector M p.conjugation p.vector
      p.conjugation_algebraVector (coordinateInclusion hRM a) (coordinateInclusion hRM b)⟩
  apply starProjection_commutes_of_invariant
  · exact hinv r
  · rw [← conjugationOperator_star p.conjugation p.conjugation_involutive]
    exact hinv (star r)

theorem StandardTracialPosition.basicConstruction_commutant
    (p : StandardTracialPosition M) (hRM : R ≤ M) :
    Set.centralizer ((M : Set (H →L[ℂ] H)) ∪
      {(vectorOrbitClosure R.toStarSubalgebra p.vector).starProjection}) =
      (conjugateRightAlgebra p.conjugation p.conjugation_involutive R : Set (H →L[ℂ] H)) := by
  ext T
  constructor
  · intro hT
    have hTM : T ∈ M.commutant := VonNeumannAlgebra.mem_commutant_iff.mpr
      (fun a ha => hT a (Or.inl ha))
    rw [← p.conjugate_algebra_eq_commutant] at hTM
    obtain ⟨a, ha, he⟩ := hTM
    have hv := congrArg (fun S : H →L[ℂ] H => S p.vector)
      (hT _ (Or.inr (Set.mem_singleton _)))
    change (vectorOrbitClosure R.toStarSubalgebra p.vector).starProjection (T p.vector) =
      T ((vectorOrbitClosure R.toStarSubalgebra p.vector).starProjection p.vector) at hv
    rw [Submodule.starProjection_eq_self_iff.mpr (mem_vectorOrbitClosure _ _)] at hv
    have hTv : T p.vector ∈ vectorOrbitClosure R.toStarSubalgebra p.vector :=
      Submodule.starProjection_eq_self_iff.mp hv
    have hvec : T p.vector = star a p.vector := by
      rw [← he]
      change p.conjugation (a (p.conjugation p.vector)) = _
      rw [p.conjugation_vector]
      exact p.conjugation_algebraVector ⟨a, ha⟩
    have haR : star a ∈ R := mem_subalgebra_of_tracial_vector_mem_orbitClosure
      p.toTracialRepresentation hRM (star (⟨a, ha⟩ : Algebra M)) (by
        change star a p.vector ∈ _
        rwa [hvec] at hTv)
    have haR' : a ∈ R := by
      have h : star (star a) ∈ R := R.toStarSubalgebra.star_mem' haR
      rw [star_star] at h
      exact h
    exact ⟨a, haR', he⟩
  · rintro ⟨a, ha, rfl⟩ x hx
    rcases hx with hx | hx
    · exact VonNeumannAlgebra.mem_commutant_iff.mp
        (conjugationOperator_mem_commutant M p.conjugation p.vector
          p.conjugation_algebraVector p.cyclic ⟨a, hRM ha⟩) x hx
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact p.right_commutes_orbitProjection hRM ⟨a, ha⟩

end

end KadisonKastler

end OAI
