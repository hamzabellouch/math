import OAI.Analysis.KadisonKastler.StandardTracialPosition
import OAI.Analysis.KadisonKastler.ConjugateRightAlgebra
import OAI.Analysis.FactorGeneration.HilbertLimits

namespace OAI

/-! # The commutant in the constructed standard tracial position -/

namespace KadisonKastler

noncomputable section

open Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem StandardTracialPosition.conjugation_commutant_vector
    (p : StandardTracialPosition M) (r : Algebra M.commutant) :
    p.conjugation (r.val p.vector) = star r.val p.vector := by
  apply ext_inner_left ℂ
  intro ξ
  apply p.cyclic.induction_on (p := fun ξ =>
    inner ℂ ξ (p.conjugation (r.val p.vector)) = inner ℂ ξ (star r.val p.vector)) ξ
  · exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
  · intro a
    have hCa : p.conjugation (star a.val p.vector) = a.val p.vector := by
      simpa only [StarMemClass.coe_star, star_star] using p.conjugation_algebraVector (star a)
    have hc := congrArg (fun T : H →L[ℂ] H => T p.vector)
      (VonNeumannAlgebra.mem_commutant_iff.mp r.property a.val a.property)
    change a.val (r.val p.vector) = r.val (a.val p.vector) at hc
    calc
      inner ℂ (a.val p.vector) (p.conjugation (r.val p.vector)) =
          inner ℂ (p.conjugation (star a.val p.vector)) (p.conjugation (r.val p.vector)) := by rw [hCa]
      _ = star (inner ℂ (star a.val p.vector) (r.val p.vector)) :=
        conjugateIsometry_inner p.conjugation _ _
      _ = inner ℂ (r.val p.vector) (star a.val p.vector) := inner_conj_symm _ _
      _ = inner ℂ (a.val (r.val p.vector)) p.vector :=
        ContinuousLinearMap.adjoint_inner_right a.val _ p.vector
      _ = inner ℂ (r.val (a.val p.vector)) p.vector := by rw [hc]
      _ = inner ℂ (a.val p.vector) (star r.val p.vector) :=
        (ContinuousLinearMap.adjoint_inner_right r.val _ p.vector).symm

theorem StandardTracialPosition.conjugate_algebra_eq_commutant
    (p : StandardTracialPosition M) :
    conjugateRightAlgebra p.conjugation p.conjugation_involutive M = M.commutant := by
  have hcyc : DenseRange (algebraVectorMap M.commutant p.vector) :=
    Generator.commutant_orbit_dense M p.vector (fun a ha => p.separating ha)
  apply le_antisymm
  · rintro T ⟨a, ha, rfl⟩
    exact conjugationOperator_mem_commutant M p.conjugation p.vector
      p.conjugation_algebraVector p.cyclic ⟨a, ha⟩
  · intro T hT
    have hM := conjugationOperator_mem_commutant M.commutant p.conjugation p.vector
      p.conjugation_commutant_vector hcyc ⟨T, hT⟩
    rw [VonNeumannAlgebra.commutant_commutant] at hM
    exact ⟨conjugationOperator p.conjugation T, hM,
      conjugationOperator_twice _ p.conjugation_involutive T⟩

end

end KadisonKastler

end OAI
