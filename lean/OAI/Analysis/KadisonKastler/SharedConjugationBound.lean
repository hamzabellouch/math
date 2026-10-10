import OAI.Analysis.KadisonKastler.CommonPositionConjugationBound
import OAI.Analysis.KadisonKastler.SharedStandardTracialPosition

namespace OAI

/-! # Tracial conjugation comparison from the constructed common right action -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M N R : VonNeumannAlgebra H}

theorem StandardTracialPosition.right_action_eq
    (p : StandardTracialPosition M) (q : StandardTracialPosition N)
    (hsame : p.vector = q.vector) (hRM : R ≤ M) (hRN : R ≤ N)
    (hright : conjugateRightAlgebra p.conjugation p.conjugation_involutive R ≤ N.commutant)
    (r : H →L[ℂ] H) (hr : r ∈ R) :
    conjugationOperator p.conjugation r = conjugationOperator q.conjugation r := by
  have hcyclic : DenseRange (fun x : Algebra N => x.val p.vector) := by
    rw [hsame]
    exact q.cyclic
  have hq : ∀ x : Algebra N, q.conjugation (x.val p.vector) = (star x).val p.vector := by
    rw [hsame]
    exact q.conjugation_algebraVector
  apply operator_eq_of_mem_commutant_of_eq_on_cyclicVector N p.vector hcyclic
  · exact hright ⟨r, hr, rfl⟩
  · exact conjugationOperator_mem_commutant N q.conjugation p.vector hq hcyclic ⟨r, hRN hr⟩
  · exact conjugationOperator_common_vector M N p.conjugation q.conjugation p.vector
      p.conjugation_algebraVector hq r (hRM hr) (hRN hr)

theorem norm_tracialConjugations_sub_le_of_shared_right
    (hRM : R ≤ M) (_hRN : R ≤ N)
    (τ : FaithfulTracialState (Algebra M)) (hτ : FiniteVectorTrace τ)
    (Ω : H) (hΩ : ‖Ω‖ = 1)
    (htrace : ∀ x : Algebra M, ‖x.val Ω‖ = traceTwoNorm τ x)
    (hcyclicM : DenseRange (fun x : Algebra M => x.val Ω))
    (J₁ J₂ : H ≃ₗᵢ⋆[ℂ] H)
    (hJ₁ : Function.Involutive J₁) (hJ₂ : Function.Involutive J₂)
    (hM : ∀ x : Algebra M, J₁ (x.val Ω) = (star x).val Ω)
    (hN : ∀ x : Algebra N, J₂ (x.val Ω) = (star x).val Ω)
    (hirr : ∀ a : Algebra M,
      (∀ r : Algebra R, coordinateInclusion hRM r * a = a * coordinateInclusion hRM r) →
      ∃ c : ℂ, a = c • (1 : Algebra M))
    (hright : ∀ u : unitary (H →L[ℂ] H), (u : H →L[ℂ] H) ∈ R →
      conjugationOperator J₁ u = conjugationOperator J₂ u)
    {b : ℝ} (hb : kkDistance M N < b) :
    ‖(J₁ : H →L⋆[ℂ] H) - (J₂ : H →L⋆[ℂ] H)‖ ≤ 768 * b := by
  let ι : Algebra M →ₗ[ℂ] H := Generator.vectorOrbitMap M.toStarSubalgebra Ω
  let φ : Algebra R →⋆ₐ[ℂ] Algebra M := coordinateInclusion hRM
  let L : unitary (Algebra R) → unitary (H →L[ℂ] H) :=
    fun u => Unitary.map (StarMonoidHom.ofClass R.toStarSubalgebra.subtype) u
  let Q : unitary (Algebra R) → unitary (H →L[ℂ] H) :=
    fun u => conjugationUnitary J₁ hJ₁ (star (L u))
  have hL (u : unitary (Algebra R)) (x : Algebra M) :
      ι (φ u * x) = (L u : H →L[ℂ] H) (ι x) := rfl
  have hQ (u : unitary (Algebra R)) (x : Algebra M) :
      ι (x * φ u) = (Q u : H →L[ℂ] H) (ι x) := by
    have hr := conjugationOperator_algebraVector M J₁ Ω hM (star (φ u)) x
    rw [star_star] at hr
    exact hr.symm
  have hTL (u : unitary (Algebra R)) :
      Commute (tracialConjugationDefect J₁ J₂) (L u : H →L[ℂ] H) := by
    exact (tracialConjugationDefect_commute_both J₁ J₂ hJ₁ hJ₂ (L u)
      (hright (L u) (u : Algebra R).property)).1
  have hTQ (u : unitary (Algebra R)) :
      Commute (tracialConjugationDefect J₁ J₂) (Q u : H →L[ℂ] H) := by
    have hu : (star (L u) : H →L[ℂ] H) ∈ R :=
      R.toStarSubalgebra.star_mem' (u : Algebra R).property
    exact (tracialConjugationDefect_commute_both J₁ J₂ hJ₁ hJ₂ (star (L u))
      (hright (star (L u)) hu)).2
  exact norm_tracialConjugations_sub_le τ ι htrace hcyclicM hτ Ω hΩ
    (fun _ => rfl) J₁ J₂ hJ₁ hM hN φ hirr L Q hL hQ hTL hTQ hb


end

end KadisonKastler

end OAI
