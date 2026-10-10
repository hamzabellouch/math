import OAI.Probability.StrongRayleigh.Model
import OAI.Probability.StrongRayleigh.BinaryProjective
import OAI.Probability.StrongRayleigh.DPPReindex
import OAI.Probability.StrongRayleigh.DeterminantalUniqueness

namespace OAI

universe u_1

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal Topology ComplexConjugate

universe u

namespace Problem336AdditiveD139

lemma isFiniteDeterminantalLaw_of_isEmpty {F : Type u_1} [Fintype F] [IsEmpty F]
    (μ : ProbabilityMeasure (F → Bool)) (K : F → F → ℂ) :
    IsFiniteDeterminantalLaw μ K := by
  classical
  intro A
  have hA : A = ∅ := Finset.eq_empty_of_isEmpty A
  subst A
  refine Eq.trans ?_
    (Matrix.det_isEmpty (A := Matrix.of (fun i j : (∅ : Finset F) => K i.1 j.1))).symm
  simp

lemma finite_dpp_exists_including_empty
    (finite_exists : ∀ (F : Type u) [Fintype F] [Nonempty F] (K : F → F → ℂ),
      PositiveContractionFinite K →
        ∃ μ : ProbabilityMeasure (F → Bool), IsFiniteDeterminantalLaw μ K)
    (F : Type u) [Fintype F] (K : F → F → ℂ) (hK : PositiveContractionFinite K) :
    ∃ μ : ProbabilityMeasure (F → Bool), IsFiniteDeterminantalLaw μ K := by
  cases isEmpty_or_nonempty F with
  | inl h =>
    let μ : ProbabilityMeasure (F → Bool) :=
      ⟨Measure.dirac (fun _ => false), inferInstance⟩
    exact ⟨μ, isFiniteDeterminantalLaw_of_isEmpty μ K⟩
  | inr h => exact finite_exists F K hK

lemma det_finset_univ {F : Type u} [Fintype F] (K : F → F → ℂ) :
    (by
      classical
      exact Matrix.det (fun i j : (Finset.univ : Finset F) => K i.1 j.1) =
        Matrix.det K) := by
  classical
  let e : (Finset.univ : Finset F) ≃ F :=
    { toFun := fun i => i.1
      invFun := fun i => ⟨i, Finset.mem_univ i⟩
      left_inv := fun i => Subtype.ext rfl
      right_inv := fun i => rfl }
  exact Matrix.det_submatrix_equiv_self e K

lemma isDeterminantalLaw_of_projectiveLimit {I : Type u}
    (K : I → I → ℂ) (P : ∀ S : Finset I, ProbabilityMeasure (S → Bool))
    (hP : ∀ S : Finset I,
      IsFiniteDeterminantalLaw (P S) (fun i j : S => K i.1 j.1))
    (μ : ProbabilityMeasure (I → Bool))
    (hμ : IsProjectiveLimit (μ : Measure (I → Bool))
      (fun S => (P S : Measure (S → Bool)))) :
    IsDeterminantalLaw μ K := by
  classical
  intro A
  have hm : (μ : Measure (I → Bool)) {x | ∀ i ∈ A, x i = true} =
      (P A : Measure (A → Bool)) {x | ∀ i : A, x i = true} := by
    have hμA : Measure.map A.restrict (μ : Measure (I → Bool)) =
        (P A : Measure (A → Bool)) := hμ A
    rw [← hμA, Measure.map_apply]
    · congr 1
      ext x
      simp [Finset.restrict]
    · exact Measurable.of_eval (fun i => measurable_pi_apply i.1)
    · exact (Set.toFinite _).measurableSet
  rw [hm]
  have h := hP A Finset.univ
  simp only [Finset.mem_univ, forall_true_left] at h
  rw [h]
  refine (det_finset_univ (fun i j : A => K i.1 j.1)).trans ?_
  exact congrArg (fun d : DecidableEq A =>
    @Matrix.det A d _ ℂ _ (fun i j : A => K i.1 j.1)) (Subsingleton.elim _ _)

lemma positiveContractionKernel_existsUnique_of_finite_exists
    (finite_exists : ∀ (F : Type u) [Fintype F] [Nonempty F] (K : F → F → ℂ),
      PositiveContractionFinite K →
        ∃ μ : ProbabilityMeasure (F → Bool), IsFiniteDeterminantalLaw μ K)
    (I : Type u) (K : I → I → ℂ) (hK : PositiveContractionKernel K) :
    ∃! μ : ProbabilityMeasure (I → Bool), IsDeterminantalLaw μ K := by
  classical
  have hex : ∀ S : Finset I, ∃ μ : ProbabilityMeasure (S → Bool),
      IsFiniteDeterminantalLaw μ (fun i j : S => K i.1 j.1) := by
    intro S
    apply finite_dpp_exists_including_empty finite_exists S
    exact ⟨fun i j => hK.1 i.1 j.1, hK.2 S⟩
  choose P hP using hex
  have hproj := finiteDppFamily_projective K P hP
    (fun S ν hν => hν.eq (hP S))
  obtain ⟨μ, hμ⟩ := binary_projective_exists
    (fun S => (P S : Measure (S → Bool))) hproj
  exact existsUnique_determinantalLaw_of_exists K
    ⟨μ, isDeterminantalLaw_of_projectiveLimit K P hP μ hμ⟩

end Problem336AdditiveD139

end

end OAI
