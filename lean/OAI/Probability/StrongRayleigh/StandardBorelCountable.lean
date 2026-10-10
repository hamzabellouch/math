import OAI.Probability.StrongRayleigh.CountableProjectiveReindex
import OAI.Probability.StrongRayleigh.ProjectiveNatExtension

namespace OAI

universe u_1 u_2

noncomputable section

open MeasureTheory

namespace Problem336AdditiveD139.StandardBorelProjective

variable {I : Type u_1} {E : Type u_2} [Countable I] [MeasurableSpace E]
  [StandardBorelSpace E] [Nonempty E]

theorem exists_probabilityMeasure_finset_countable
    (P : (S : Finset I) → ProbabilityMeasure (S → E))
    (hP : IsProjectiveMeasureFamily (α := fun _ => E)
      (fun S => (P S : Measure (S → E)))) :
    ∃ μ : ProbabilityMeasure (I → E),
      IsProjectiveLimit (α := fun _ => E) (μ : Measure (I → E))
        (fun S => (P S : Measure (S → E))) := by
  exact CountableProjectiveReindex.countable_projective_exists_of_nat
    (fun P hP => exists_probabilityMeasure_finset_nat P hP) P hP

theorem existsUnique_probabilityMeasure_finset_countable
    (P : (S : Finset I) → ProbabilityMeasure (S → E))
    (hP : IsProjectiveMeasureFamily (α := fun _ => E)
      (fun S => (P S : Measure (S → E)))) :
    ∃! μ : ProbabilityMeasure (I → E),
      IsProjectiveLimit (α := fun _ => E) (μ : Measure (I → E))
        (fun S => (P S : Measure (S → E))) := by
  obtain ⟨μ, hμ⟩ := exists_probabilityMeasure_finset_countable P hP
  refine ⟨μ, hμ, ?_⟩
  intro ν hν
  exact Subtype.ext (hν.unique hμ)

theorem exists_projectiveLimit_countable
    (P : (S : Finset I) → Measure (S → E)) [∀ S, IsProbabilityMeasure (P S)]
    (hP : IsProjectiveMeasureFamily (α := fun _ => E) P) :
    ∃ μ : ProbabilityMeasure (I → E),
      IsProjectiveLimit (α := fun _ => E) (μ : Measure (I → E)) P := by
  exact exists_probabilityMeasure_finset_countable (fun S => ⟨P S, inferInstance⟩) hP

end Problem336AdditiveD139.StandardBorelProjective

end

end OAI
