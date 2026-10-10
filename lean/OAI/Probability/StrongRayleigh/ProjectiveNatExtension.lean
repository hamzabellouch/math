import OAI.Probability.StrongRayleigh.StandardBorelProjective

namespace OAI

universe u_1 u_2

noncomputable section

open MeasureTheory Finset Preorder

namespace Problem336AdditiveD139.StandardBorelProjective

theorem exists_probabilityMeasure_finset_nat
    {E : Type u_1} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    (P : (S : Finset ℕ) → ProbabilityMeasure (S → E))
    (hP : IsProjectiveMeasureFamily (α := fun _ => E)
      (fun S => (P S : Measure (S → E)))) :
    ∃ μ : ProbabilityMeasure (ℕ → E),
      IsProjectiveLimit (α := fun _ => E) (μ : Measure (ℕ → E))
        (fun S => (P S : Measure (S → E))) := by
  obtain ⟨μ, hμ⟩ := exists_probabilityMeasure_prefix (fun n => P (Iic n))
    (fun n => (hP (Iic (n + 1)) (Iic n)
      (Finset.Iic_subset_Iic.mpr (Nat.le_succ n))).symm)
  exact ⟨μ, (isProjectiveLimit_nat_iff hP (μ : Measure (ℕ → E))).mpr hμ⟩

theorem exists_projectiveLimit_nat
    {E : Type u_2} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    (P : (S : Finset ℕ) → Measure (S → E))
    [∀ S, IsProbabilityMeasure (P S)]
    (hP : IsProjectiveMeasureFamily (α := fun _ => E) P) :
    ∃ μ : ProbabilityMeasure (ℕ → E),
      IsProjectiveLimit (α := fun _ => E) (μ : Measure (ℕ → E)) P :=
  exists_probabilityMeasure_finset_nat (fun S => ⟨P S, inferInstance⟩) hP

end Problem336AdditiveD139.StandardBorelProjective

end

end OAI
