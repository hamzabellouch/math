import OAI.InformationTheory.Entanglement.ConditionalUpdate

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped MeasureTheory ProbabilityTheory Topology
namespace SecretKey
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
variable (μ : Measure Ω) [IsFiniteMeasure μ]

def TapePublicStep (A B F G : MeasurableSpace Ω) (hF : F ≤ mΩ) : Prop :=
  G ≤ A ⊔ F ∨ G ≤ B ⊔ F ∨
    ∃ C : MeasurableSpace Ω, ∃ _ : C ≤ mΩ,
      G=C ⊔ F ∧ CondIndep F C (A ⊔ B) hF μ

theorem tapes_independent_given_complete_public
    (A B : MeasurableSpace Ω) (hA : A ≤ mΩ) (hB : B ≤ mΩ)
    (F : Filtration ℕ mΩ)
    (h0 : CondIndep (F 0) A B (F.le 0) μ)
    (hstep : ∀ k, TapePublicStep μ A B (F k) (F (k+1)) (F.le k)) :
    CondIndep (⨆ k, F k) (A ⊔ ⨆ k, F k) (B ⊔ ⨆ k, F k)
      (iSup_le fun k => F.le k) μ := by
  have hp : ∀ k, CondIndep (F k) A B (F.le k) μ := by
    intro k
    induction k with
    | zero => exact h0
    | succ k ih =>
      rcases hstep k with ha|hb|⟨C,hC,hg,hind⟩
      · exact sender_message_preserves_independence (F.le k) hA hB ih
          (F.mono (Nat.le_succ k)) ha
      · exact (sender_message_preserves_independence (F.le k) hB hA ih.symm
          (F.mono (Nat.le_succ k)) hb).symm
      · simpa only [hg] using
          public_source_preserves_independence (F.le k) hA hB ih hC hind
  exact conditional_independence_adjoin_public (iSup_le fun k => F.le k) hA hB
    (conditional_independence_limit μ F A B hA hB hp)

theorem terminal_tape_variables_independent
    (A B : MeasurableSpace Ω) (hA : A ≤ mΩ) (hB : B ≤ mΩ)
    (F : Filtration ℕ mΩ)
    (h0 : CondIndep (F 0) A B (F.le 0) μ)
    (hstep : ∀ k, TapePublicStep μ A B (F k) (F (k+1)) (F.le k))
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (X : Ω → α) (Y : Ω → β)
    (hX : Measurable[A ⊔ ⨆ k, F k] X)
    (hY : Measurable[B ⊔ ⨆ k, F k] Y) :
    CondIndepFun (⨆ k, F k) (iSup_le fun k => F.le k) X Y μ := by
  rw [condIndepFun_iff_condIndep]
  exact condIndep_of_condIndep_of_le_right
    (condIndep_of_condIndep_of_le_left
      (tapes_independent_given_complete_public μ A B hA hB F h0 hstep) hX.comap_le) hY.comap_le

end SecretKey

end

end OAI
