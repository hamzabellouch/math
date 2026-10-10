import OAI.Combinatorics.BalancedRyser.Candidates.CandidateValidityWitness
import OAI.Combinatorics.BalancedRyser.Probability.FreshWitnessProbability

namespace OAI

namespace Balanced.CandidateWitnessProbability

open CandidateValidityWitness FreshWitnessProbability

noncomputable section
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem pairWitness_family_probability_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : Finset (Direction F)) (a : MergedPairs F)
    (e : ι ↪ Direction F) (hfresh : ∀ i, e i ∉ D)
    (x y : ι → Point F) :
    ((exposedLaw D a).toOuterMeasure
      {M | ∀ i, PairWitness M (e i) (x i) (y i)}).toReal ≤
      (2 : ℝ) ^ Fintype.card ι *
        (Fintype.card F : ℝ)⁻¹ ^ (2 * Fintype.card ι) := by
  have hevent : {M : MergedPairs F | ∀ i, PairWitness M (e i) (x i) (y i)} =
      {M | ∃ σ : ι → Bool, ∀ i,
        OnLine (x i) (constituent M (e i) (σ i)) ∧
        OnLine (y i) (constituent M (e i) (!(σ i)))} := by
    ext M
    simp only [Set.mem_ofPred_eq, PairWitness]
    constructor
    · intro h
      choose σ hσ using h
      exact ⟨σ, hσ⟩
    · rintro ⟨σ, hσ⟩ i
      exact ⟨σ i, hσ i⟩
  rw [hevent]
  exact paired_witnesses_probability_le D a e hfresh x y

theorem pairWitness_probability_le
    (D : Finset (Direction F)) (a : MergedPairs F)
    (d : Direction F) (hd : d ∉ D) (x y : Point F) :
    ((exposedLaw D a).toOuterMeasure {M | PairWitness M d x y}).toReal ≤
      2 / (Fintype.card F : ℝ)^2 := by
  let e : Unit ↪ Direction F := ⟨fun _ => d, fun _ _ _ => Subsingleton.elim _ _⟩
  have h := pairWitness_family_probability_le D a e (fun _ => hd)
    (fun _ => x) (fun _ => y)
  change ((exposedLaw D a).toOuterMeasure
    {M | ∀ _ : Unit, PairWitness M d x y}).toReal ≤ _ at h
  simpa [div_eq_mul_inv] using h

theorem two_pairWitness_probability_le
    (D : Finset (Direction F)) (a : MergedPairs F)
    (d e : Direction F) (hd : d ∉ D) (he : e ∉ D) (hde : d ≠ e)
    (x₀ y₀ x₁ y₁ : Point F) :
    ((exposedLaw D a).toOuterMeasure
      {M | PairWitness M d x₀ y₀ ∧ PairWitness M e x₁ y₁}).toReal ≤
      4 / (Fintype.card F : ℝ)^4 := by
  let f : Bool ↪ Direction F :=
    ⟨fun b => if b then e else d, by
      intro b c hbc
      cases b <;> cases c <;> simp_all⟩
  have hf : ∀ b, f b ∉ D := by
    intro b
    cases b <;> assumption
  have h := pairWitness_family_probability_le D a f hf
    (fun b => if b then x₁ else x₀) (fun b => if b then y₁ else y₀)
  norm_num [f, div_eq_mul_inv] at h ⊢
  exact h

end
end Balanced.CandidateWitnessProbability

end OAI
