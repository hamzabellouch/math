import OAI.Probability.InvariantIsing.Cavity.CavityStrictCascadeLimit

namespace OAI

/-! A depth-n cascade only uses its first n exponents. This identifies
the uniform approximation convention with the field-chain convention. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron

namespace InvariantIsing

lemma cavity_labeled_exponent_congr (n : ℕ) (b c : ℕ → ℝ)
    (hbc : ∀ i, i < n → b i = c i) :
    labeledCascadeLaw n b = labeledCascadeLaw n c := by
  induction n generalizing b c with
  | zero => rfl
  | succ n ih =>
    have h0 := hbc 0 (Nat.zero_lt_succ n)
    have ht := ih (fun i => b (i + 1)) (fun i => c (i + 1))
      (fun i hi => hbc (i + 1) (by omega))
    apply Subtype.ext
    change (labeledPoissonLaw (intensityComponents (powerIntensity (b 0)))).prod
        (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
          (labeledCascadeLaw n (fun i => b (i + 1)) : Measure (LabeledTree n))))) =
      (labeledPoissonLaw (intensityComponents (powerIntensity (c 0)))).prod
        (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
          (labeledCascadeLaw n (fun i => c (i + 1)) : Measure (LabeledTree n)))))
    rw [h0, ht]

lemma cavity_cascade_exponent_congr (n : ℕ) (b c a : ℕ → ℝ)
    (hbc : ∀ i, i < n → b i = c i) :
    cascadeCompactLaw n b a = cascadeCompactLaw n c a := by
  simp only [cascadeCompactLaw, cascadeReplicaLaw, cavity_labeled_exponent_congr n b c hbc]
  rfl

lemma cavity_uniform_chain_exponent (n i : ℕ) (hi : i < n) :
    uniformExponent n i = chainExponent (uniformCut n) i := by
  rw [chainExponent_apply _ hi]
  simp only [uniformExponent, uniformCut, Nat.cast_add, Nat.cast_one]

lemma cavity_uniform_chain_law (n : ℕ) (a : ℕ → ℝ) :
    cascadeCompactLaw n (uniformExponent n) a =
      cascadeCompactLaw n (chainExponent (uniformCut n)) a :=
  cavity_cascade_exponent_congr n _ _ a (cavity_uniform_chain_exponent n)

end InvariantIsing

end

end OAI
