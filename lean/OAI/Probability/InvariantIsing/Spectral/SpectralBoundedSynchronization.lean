import OAI.Probability.InvariantIsing.Spectral.SpectralPathSynchronization

namespace OAI

/-! Bounded Lipschitz group factors for the replica-product application. -/

noncomputable section

open MeasureTheory ProbabilityTheory IsingPerceptron Set

namespace InvariantIsing

theorem spectralPartition_bounded_synchronization {m : ℕ}
    {Q : ProbabilityMeasure (SpectralArray (m + 1))}
    (hgg : HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (Q : Measure (SpectralArray (m + 1))))
    (hG : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralGram x)
    (q : Fin (m + 1) → ℝ) (hq : ∀ a, 0 ≤ q a)
    (hd : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i a, (x (i,i) a : ℝ) = q a)
    (hE : ∀ e : ℕ → ℕ, Function.Injective e →
      (Q : Measure (SpectralArray (m + 1))).map (permuteSpectralArray e) = Q)
    (hP : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), SpectralPartitionGeometry m x)
    (hn : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ a, 0 ≤ (x (0,1) a : ℝ))
    (a : Fin m) :
    ∃ f : ℝ → ℝ, LipschitzWith 1 f ∧ (∀ r, f r ∈ Icc (0 : ℝ) 1) ∧
      ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))), ∀ i j, i ≠ j →
        (x (i,j) a.castSucc : ℝ) = f (spectralSpinArray x i j) := by
  obtain ⟨f, hf, hpair⟩ := spectralPartition_lipschitz_synchronization hgg hG q hq hd
    (fun e => hE e e.injective) hP hn a
  let g : ℝ → ℝ := fun r => min (max (f r) 0) 1
  have hg : LipschitzWith 1 g := (hf.max_const 0).min_const 1
  have hgb (r : ℝ) : g r ∈ Icc (0 : ℝ) 1 :=
    ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩
  have hgp : ∀ᵐ x ∂(Q : Measure (SpectralArray (m + 1))),
      (x (0,1) a.castSucc : ℝ) = g (spectralSpinArray x 0 1) := by
    filter_upwards [hpair, hn] with x hx hnx
    dsimp only [g]
    rw [← hx, max_eq_left (hnx a.castSucc), min_eq_left (x (0,1) a.castSucc).property.2]
  exact ⟨g, hg, hgb, spectral_factor_all_off_diagonal hE a g hg.continuous hgp⟩

end InvariantIsing

end

end OAI
