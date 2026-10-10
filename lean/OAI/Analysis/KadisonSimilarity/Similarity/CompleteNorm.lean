import OAI.Analysis.KadisonSimilarity.Similarity.CompletelyBounded

namespace OAI

/-! The least nonnegative complete bound. Kirchberg's proof uses a
similarity attaining this bound, rather than an arbitrary similarity. -/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def completeNorm (f : A → (H →L[ℂ] H)) : ℝ :=
  sInf {C : ℝ | 0 ≤ C ∧ CompleteBound f C}

theorem completeNorm_nonneg {f : A → (H →L[ℂ] H)} (hf : IsCompletelyBounded f) :
    0 ≤ completeNorm f :=
  le_csInf hf (fun _ h => h.1)

theorem completeNorm_le {f : A → (H →L[ℂ] H)} {C : ℝ}
    (hC : 0 ≤ C) (hf : CompleteBound f C) : completeNorm f ≤ C :=
  csInf_le ⟨0, fun _ h => h.1⟩ ⟨hC, hf⟩

/-- Complete bounds form a closed set, so their finite infimum is a bound. -/
theorem completeBound_completeNorm {f : A → (H →L[ℂ] H)}
    (hf : IsCompletelyBounded f) : CompleteBound f (completeNorm f) := by
  intro n X
  by_cases hz : ‖CStarMatrix.ofMatrix X‖ = 0
  · obtain ⟨C, _, hC⟩ := hf
    simpa only [hz, mul_zero] using hC n X
  · have hp : 0 < ‖CStarMatrix.ofMatrix X‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply (div_le_iff₀ hp).mp
    exact le_csInf hf (fun C hC => (div_le_iff₀ hp).mpr (hC.2 n X))

end KadisonSimilarity

end

end OAI
