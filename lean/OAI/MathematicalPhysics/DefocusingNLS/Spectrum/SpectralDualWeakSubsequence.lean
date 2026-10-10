import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWeakSubsequence

namespace OAI

/-! Bounded sequences in the Hilbert dual have weakly convergent subsequences. -/

open Filter Topology
namespace DefocusingNLS

theorem spectralRealHilbert_dual_weak_subsequence {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (F : ℕ → StrongDual ℝ E) (M : ℝ) (hF : ∀ n, ‖F n‖ ≤ M) :
    ∃ F₀ : StrongDual ℝ E, ‖F₀‖ ≤ M ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ L : StrongDual ℝ E →L[ℝ] ℝ,
        Tendsto (fun n => L (F (φ n))) atTop (𝓝 (L F₀)) := by
  let A := InnerProductSpace.toDual ℝ E
  have hb (n : ℕ) : ‖A.symm (F n)‖ ≤ M := (A.symm.norm_map _).le.trans (hF n)
  obtain ⟨u,hu,φ,hφ,ht⟩ := spectralRealHilbert_weak_subsequence (fun n => A.symm (F n)) M hb
  refine ⟨A u,(A.norm_map u).le.trans hu,φ,hφ,fun L => ?_⟩
  have h := ht (L.comp A.toContinuousLinearEquiv.toContinuousLinearMap)
  simpa only [ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe,A.apply_symm_apply] using h

end DefocusingNLS

end OAI
