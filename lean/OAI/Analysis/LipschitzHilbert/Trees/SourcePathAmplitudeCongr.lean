import OAI.Analysis.LipschitzHilbert.Phase.SourcePathPrediction

namespace OAI

/-! Exact node amplitude identities preserve the path ratios and their
predictors. This permits literal regrouping of physical packets before
the marked path integral, without changing any mass or transition. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid
variable {τ σ σ' X : Type*} {κ : Type} [Fintype κ]
variable (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
  (weight : τ → X → ℝ) (K : ℕ) (gap : ℕ → ℝ)
  (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
  (value : X → σ → EuclideanSpace ℂ κ)
  (packets' : Finset σ') (assigned' : σ' → τ) (stop' : σ' → ℕ)
  (value' : X → σ' → EuclideanSpace ℂ κ)
  (phase : ℕ → ℂ) (a : ℝ) (x : X)
  (hamp : ∀ level cell,
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      packets assigned stop (value x) phase a x level cell =
    g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      packets' assigned' stop' (value' x) phase a x level cell)

include hamp

theorem sourceBlockNodeRatio_congr_amplitude (α p : ℝ) (lower upper : ℕ) (parent : ℤ) :
    g.sourceBlockNodeRatio tops slope precision cutoff weight K gap
      packets assigned stop value phase a α p lower upper parent x =
    g.sourceBlockNodeRatio tops slope precision cutoff weight K gap
      packets' assigned' stop' value' phase a α p lower upper parent x := by
  simp only [sourceBlockNodeRatio,hamp]

theorem sourceShiftedPathRatio_congr_amplitude {Kb : ℕ}
    (α p : ℝ) (shift : Fin Kb) (top : τ) (j : ℕ) :
    g.sourceShiftedPathRatio tops slope precision cutoff weight K gap
      packets assigned stop value phase a α p shift top x j =
    g.sourceShiftedPathRatio tops slope precision cutoff weight K gap
      packets' assigned' stop' value' phase a α p shift top x j := by
  exact g.sourceBlockNodeRatio_congr_amplitude tops slope precision cutoff weight K gap
    packets assigned stop value packets' assigned' stop' value' phase a x hamp α p _ _ _

theorem sourceActivePathValue_congr_amplitude {Kb : ℕ}
    (α p M : ℝ) (shift : Fin Kb) (top : τ) (count : ℕ) :
    g.sourceActivePathValue tops slope precision cutoff weight K gap
      packets assigned stop value phase a α p M shift top count x =
    g.sourceActivePathValue tops slope precision cutoff weight K gap
      packets' assigned' stop' value' phase a α p M shift top count x := by
  classical
  unfold sourceActivePathValue sourceActiveProduct
  apply Finset.prod_congr rfl
  intro j _
  split_ifs
  · exact g.sourceShiftedPathRatio_congr_amplitude tops slope precision cutoff weight K gap
      packets assigned stop value packets' assigned' stop' value' phase a x hamp α p shift top j
  · rfl

theorem sourceShiftedPathPrediction_congr_amplitude {Kb : ℕ}
    (p μ : ℝ) (shift : Fin Kb) (top : τ) (j : ℕ) :
    g.sourceShiftedPathPrediction tops slope precision cutoff weight K gap
      packets assigned stop value phase a p μ shift top x j =
    g.sourceShiftedPathPrediction tops slope precision cutoff weight K gap
      packets' assigned' stop' value' phase a p μ shift top x j := by
  simp only [sourceShiftedPathPrediction,sourceBlockPrediction,hamp]

end LipschitzHilbert.AngularGrid

end

end OAI
