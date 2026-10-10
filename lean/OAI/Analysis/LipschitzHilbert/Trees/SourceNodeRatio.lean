import OAI.Analysis.LipschitzHilbert.Trees.HierarchyNormalization
import OAI.Analysis.LipschitzHilbert.Phase.SourcePredictionValues
import OAI.Analysis.LipschitzHilbert.Trees.SourceBlockChildren
import OAI.Analysis.LipschitzHilbert.Trees.UnaryEnergy

namespace OAI

/-! The normalized prediction is exactly the source node ratio with its
packet residual removed. The denominator retains the stopped-top mass
and every nonempty eligible child, including zero-amplitude children. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

variable {ι κ : Type} [Fintype ι] [Fintype κ]

def sourceNodeDenominator (n : ℝ) (c : ι → ℝ) (A : ι → EuclideanSpace ℂ κ)
    (α p : ℝ) : ℝ := n+∑ i, c i^(α-p)*‖A i‖^p

def sourceNodeRatio (n : ℝ) (c : ι → ℝ) (A : ι → EuclideanSpace ℂ κ)
    (α p : ℝ) (parentAmplitude : EuclideanSpace ℂ κ) : ℝ :=
  vertexAmount n parentAmplitude α p/sourceNodeDenominator n c A α p

theorem sourceNodeDenominator_stopped_mass (n : ℝ) (c : ι → ℝ)
    (A : ι → EuclideanSpace ℂ κ) (α p : ℝ) :
    sourceNodeDenominator n c A α p = (n-∑ i, c i)+∑ i, vertexAmount (c i) (A i) α p := by
  simp only [sourceNodeDenominator,vertexAmount,Finset.sum_add_distrib]
  ring

theorem sourceNodeDenominator_pos {n : ℝ} (hn : 0 < n) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (A : ι → EuclideanSpace ℂ κ) (α p : ℝ) :
    0 < sourceNodeDenominator n c A α p := by
  apply add_pos_of_pos_of_nonneg hn
  exact Finset.sum_nonneg fun i _ => mul_nonneg (Real.rpow_nonneg (hc i) _)
    (Real.rpow_nonneg (norm_nonneg _) _)

theorem sourceNodeRatio_pos {n : ℝ} (hn : 0 < n) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (A : ι → EuclideanSpace ℂ κ) (α p : ℝ)
    (parentAmplitude : EuclideanSpace ℂ κ) :
    0 < sourceNodeRatio n c A α p parentAmplitude :=
  div_pos (vertexAmount_pos hn parentAmplitude) (sourceNodeDenominator_pos hn c hc A α p)

/-- Exact source equation (src-25), in the actual prediction notation. -/
theorem sourcePredictionValue_eq_nodeRatio (n : ℝ) (c : ι → ℝ)
    (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ) (μ α p : ℝ)
    (hn : 0 < n) (hc : ∀ i, 0 < c i) (hrelation : p*μ = α-1) :
    sourcePredictionValue p μ n c A lam =
      sourceNodeRatio n c A α p (∑ i, lam i • A i) := by
  have h := normalized_child_ratio n c A lam μ α p hn hc hrelation
  simp only [sourcePredictionValue,energyRatio,sourceNodeRatio,sourceNodeDenominator,vertexAmount,
    RCLike.real_smul_eq_coe_smul (K := ℂ),smul_smul,mul_assoc] at h ⊢
  convert h.symm using 2

/-- Removing a residual is literal subtraction in the parent amplitude,
with the child denominator left unchanged. -/
theorem sourcePredictionValue_eq_residual_free_ratio
    (n : ℝ) (c : ι → ℝ) (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ)
    (parentAmplitude residual : EuclideanSpace ℂ κ) (μ α p : ℝ)
    (hn : 0 < n) (hc : ∀ i, 0 < c i) (hrelation : p*μ = α-1)
    (hdecomp : parentAmplitude = residual+∑ i, lam i • A i) :
    sourcePredictionValue p μ n c A lam =
      sourceNodeRatio n c A α p (parentAmplitude-residual) := by
  rw [hdecomp,add_sub_cancel_left]
  exact sourcePredictionValue_eq_nodeRatio n c A lam μ α p hn hc hrelation

/-- The source residual logarithmic error, with its exact mass power.
The common child denominator cancels before applying the energy estimate. -/
theorem source_node_log_residual_error
    (n : ℝ) (c : ι → ℝ) (A : ι → EuclideanSpace ℂ κ)
    (parentAmplitude residual : EuclideanSpace ℂ κ) (μ α p : ℝ)
    (hn : 0 < n) (hc : ∀ i, 0 ≤ c i) (hp : 1 ≤ p) (hrelation : p*μ = α-1) :
    |Real.log (sourceNodeRatio n c A α p parentAmplitude)-
        Real.log (sourceNodeRatio n c A α p (parentAmplitude-residual))| ≤
      p*n^(μ-1)*‖residual‖ := by
  have hd := sourceNodeDenominator_pos hn c hc A α p
  have hparent := vertexAmount_pos (a := α) (p := p) hn parentAmplitude
  have hfree := vertexAmount_pos (a := α) (p := p) hn (parentAmplitude-residual)
  have hμ : (α-1)/p = μ := by
    apply (div_eq_iff (show p ≠ 0 by linarith)).mpr
    nlinarith
  unfold sourceNodeRatio
  rw [Real.log_div hparent.ne' hd.ne',Real.log_div hfree.ne' hd.ne',sub_sub_sub_cancel_right]
  have h := log_vertexAmount_lipschitz (a := α) hn hp parentAmplitude (parentAmplitude-residual)
  simpa only [hμ,sub_sub_cancel] using h

theorem source_node_log_prediction_error
    (n : ℝ) (c : ι → ℝ) (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ)
    (parentAmplitude residual : EuclideanSpace ℂ κ) (μ α p : ℝ)
    (hn : 0 < n) (hc : ∀ i, 0 < c i) (hp : 1 ≤ p) (hrelation : p*μ = α-1)
    (hdecomp : parentAmplitude = residual+∑ i, lam i • A i) :
    |Real.log (sourceNodeRatio n c A α p parentAmplitude)-
        Real.log (sourcePredictionValue p μ n c A lam)| ≤
      p*n^(μ-1)*‖residual‖ := by
  rw [sourcePredictionValue_eq_residual_free_ratio n c A lam parentAmplitude residual
    μ α p hn hc hrelation hdecomp]
  exact source_node_log_residual_error n c A parentAmplitude residual μ α p hn
    (fun i => (hc i).le) hp hrelation

namespace AngularGrid
attribute [local instance] Classical.propDecidable

/-- On an actual source block, the normalized predictor is exactly beta0:
the node amount with its literal packet residual removed, divided by the
original stopped-mass/child-amount denominator. -/
theorem source_block_residual_free_ratio {τ σ X : Type*}
    (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → X → ℝ) (hprecision : ∀ t ∈ tops, 0 ≤ precision t)
    (hweight : ∀ t x, 0 < weight t x) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : σ → EuclideanSpace ℂ κ) (phase : ℕ → ℂ) (a : ℝ) (x : X)
    (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (heligible : ∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s))
    {lower upper : ℕ} (hle : lower ≤ upper) (parent : ℤ)
    (hparent : (g.cellTops tops slope precision cutoff lower parent).Nonempty)
    (μ α p : ℝ) (hrelation : p*μ = α-1) :
    let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
    let c := fun i : cells => g.mass tops slope precision cutoff weight upper i.val x
    let A := fun i : cells => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      packets assigned stop value phase a x upper i.val
    let lam := fun i : cells => g.packetPathProduct
      (g.sourceTransition tops slope precision cutoff weight K gap phase x) lower upper
      (slope (g.sourceBlockTop tops slope precision cutoff lower upper parent i))
    let n := g.mass tops slope precision cutoff weight lower parent x
    let parentAmplitude := g.sourcePacketAmplitude tops slope precision cutoff weight K gap
      packets assigned stop value phase a x lower parent
    let residual := g.packetResidual packets (fun s => slope (assigned s)) stop
      (g.sourcePacketBase tops slope precision cutoff weight assigned stop value a x)
      (g.sourceTransition tops slope precision cutoff weight K gap phase x) lower upper parent
    sourcePredictionValue p μ n c A lam =
      sourceNodeRatio n c A α p (parentAmplitude-residual) := by
  dsimp only
  obtain ⟨t,ht⟩ := hparent
  have hn := g.mass_pos_of_member tops slope precision cutoff weight hweight lower parent x ht
  have hc (i : g.sourceBlockCells tops slope precision cutoff lower upper parent) :
      0 < g.mass tops slope precision cutoff weight upper i.val x :=
    g.mass_pos_of_member tops slope precision cutoff weight hweight upper i.val x
      (g.sourceBlockTop_mem_child tops slope precision cutoff lower upper parent i)
  apply sourcePredictionValue_eq_residual_free_ratio _ _ _ _ _ _ μ α p hn hc hrelation
  exact g.sourcePacketAmplitude_block_children tops slope precision cutoff weight hprecision K gap
    packets assigned stop value phase a x hassigned heligible hle parent

end AngularGrid
end LipschitzHilbert

end

end OAI
