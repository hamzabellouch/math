import OAI.Analysis.LipschitzHilbert.Trees.SourceNodeRatio
import OAI.Analysis.LipschitzHilbert.Trees.SourceAmplitudeMeasurable
import OAI.Analysis.LipschitzHilbert.Trees.SourceMassStopping

namespace OAI

/-! Measurability of the original source node ratios and the finite active
path product. These are the integrands used for line-to-plane gluing,
independently of any selected snapshot predictors. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

variable {X : Type*} {ι κ : Type} [MeasurableSpace X] [Fintype ι] [Fintype κ]

theorem measurable_sourceNodeRatio (α p : ℝ) (n : X → ℝ) (c : X → ι → ℝ)
    (A : X → ι → EuclideanSpace ℂ κ) (parent : X → EuclideanSpace ℂ κ)
    (hn : Measurable n) (hc : ∀ i, Measurable (fun x => c x i))
    (hA : ∀ i, Measurable (fun x => A x i)) (hp : Measurable parent) :
    Measurable (fun x => sourceNodeRatio (n x) (c x) (A x) α p (parent x)) := by
  unfold sourceNodeRatio sourceNodeDenominator vertexAmount
  fun_prop

/-- Inactive indices have factor one, exactly as in the source path
expansion. The threshold is tested against the original forward masses. -/
def sourceActiveProduct (n beta : X → ℕ → ℝ) (M : ℝ) (count : ℕ) (x : X) : ℝ :=
  ∏ j ∈ Finset.range count, if M < n x j then beta x j else 1

theorem measurable_sourceActiveProduct (n beta : X → ℕ → ℝ) (M : ℝ) (count : ℕ)
    (hn : ∀ j, Measurable (fun x => n x j))
    (hb : ∀ j, Measurable (fun x => beta x j)) :
    Measurable (sourceActiveProduct n beta M count) := by
  unfold sourceActiveProduct
  apply Finset.measurable_prod
  intro j _
  exact Measurable.ite (measurableSet_lt measurable_const (hn j)) (hb j) measurable_const

omit [MeasurableSpace X] in
theorem sourceActiveProduct_nonneg (n beta : X → ℕ → ℝ) (M : ℝ) (count : ℕ)
    (x : X) (hb : ∀ j < count, M < n x j → 0 ≤ beta x j) :
    0 ≤ sourceActiveProduct n beta M count x := by
  apply Finset.prod_nonneg
  intro j hj
  split_ifs with h
  · exact hb j (Finset.mem_range.mp hj) h
  · exact zero_le_one

omit [MeasurableSpace X] in
/-- The measurable active product agrees exactly with the finite prefix
ending at the first mass crossing. The terminal mass may be zero. -/
theorem sourceActiveProduct_eq_stopped_product (n beta : X → ℕ → ℝ)
    (M : ℝ) (count : ℕ) (x : X) (hfinal : n x count ≤ M) (hanti : Antitone (n x)) :
    sourceActiveProduct n beta M count x =
      ∏ j ∈ Finset.range (firstMassStop (n x) count M), beta x j := by
  let stop := firstMassStop (n x) count M
  have hs : stop ≤ count := (firstMassStop_spec (n x) count M hfinal).1
  unfold sourceActiveProduct
  calc
    _ = ∏ j ∈ Finset.range stop, if M < n x j then beta x j else 1 := by
      symm
      apply Finset.prod_subset (Finset.range_mono hs)
      intro j _ hj
      have hjs : ¬j < stop := fun h => hj (Finset.mem_range.mpr h)
      have hn : ¬M < n x j := fun h => hjs
        ((firstMassStop_active_iff (n x) count M hfinal hanti j).mpr h)
      simp only [ite_eq_right hn]
    _ = ∏ j ∈ Finset.range stop, beta x j := by
      apply Finset.prod_congr rfl
      intro j hj
      exact ite_eq_left ((firstMassStop_active_iff (n x) count M hfinal hanti j).mp
        (Finset.mem_range.mp hj))

theorem sourceNodeRatio_nonneg (n : ℝ) (hn : 0 ≤ n) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (A : ι → EuclideanSpace ℂ κ) (α p : ℝ)
    (parent : EuclideanSpace ℂ κ) : 0 ≤ sourceNodeRatio n c A α p parent := by
  unfold sourceNodeRatio sourceNodeDenominator vertexAmount
  exact div_nonneg
    (add_nonneg hn (mul_nonneg (Real.rpow_nonneg hn _) (Real.rpow_nonneg (norm_nonneg _) _)))
    (add_nonneg hn (Finset.sum_nonneg (fun i _ =>
      mul_nonneg (Real.rpow_nonneg (hc i) _) (Real.rpow_nonneg (norm_nonneg _) _))))

namespace AngularGrid

/-- Actual packet amplitudes and original cell masses give measurable
node ratios, including at zero masses. -/
theorem source_packet_node_ratio_measurable {τ σ : Type*}
    (g : AngularGrid) (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ)
    (weight : τ → X → ℝ) (hw : ∀ t, Measurable (weight t))
    (K : ℕ) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ)
    (hv : ∀ s, Measurable (fun x => value x s)) (phase : ℕ → ℂ) (a α p : ℝ)
    (lower upper : ℕ) (parent : ℤ) :
    let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
    Measurable (fun x => sourceNodeRatio
      (g.mass tops slope precision cutoff weight lower parent x)
      (fun i : cells => g.mass tops slope precision cutoff weight upper i.val x)
      (fun i : cells => g.sourcePacketAmplitude tops slope precision cutoff weight K gap
        packets assigned stop (value x) phase a x upper i.val) α p
      (g.sourcePacketAmplitude tops slope precision cutoff weight K gap
        packets assigned stop (value x) phase a x lower parent)) := by
  dsimp only
  exact measurable_sourceNodeRatio α p _ _ _ _
    (g.measurable_mass tops slope precision cutoff weight hw lower parent)
    (fun i => g.measurable_mass tops slope precision cutoff weight hw upper i.val)
    (fun i => g.measurable_sourcePacketAmplitude tops slope precision cutoff weight hw K gap
      packets assigned stop value hv phase a upper i.val)
    (g.measurable_sourcePacketAmplitude tops slope precision cutoff weight hw K gap
      packets assigned stop value hv phase a lower parent)

end AngularGrid
end LipschitzHilbert

end

end OAI
