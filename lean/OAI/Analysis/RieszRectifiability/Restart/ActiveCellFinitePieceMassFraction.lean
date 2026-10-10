import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.LatticeMassPacking
import OAI.Analysis.RieszRectifiability.Restart.ActiveCellFinitePieceAssembly

namespace OAI

/-!
# Retained mass from finite-piece assembly

For finite mass, two relative deficit bounds leave at least the fraction `1 - δ - η` in the
retained set. Applying this estimate to parent surface loss and uncovered child mass upgrades
finite-piece assembly to a chart with an explicit retained cell-mass fraction, while preserving
its Lipschitz bound and image containment.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem mass_fraction_of_two_deficits (m a b c : ℝ≥0∞) (hm : m ≠ ⊤)
    (δ η : ℝ) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hmass : m ≤ a + b + c)
    (hb : b ≤ ENNReal.ofReal δ * m) (hc : c ≤ ENNReal.ofReal η * m) :
    ENNReal.ofReal (1 - δ - η) * m ≤ a := by
  have htotal : m ≤ a + ENNReal.ofReal (δ + η) * m := by
    have h := hmass.trans (add_le_add (add_le_add le_rfl hb) hc)
    simpa only [ENNReal.ofReal_add hδ hη, add_mul, add_assoc] using! h
  rw [sub_sub, ENNReal.ofReal_sub 1 (add_nonneg hδ hη), ENNReal.ofReal_one,
    ENNReal.sub_mul (fun _ _ => hm), one_mul]
  exact tsub_le_iff_right.mpr htotal

theorem exists_active_cell_chart_with_retained_mass_fraction {n d : ℕ} (hn : 0 < n)
    (μ : Measure (Ambient d)) (G : ℝ) (hG : 0 < G) (hg : GlobalUpperGrowth n G μ)
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεfine : ε ≤ 1 / 281474976710656) (hsmall : activeProjectionError d ε ≤ 1 / 128)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (q : SupportCellDescendant μ R hR k z) (hq : activeRegionCell Good q)
    (N : ℕ) (D : Fin N → Set (Ambient n))
    (hD : ∀ j, D j ⊆ ball (0 : Ambient n) q.radius)
    (piece : Fin N → Ambient n → Ambient d) (P : ℝ≥0)
    (hpieceLip : ∀ j, LipschitzOnWith P (piece j) (D j))
    (hpieceImage : ∀ j, piece j '' D j ⊆ closedBall q.center (3 * q.radius))
    (E : Set (Ambient d)) (hE : E = ⋃ j : Fin N, piece j '' D j)
    (child : ∀ i : activeCellSelectedStopSet μ R hR k z Good q E,
      ball (0 : Ambient n) i.val.radius → Ambient d)
    (M : ℝ≥0) (hLip : ∀ i, LipschitzWith M (child i))
    (himage : ∀ i, Set.range (child i) ⊆ closedBall i.val.center (2 * i.val.radius))
    (δ η : ℝ) (hδ : 0 ≤ δ) (hη : 0 ≤ η)
    (hparentLoss : (ENNReal.ofReal G + activeRegionStopMassAreaConstant n G) *
      (μH[(n : ℝ)] : Measure (Ambient d))
        ((Set.range f ∩ closedBall q.center (3 * q.radius)) \ E) ≤ ENNReal.ofReal δ * μ q.cell)
    (hchildLoss : (∑' i : activeCellSelectedStopSet μ R hR k z Good q E,
      μ (i.val.cell \ Set.range (child i))) ≤ ENNReal.ofReal η * μ q.cell) :
    ∃ g : ball (0 : Ambient n) q.radius → Ambient d,
      LipschitzWith (activeCellFinitePieceAssemblyConstant d N P M) g ∧
      Set.range g ⊆ closedBall q.center (2 * q.radius) ∧
      ENNReal.ofReal (1 - δ - η) * μ q.cell ≤ μ (q.cell ∩ Set.range g) := by
  obtain ⟨g, hgLip, hgRange, hmass⟩ := exists_active_cell_chart_from_finite_pieces hn μ G hG hg
    R hR k z Good S hS ε hε hεfine hsmall hfit f hmodel q hq N D hD
    piece P hpieceLip hpieceImage E hE child M hLip himage
  have hfinite : μ q.cell ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (q.measure_upper G hg)
  exact ⟨g, hgLip, hgRange,
    mass_fraction_of_two_deficits _ _ _ _ hfinite δ η hδ hη hmass hparentLoss hchildLoss⟩

end

end RieszRectifiability

end OAI
