import OAI.Geometry.IsometricImmersion.Caps.CapOverlapCosts

namespace OAI

noncomputable section
open Set
open scoped ContDiff

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry SmoothLocal.Flow SmoothLocal.ODE

def capOuterLeft (L : ℝ) : ℝ := capOuterEdge (capOuterEdge L)
def capOuterLeftOne (L : ℝ) : ℝ := capInnerEdge (capOuterEdge L)
def capOuterRightOne (R : ℝ) : ℝ := -capInnerEdge (capOuterEdge (-R))
def capOuterRight (R : ℝ) : ℝ := -capOuterEdge (capOuterEdge (-R))
def capOuterBottom (A : ℝ) : ℝ := capOuterEdge (capOuterEdge A)
def capOuterBottomOne (A : ℝ) : ℝ := capInnerEdge (capOuterEdge A)

theorem capOuterSpatialCutoff_eq_threeEdge (L R A : ℝ) :
    capOuterSpatialCutoff L R A =
      threeEdgeCutoff (capOuterLeft L) (capOuterLeftOne L) (capOuterRightOne R)
        (capOuterRight R) (capOuterBottom A) (capOuterBottomOne A) := by
  simp only [capOuterSpatialCutoff, capSpatialCutoff, neg_neg, capOuterLeft, capOuterLeftOne,
    capOuterRightOne, capOuterRight, capOuterBottom, capOuterBottomOne]

theorem capOuterRectangle_edges {L R A : ℝ}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) :
    -2 < capOuterLeft L ∧ capOuterLeft L < capOuterLeftOne L ∧ capOuterLeftOne L < -3/2 ∧
    3/2 < capOuterRightOne R ∧ capOuterRightOne R < capOuterRight R ∧ capOuterRight R < 2 ∧
    -2 < capOuterBottom A ∧ capOuterBottom A < capOuterBottomOne A ∧
    capOuterBottomOne A < A ∧ capOuterLeft L < L ∧ R < capOuterRight R := by
  obtain ⟨hlo,hli,hlu,hlx⟩ := capEdges_bounds hL
  obtain ⟨hro,hri,hru,hrx⟩ := capEdges_bounds (x := -R) (by linarith)
  obtain ⟨hao,hai,hau,hax⟩ := capEdges_bounds hA
  obtain ⟨hloo,hlio,hluo,hlxo⟩ := capEdges_bounds hlo
  obtain ⟨hroo,hrio,hruo,hrxo⟩ := capEdges_bounds hro
  obtain ⟨haoo,haio,hauo,haxo⟩ := capEdges_bounds hao
  unfold capOuterLeft capOuterLeftOne capOuterRightOne capOuterRight capOuterBottom capOuterBottomOne
  refine ⟨hloo,hlio,hluo,?_,?_,?_,haoo,haio,?_,?_,?_⟩ <;> linarith

theorem capOuterRectangle_subset_domain {L R A b : ℝ}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) (hb : b < 2) :
    closedRectangle (capOuterLeft L) (capOuterRight R) (capOuterBottom A) b ⊆ capChartDomain := by
  obtain ⟨hlo,hli,hlu,hri,hrr,hro,hao,hai,hau,hlx,hrx⟩ := capOuterRectangle_edges hL hR hA
  intro p hp
  exact ⟨⟨hlo.trans_le hp.1.1, hp.1.2.trans_lt hro⟩,
    ⟨hao.trans_le hp.2.1,hp.2.2.trans_lt hb⟩⟩

theorem capSpatialCutoff_outer_boundary {L R A b : ℝ}
    (hL : -2 < L) (hR : R < 2) (hA : -2 < A) :
    (∀ s ∈ Icc (capOuterBottom A) b,
      capSpatialCutoff L R A (boxPoint (capOuterLeft L) s) = 0 ∧
      capSpatialCutoff L R A (boxPoint (capOuterRight R) s) = 0) ∧
    (∀ t ∈ Icc (capOuterLeft L) (capOuterRight R),
      capSpatialCutoff L R A (boxPoint t (capOuterBottom A)) = 0) := by
  obtain ⟨hlo,hli,hlu,hlx⟩ := capEdges_bounds hL
  obtain ⟨hro,hri,hru,hrx⟩ := capEdges_bounds (x := -R) (by linarith)
  obtain ⟨hao,hai,hau,hax⟩ := capEdges_bounds hA
  have hlout : capOuterLeft L < capOuterEdge L := by
    have hh := capEdges_bounds hlo
    exact hh.2.1.trans hh.2.2.2
  have hrout : -capOuterEdge (-R) < capOuterRight R := by
    have hh := capEdges_bounds hro
    exact neg_lt_neg (hh.2.1.trans hh.2.2.2)
  have haout : capOuterBottom A < capOuterEdge A := by
    have hh := capEdges_bounds hao
    exact hh.2.1.trans hh.2.2.2
  constructor
  · intro s hs
    constructor
    · apply threeEdgeCutoff_zero hli (neg_lt_neg hri) hai
      exact Or.inl (by simpa [boxPoint] using hlout.le)
    · apply threeEdgeCutoff_zero hli (neg_lt_neg hri) hai
      exact Or.inr (Or.inl (by simpa [boxPoint] using hrout.le))
  · intro t ht
    apply threeEdgeCutoff_zero hli (neg_lt_neg hri) hai
    exact Or.inr (Or.inr (by simpa [boxPoint] using haout.le))

end SmoothLocal.Weighted

end

end OAI
