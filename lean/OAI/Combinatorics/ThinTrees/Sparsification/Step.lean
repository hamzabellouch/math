import Mathlib
import OAI.Combinatorics.ThinTrees.Sparsification.GraphCertificates
import OAI.Combinatorics.ThinTrees.Sparsification.HalfNumeric

namespace OAI

/-! Sparsification step. -/

section

namespace AlgorithmicThinTrees.GraphicHalf
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open MetricTests MetricTests.RationalStep Normalization RationalSigning
open scoped MatrixOrder
variable {d m : ℕ}

def sparsify (G : MultiGraph (d+1) m) (r : ℕ) : Finset (Fin m) :=
  let a := extractState G r
  halfEdges G a.active a.matrix (normalizedScales a.packingTarget r (graphColumns G a.active))

theorem sparsification_correct : ∃R : ℕ, 4 ≤ R ∧ ∀r : ℕ, R ≤ r →
    ∀(d m : ℕ) (G : MultiGraph (d+1) m), 2 ≤ d+1 → G.TreePackable univ r →
      (r:ℝ)/4 ≤ nextCount r ∧ (nextCount r:ℝ) ≤ (r:ℝ)/2 ∧ 0 < nextCount r ∧
      G.TreePackable (sparsify G r) (nextCount r) ∧
      (∀S : Finset (Fin (d+1)), ((G.cut (sparsify G r) S).card:ℝ) ≤
        (1/2+3*halfError r)*(G.cut univ S).card) ∧
      (1/2+3*halfError r)*(r:ℝ) ≤ (1+80*errorU r)*nextCount r := by
  obtain ⟨R₁,hR₁,hstep⟩ := shortcut_correct
  obtain ⟨R₂,hnum⟩ := eventual_numeric
  refine ⟨max R₁ R₂,?_,?_⟩
  · exact (by norm_num : 4 ≤ 64^16).trans (hR₁.trans (le_max_left _ _))
  intro r hr d m G hn hp
  have hr₁ := (le_max_left _ _).trans hr
  have hr₂ := (le_max_right _ _).trans hr
  have hnumer := hnum r hr₂
  have hr0 : 0 < r := by have := hnumer.rlarge; omega
  have hconn := packing_connected G hr0 hp
  obtain ⟨hX,hpack,hqpos,hqr,hqbound,hres⟩ := hstep r hr₁ (d+1) m G hn hp
  let a := extractState G r
  let B := a.active
  let q := a.packingTarget
  let s := normalizedScales q r (graphColumns G B)
  have hX' : a.realMatrix ∈ metricDomain G := hX
  have hqr' : (1-6*errorU r)*(r:ℝ) ≤ q := hqbound
  obtain ⟨hs,hleverage,hbits⟩ := graphic_normalization G B hqpos hqr hpack
  change (∀e, 0 < s e ∧ s e ≤ 1) at hs
  change (∀e, leverage (realColumns (graphColumns G B)) (realWeights s) e ≤ (1+4/(r:ℝ))/(q:ℝ)) at hleverage
  have hQ : ((scaledForm G B s).map (fun x : ℚ => (x:ℝ))).PosDef := by
    rw [scaledForm_cast]
    obtain ⟨F⟩ := graph_containedPacking G B hqpos hpack
    exact F.covariance_posDef _ (realWeights_box hs).1
  have hnorm : ∀e, realVec (fullColumns G B) e ⬝ᵥ
      (((positiveForm a.matrix).map (fun x : ℚ => (x:ℝ)))⁻¹*ᵥrealVec (fullColumns G B) e)+
      leverage (realColumns (graphColumns G B)) (realWeights s) e ≤ varianceBound r := by
    intro e
    have hlev := (hleverage e).trans (normalized_size hnumer hqr')
    have hfirst : realVec (fullColumns G B) e ⬝ᵥ
        (((positiveForm a.matrix).map (fun x : ℚ => (x:ℝ)))⁻¹*ᵥrealVec (fullColumns G B) e) ≤
        (r:ℝ)^(-1/4:ℝ) := by
      rw [fullColumns_cast,positiveForm_cast]
      by_cases he : e ∈ B
      · rw [ite_eq_left he]
        exact hres e he
      · rw [ite_eq_right he,zero_dotProduct]
        exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    unfold varianceBound
    linarith only [hfirst,hlev]
  obtain ⟨hlap,hframe⟩ := half_bounds G B a.matrix s hconn hX' hQ
    (show 0 ≤ varianceBound r by unfold varianceBound; positivity) hnorm
  change G.laplacian (sparsify G r) ≤ (1/2:ℝ) • G.laplacian B+
    halfError r • regularize a.realMatrix at hlap
  change (1/2-halfError r) • (scaledForm G B s).map (fun x : ℚ => (x:ℝ)) ≤
    StackedSigning.gram (realVec (scaledColumns G B s)) (sparsify G r) at hframe
  obtain ⟨hlo,hhi,hpos⟩ := nextCount_bounds hnumer
  refine ⟨hlo,hhi,hpos,?_,?_,half_ratio hnumer⟩
  · apply packing_bound G hn B (sparsify G r) inter_subset_right s (fun e => (hs e).1) hQ
      (c:=1/2-halfError r) (h:=(1+4/(r:ℝ))/(q:ℝ))
    · linarith only [hnumer.loss,hnumer.small]
    · positivity
    · exact packing_numeric hnumer hqpos hqr'
    · intro e _; exact hleverage e
    · exact hframe
  · intro S
    exact cut_bound G (by omega) (sparsify G r) B hX'
      (by unfold halfError; positivity) hlap S

end AlgorithmicThinTrees.GraphicHalf
end

end OAI
