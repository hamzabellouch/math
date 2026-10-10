import OAI.Probability.InvariantIsing.Magnetic.MagneticContinuationClosedPDE
import OAI.Probability.InvariantIsing.Magnetic.MagneticScaledCurvatureOrder

namespace OAI

/-! The actual square continuation in the rescaled physical variance.
Its diffusion coefficient is the rescaled inverse curvature. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

def magneticScaledSquareJet (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0) (i : Fin (L.length + 1)) :
    MagneticContinuationJet :=
  (magneticScalarSquareFourJet (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL)
    (Fin.cast (by rw [fieldScaleIncrements_length]) i)).toMagneticContinuationJet

def magneticScaledSquareContinuation (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0) (i : Fin (L.length + 1))
    (ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  closedMagneticContinuation (fieldScaleIncrements α L)
    (magneticScaledSquareJet L hL α i) ζ ((α : ℝ) ^ 2 * p.1, p.2)

def magneticScaledSquareSlope (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0) (i : Fin (L.length + 1))
    (ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  closedMagneticContinuationSlope (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) (magneticScaledSquareJet L hL α i)
    ζ ((α : ℝ) ^ 2 * p.1, p.2)

def magneticScaledSquareSecond (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0) (i : Fin (L.length + 1))
    (ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  closedMagneticContinuationSecond (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) (magneticScaledSquareJet L hL α i)
    ζ ((α : ℝ) ^ 2 * p.1, p.2)

def magneticScaledSquareTime (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0) (i : Fin (L.length + 1))
    (ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (magneticScaledClosedCurvature L hL α ζ p) ^ 2 / 2 *
    magneticScaledSquareSecond L hL α i ζ p

lemma magneticScaledSquareContinuation_continuousOn (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0) (i : Fin (L.length + 1))
    {ζ : ℝ} (hζ : 0 ≤ ζ) :
    ContinuousOn (magneticScaledSquareContinuation L hL α i ζ)
      (univ ×ˢ Icc (-1 : ℝ) 1) := by
  have hc := continuousOn_closedMagneticContinuation (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) (magneticScaledSquareJet L hL α i)
    (magneticScalarSquareFourJet_sandwich _ _ _) hζ
  have hm : Continuous (fun p : ℝ × ℝ => ((α : ℝ) ^ 2 * p.1, p.2)) := by fun_prop
  exact hc.comp hm.continuousOn (fun p hp => ⟨mem_univ _, hp.2⟩)

lemma magneticScaledSquareContinuation_hasDerivAt_time (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {α : ℝ≥0} (hα : 0 < α)
    (i : Fin (L.length + 1)) {ζ v : ℝ} (hζ : 0 ≤ ζ) (hv : 0 < v) (s : ℝ) :
    HasDerivAt (fun t => magneticScaledSquareContinuation L hL α i ζ (t, s))
      (magneticScaledSquareTime L hL α i ζ (v, s)) v := by
  have hαr : 0 < (α : ℝ) := hα
  have hd := closedMagneticContinuation_hasDerivAt_time (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) (magneticScaledSquareJet L hL α i)
    hζ (mul_pos (sq_pos_of_pos hαr) hv) s
  have ht := hd.comp v ((hasDerivAt_id v).const_mul ((α : ℝ) ^ 2))
  convert ht using 1
  · rfl
  · simp only [magneticScaledSquareTime, magneticScaledClosedCurvature,
      magneticScaledSquareSecond, closedMagneticContinuationTime]
    ring

lemma magneticScaledSquareContinuation_hasDerivAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0) (i : Fin (L.length + 1))
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (fun u => magneticScaledSquareContinuation L hL α i ζ (v, u))
      (magneticScaledSquareSlope L hL α i ζ (v, s)) s :=
  closedMagneticContinuation_hasDerivAt_spin (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) (magneticScaledSquareJet L hL α i)
    hζ hs ((α : ℝ) ^ 2 * v)

lemma magneticScaledSquareSlope_hasDerivAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0) (i : Fin (L.length + 1))
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (fun u => magneticScaledSquareSlope L hL α i ζ (v, u))
      (magneticScaledSquareSecond L hL α i ζ (v, s)) s :=
  closedMagneticContinuationSlope_hasDerivAt_spin (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) (magneticScaledSquareJet L hL α i)
    hζ hs ((α : ℝ) ^ 2 * v)

lemma magneticScaledSquareSecond_nonneg (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    (α : ℝ≥0) (i : Fin (L.length + 1)) {ζ v : ℝ}
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hv : 0 ≤ v) (s : ℝ) :
    0 ≤ magneticScaledSquareSecond L hL α i ζ (v, s) :=
  closedMagneticSquareContinuationSecond_nonneg (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) (fieldScaleIncrements_exponent_le_one α L hL1)
    _ hζ hζ1 (mul_nonneg (sq_nonneg _) hv) s

end InvariantIsing

end

end OAI
