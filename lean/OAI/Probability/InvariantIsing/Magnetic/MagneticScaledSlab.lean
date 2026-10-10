import OAI.Probability.InvariantIsing.Magnetic.MagneticSlabClosedDerivatives
import OAI.Probability.InvariantIsing.Fields.FieldScalarScaling

namespace OAI

/-! The literal scaled inverse curvature used in the radial comparison.
Time is physical variance; its scaling yields the coefficient αζ. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma fieldScaleIncrements_positive (c : ℝ≥0) (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) :
    ∀ av ∈ fieldScaleIncrements c L, 0 < av.1 := by
  intro av hav
  obtain ⟨bv, hb, rfl⟩ := List.mem_map.mp hav
  exact hL bv hb

lemma fieldScaleIncrements_exponent_le_one (c : ℝ≥0) (L : List (ℝ × ℝ≥0))
    (hL1 : ∀ av ∈ L, av.1 ≤ 1) :
    ∀ av ∈ fieldScaleIncrements c L, av.1 ≤ 1 := by
  intro av hav
  obtain ⟨bv, hb, rfl⟩ := List.mem_map.mp hav
  exact hL1 bv hb

lemma magneticThirdRatioCap_scale (c : ℝ≥0) (L : List (ℝ × ℝ≥0)) :
    magneticThirdRatioCap (fieldScaleIncrements c L) = magneticThirdRatioCap L := by
  induction L with
  | nil => rfl
  | cons av L ih => simp only [fieldScaleIncrements, List.map_cons, magneticThirdRatioCap] at *; rw [ih]

lemma magneticFourthRatioCap_scale (c : ℝ≥0) (L : List (ℝ × ℝ≥0)) :
    magneticFourthRatioCap (fieldScaleIncrements c L) = magneticFourthRatioCap L := by
  induction L with
  | nil => rfl
  | cons av L ih =>
    change magneticFourthRatioCap (fieldScaleIncrements c L) +
      8 * |av.1| * magneticThirdRatioCap (fieldScaleIncrements c L) + 3 * |av.1| + 37 * av.1 ^ 2 = _
    rw [ih, magneticThirdRatioCap_scale]
    rfl

lemma magneticSlabPotentialCap_scale (c : ℝ≥0) (L : List (ℝ × ℝ≥0)) (ζ : ℝ) :
    magneticSlabPotentialCap (fieldScaleIncrements c L) ζ = magneticSlabPotentialCap L ζ := by
  simp only [magneticSlabPotentialCap, magneticFourthRatioCap, magneticThirdRatioCap,
    magneticFourthRatioCap_scale, magneticThirdRatioCap_scale]

def magneticScaledClosedCurvature (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0) (ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (α : ℝ) * closedMagneticScalarCurvature (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) ζ ((α : ℝ) ^ 2 * p.1, p.2)

def magneticScaledClosedSlope (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0) (ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (α : ℝ) * closedMagneticScalarSlope (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) ζ ((α : ℝ) ^ 2 * p.1, p.2)

def magneticScaledClosedSecond (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0) (ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (α : ℝ) * closedMagneticScalarSecond (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) ζ ((α : ℝ) ^ 2 * p.1, p.2)

def magneticScaledClosedTime (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0) (ζ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (magneticScaledClosedCurvature L hL α ζ p) ^ 2 / 2 * magneticScaledClosedSecond L hL α ζ p +
    ((α : ℝ) * ζ) * (magneticScaledClosedCurvature L hL α ζ p) ^ 2

lemma magneticScaledClosedCurvature_hasDerivAt_time (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {α : ℝ≥0} (hα : 0 < α)
    {ζ v : ℝ} (hζ : 0 ≤ ζ) (hv : 0 < v) (s : ℝ) :
    HasDerivAt (fun t => magneticScaledClosedCurvature L hL α ζ (t, s))
      (magneticScaledClosedTime L hL α ζ (v, s)) v := by
  have hαr : 0 < (α : ℝ) := hα
  have ht := closedMagneticScalarCurvature_hasDerivAt_time (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) hζ (mul_pos (sq_pos_of_pos hαr) hv) s
  have hd := (ht.comp v ((hasDerivAt_id v).const_mul ((α : ℝ) ^ 2))).const_mul (α : ℝ)
  convert hd using 1
  · rfl
  · simp only [magneticScaledClosedTime, magneticScaledClosedCurvature,
      magneticScaledClosedSecond, closedMagneticScalarTime]
    ring

lemma magneticScaledClosedCurvature_hasDerivAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0)
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (fun u => magneticScaledClosedCurvature L hL α ζ (v, u))
      (magneticScaledClosedSlope L hL α ζ (v, s)) s :=
  (closedMagneticScalarCurvature_hasDerivAt_spin (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) hζ hs ((α : ℝ) ^ 2 * v)).const_mul (α : ℝ)

lemma magneticScaledClosedSlope_hasDerivAt_spin (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (α : ℝ≥0)
    {ζ s : ℝ} (hζ : 0 ≤ ζ) (hs : |s| < 1) (v : ℝ) :
    HasDerivAt (fun u => magneticScaledClosedSlope L hL α ζ (v, u))
      (magneticScaledClosedSecond L hL α ζ (v, s)) s :=
  (closedMagneticScalarSlope_hasDerivAt_spin (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) hζ hs ((α : ℝ) ^ 2 * v)).const_mul (α : ℝ)

lemma magneticScaledClosedCurvature_nil_initial {α : ℝ≥0} {ζ s : ℝ}
    (hζ : 0 ≤ ζ) (hs : s ∈ Icc (-1 : ℝ) 1) :
    magneticScaledClosedCurvature [] (by simp) α ζ (0, s) = (α : ℝ) * (1 - s ^ 2) := by
  simp only [magneticScaledClosedCurvature, mul_zero, fieldScaleIncrements, List.map_nil]
  by_cases hsi : |s| < 1
  · simp only [closedMagneticScalarCurvature, hsi, ite_true]
    rw [magneticScalarInverseCurvature_nil_initial hζ hsi]
  · have habs : |s| = 1 := le_antisymm (abs_le.mpr hs) (le_of_not_gt hsi)
    have hsq : s ^ 2 = 1 := by
      rw [← sq_abs, habs]
      norm_num
    simp only [closedMagneticScalarCurvature, hsi, ite_false, hsq, sub_self, mul_zero]

lemma magneticScaledClosedCurvature_continuousOn (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1) (α : ℝ≥0)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) :
    ContinuousOn (magneticScaledClosedCurvature L hL α ζ) (univ ×ˢ Icc (-1 : ℝ) 1) := by
  have hc := continuousOn_closedMagneticScalarCurvature (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) (fieldScaleIncrements_exponent_le_one α L hL1)
    hζ hζ1
  have hm : Continuous (fun p : ℝ × ℝ => ((α : ℝ) ^ 2 * p.1, p.2)) := by fun_prop
  exact continuousOn_const.mul (hc.comp hm.continuousOn (fun p hp => ⟨mem_univ _, hp.2⟩))

lemma magneticScaledClosedCurvature_mem_interval (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1) (α : ℝ≥0)
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (p : ℝ × ℝ)
    (hp : p.2 ∈ Icc (-1 : ℝ) 1) :
    magneticScaledClosedCurvature L hL α ζ p ∈ Icc 0 (α : ℝ) := by
  have h0 := closedMagneticScalarCurvature_nonneg (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) hζ ((α : ℝ) ^ 2 * p.1, p.2)
  have h1 := closedMagneticScalarCurvature_le_one (fieldScaleIncrements α L)
    (fieldScaleIncrements_positive α L hL) (fieldScaleIncrements_exponent_le_one α L hL1)
    hζ hζ1 ((α : ℝ) ^ 2 * p.1, p.2) hp
  exact ⟨mul_nonneg α.coe_nonneg h0, (mul_le_mul_of_nonneg_left h1 α.coe_nonneg).trans_eq (mul_one _)⟩

end InvariantIsing

end

end OAI
