import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingDuhamel
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace OAI

/-! # Continuity of the moving-scale Duhamel map

Rescaling the integration time to the fixed unit interval gives strong
continuity, including at time zero, without operator-norm continuity.
-/

open Set MeasureTheory

namespace DefocusingNLS

attribute [local irreducible] expandingFreeStep expandingFreeFamily

private noncomputable def unitTime (u : ℝ) : Icc (0 : ℝ) 1 :=
  projIcc 0 1 zero_le_one u

private noncomputable def expandingDuhamelParameters (p : ExpandingFreeParameters)
    (u : ℝ) : ExpandingFreeParameters :=
  (⟨expandingRadius p.1.1 ((p.2 : ℝ) * unitTime u),
    p.1.2.trans (expandingRadius_ge _ _ p.1.2 (mul_nonneg p.2.2 (unitTime u).2.1))⟩,
   ⟨(p.2 : ℝ) - (p.2 : ℝ) * unitTime u,
    sub_nonneg.mpr (mul_le_of_le_one_right p.2.2 (unitTime u).2.2)⟩)

private theorem continuous_expandingDuhamelParameters :
    Continuous (fun z : ExpandingFreeParameters × ℝ => expandingDuhamelParameters z.1 z.2) := by
  have hL : Continuous (fun z : ExpandingFreeParameters × ℝ => z.1.1.1) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
  have hs : Continuous (fun z : ExpandingFreeParameters × ℝ => (z.1.2 : ℝ)) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
  have hu : Continuous (fun z : ExpandingFreeParameters × ℝ => (unitTime z.2 : ℝ)) :=
    continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd)
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    exact hL.mul (Real.continuous_exp.comp ((hs.mul hu).div_const 2))
  · apply Continuous.subtype_mk
    exact hs.sub (hs.mul hu)

private noncomputable def expandingUnitDuhamelIntegrand (a b k : ℝ)
    (ha : 0 < a) (hk : 8 < k) (r : ℝ → FourierL2)
    (p : ExpandingFreeParameters) (u : ℝ) : FourierL2 :=
  expandingFreeFamily a b k ha hk (expandingDuhamelParameters p u)
    (r ((p.2 : ℝ) * unitTime u))

private theorem continuous_expandingUnitDuhamelIntegrand (a b k : ℝ)
    (ha : 0 < a) (hk : 8 < k) (r : ℝ → FourierL2) (hr : Continuous r) :
    Continuous (fun z : ExpandingFreeParameters × ℝ =>
      expandingUnitDuhamelIntegrand a b k ha hk r z.1 z.2) := by
  have harg : Continuous (fun z : ExpandingFreeParameters × ℝ =>
      (expandingDuhamelParameters z.1 z.2, r ((z.1.2 : ℝ) * unitTime z.2))) := by
    apply continuous_expandingDuhamelParameters.prodMk
    apply hr.comp
    exact (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).mul
      (continuous_subtype_val.comp (continuous_projIcc.comp continuous_snd))
  unfold expandingUnitDuhamelIntegrand
  exact (continuous_expandingFreeFamily_uncurry a b k ha hk).comp harg

private theorem expandingUnitDuhamelIntegrand_eq (a b k : ℝ)
    (ha : 0 < a) (hk : 8 < k) (r : ℝ → FourierL2)
    (p : ExpandingFreeParameters) (u : ℝ) (hu : u ∈ Icc 0 1) :
    expandingUnitDuhamelIntegrand a b k ha hk r p u =
      expandingDuhamelIntegrand a b k p.1.1 ha hk p.1.2 p.2 r ((p.2 : ℝ) * u) := by
  have htu : (p.2 : ℝ) * u ∈ Icc (0 : ℝ) (p.2 : ℝ) :=
    ⟨mul_nonneg p.2.2 hu.1, mul_le_of_le_one_right p.2.2 hu.2⟩
  rw [expandingDuhamelIntegrand_of_mem _ _ _ _ _ _ _ _ _ _ htu]
  simp only [expandingUnitDuhamelIntegrand, expandingFreeFamily, expandingDuhamelParameters,
    unitTime, projIcc_of_mem _ hu]
  rfl

/-- A fixed unit-interval integral represents the moving-scale Duhamel term exactly. -/
theorem expandingDuhamel_eq_unitIntegral (a b k : ℝ)
    (ha : 0 < a) (hk : 8 < k) (r : ℝ → FourierL2)
    (p : ExpandingFreeParameters) :
    expandingDuhamel a b k p.1.1 ha hk p.1.2 p.2 r =
      (p.2 : ℝ) • ∫ u in Icc (0 : ℝ) 1,
        expandingUnitDuhamelIntegrand a b k ha hk r p u := by
  have hrescale := intervalIntegral.smul_integral_comp_mul_left
    (a := 0) (b := 1)
    (expandingDuhamelIntegrand a b k p.1.1 ha hk p.1.2 p.2 r) (p.2 : ℝ)
  simp only [mul_zero, mul_one] at hrescale
  rw [intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ (p.2 : ℝ) from p.2.2),
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc] at hrescale
  rw [expandingDuhamel, ← hrescale]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro u hu
  exact (expandingUnitDuhamelIntegrand_eq a b k ha hk r p u hu).symm

/-- The inhomogeneous solution depends strongly continuously on starting scale and time. -/
theorem continuous_expandingDuhamel (a b k : ℝ)
    (ha : 0 < a) (hk : 8 < k) (r : ℝ → FourierL2) (hr : Continuous r) :
    Continuous (fun p : ExpandingFreeParameters =>
      expandingDuhamel a b k p.1.1 ha hk p.1.2 p.2 r) := by
  let hLc : LocallyCompactSpace {L : ℝ // 1 ≤ L} :=
    (isClosed_Ici : IsClosed (Ici (1 : ℝ))).locallyCompactSpace
  let hSc : LocallyCompactSpace {s : ℝ // 0 ≤ s} :=
    (isClosed_Ici : IsClosed (Ici (0 : ℝ))).locallyCompactSpace
  let : LocallyCompactSpace ExpandingFreeParameters :=
    @Prod.locallyCompactSpace _ _ _ _ hLc hSc
  simp only [expandingDuhamel_eq_unitIntegral]
  exact (continuous_subtype_val.comp continuous_snd).smul
    (continuous_parametric_integral_of_continuous
      (continuous_expandingUnitDuhamelIntegrand a b k ha hk r hr) isCompact_Icc)

/-- Continuous forcing on a closed time slab yields a continuous inhomogeneous solution. -/
theorem continuousOn_expandingDuhamel (a b k L T : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (hT : 0 ≤ T)
    (r : ℝ → FourierL2) (hr : ContinuousOn r (Icc 0 T)) :
    ContinuousOn (fun t => expandingDuhamel a b k L ha hk hL t r) (Icc 0 T) := by
  let r' : ℝ → FourierL2 := fun t => r (projIcc 0 T hT t)
  have hr' : Continuous r' := hr.domRestrict.comp continuous_projIcc
  have hp : Continuous (fun t : Icc (0 : ℝ) T =>
      ((⟨L, hL⟩, ⟨t.1, t.2.1⟩) : ExpandingFreeParameters)) :=
    continuous_const.prodMk (continuous_subtype_val.subtype_mk _)
  rw [continuousOn_iff_continuous_domRestrict]
  convert (continuous_expandingDuhamel a b k ha hk r' hr').comp hp using 1
  apply funext
  intro t
  change expandingDuhamel a b k L ha hk hL t r =
    expandingDuhamel a b k L ha hk hL t r'
  unfold expandingDuhamel
  apply setIntegral_congr_fun measurableSet_Icc
  intro τ hτ
  rw [expandingDuhamelIntegrand_of_mem _ _ _ _ _ _ _ _ _ _ hτ,
    expandingDuhamelIntegrand_of_mem _ _ _ _ _ _ _ _ _ _ hτ]
  have hτT : τ ∈ Icc 0 T := ⟨hτ.1, hτ.2.trans t.2.2⟩
  simp only [r', projIcc_of_mem _ hτT]

end DefocusingNLS

end OAI
