import OAI.Geometry.CylinderCovering.Rational.InversionDefinitions
import OAI.Geometry.CylinderCovering.Convexity.ThresholdInversion

namespace OAI

open Set
open scoped NNReal

namespace SlopeRational

lemma inverseRectangle_eq_box (d : ℝ) :
    inverseRectangle d =
      {p : Plane | ∀ i : Fin 2, p i ∈ Icc (![-1, -1] i) (![1, 1 / 2 + d / 2] i)} := by
  ext p
  simp [inverseRectangle, Fin.forall_fin_two, abs_le, and_assoc]

lemma inverseRectangle_isClosed (d : ℝ) : IsClosed (inverseRectangle d) := by
  unfold inverseRectangle
  have h0 : Continuous (fun p : Plane => |p 0|) := by fun_prop
  have h1 : Continuous (fun p : Plane => p 1) := by fun_prop
  exact (isClosed_le h0 continuous_const).inter
    ((isClosed_le continuous_const h1).inter (isClosed_le h1 continuous_const))

lemma inverseRectangle_isCompact {d : ℝ} (hd : 0 < d) :
    IsCompact (inverseRectangle d) := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨inverseRectangle_isClosed d, isBounded_iff_forall_norm_le.mpr ?_⟩
  refine ⟨2 + d, ?_⟩
  intro p hp
  rcases hp with ⟨hp0, hp1lo, hp1hi⟩
  have hp1 : |p 1| ≤ 1 + d := by
    apply abs_le.mpr
    constructor <;> linarith
  have hnorm := EuclideanSpace.norm_sq_eq p
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] at hnorm
  have hp0sq : (p 0) ^ 2 ≤ 1 := by
    have hs := (sq_le_sq₀ (abs_nonneg (p 0)) (by norm_num : (0 : ℝ) ≤ 1)).mpr hp0
    simpa only [sq_abs, one_pow] using hs
  have hp1sq : (p 1) ^ 2 ≤ (1 + d) ^ 2 := by
    have hs := (sq_le_sq₀ (abs_nonneg (p 1)) (by positivity : 0 ≤ 1 + d)).mpr hp1
    simpa only [sq_abs] using hs
  nlinarith [norm_nonneg p]

lemma inverseRectangle_convex (d : ℝ) : Convex ℝ (inverseRectangle d) := by
  rw [inverseRectangle_eq_box]
  have heq : {p : Plane | ∀ i : Fin 2, p i ∈ Icc (![-1, -1] i) (![1, 1 / 2 + d / 2] i)} =
      ⋂ i : Fin 2, {p : Plane | p i ∈ Icc (![-1, -1] i) (![1, 1 / 2 + d / 2] i)} := by
    ext p
    simp
  rw [heq]
  exact convex_iInter fun i =>
    (convex_Icc _ _).linear_preimage (PiLp.projₗ 2 (fun _ : Fin 2 => ℝ) i)

lemma inverseRectangle_denominator_pos {d : ℝ} (hd : 0 < d)
    {p : Plane} (hp : p ∈ inverseRectangle d) : 0 < radius (p 1) + d := by
  have ht := hp.2.2
  unfold radius
  linarith

lemma field_contDiffOn_inverseRectangle {d : ℝ} (hd : 0 < d) :
    ContDiffOn ℝ 1 (field d) (inverseRectangle d) := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  have hden : 0 < 1 / 2 - p 1 + d := inverseRectangle_denominator_pos hd hp
  unfold field vec2
  apply PiLp.contDiff_toLp.contDiffAt.comp p
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · change ContDiffAt ℝ 1 (fun z : Plane => a d (z 0) (z 1)) p
    unfold a radius
    fun_prop (disch := positivity)
  · change ContDiffAt ℝ 1 (fun z : Plane => b d (z 0) (z 1)) p
    unfold b radius
    fun_prop (disch := positivity)

lemma rectangleInversion_of_contDiff {d : ℝ} (hd : 0 < d)
    (hregular : ContDiffOn ℝ 1 (field d) (inverseRectangle d)) : RectangleInversionAt d := by
  obtain ⟨L, hL⟩ := hregular.exists_lipschitzOnWith (by norm_num)
    (inverseRectangle_convex d) (inverseRectangle_isCompact hd)
  obtain ⟨B₀, hB₀⟩ := (inverseRectangle_isCompact hd).exists_bound_of_continuousOn
    hregular.continuousOn
  let B := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hbound : ∀ p ∈ inverseRectangle d, ‖field d p‖ ≤ B := by
    intro p hp
    exact (hB₀ p hp).trans (le_max_left _ _)
  let margin := min (1 / 2 : ℝ) (d / 2)
  have hm : 0 < margin := lt_min (by norm_num) (by positivity)
  obtain ⟨δ, hδ, hsmall⟩ := CylinderCovering.ThresholdInversion.exists_small_tilt
    (L : ℝ) B margin L.coe_nonneg hB hm
  refine ⟨δ, hδ, ?_⟩
  intro s hs
  obtain ⟨hsL, hsB⟩ := hsmall s hs
  constructor
  · intro y t hy ht
    have hbox := CylinderCovering.ThresholdInversion.existsUnique_inverse_on_box_smul
      (![-1, -1] : Fin 2 → ℝ) (![1, 1 / 2 + d / 2] : Fin 2 → ℝ) hm.le
      (W := field d) (L := (L : ℝ)) (B := B) (t := s) L.coe_nonneg hB
    have hlip : ∀ p : Plane, (∀ i, p i ∈ Icc (![-1, -1] i) (![1, 1 / 2 + d / 2] i)) →
        ∀ q : Plane, (∀ i, q i ∈ Icc (![-1, -1] i) (![1, 1 / 2 + d / 2] i)) →
          ‖field d p - field d q‖ ≤ (L : ℝ) * ‖p - q‖ := by
      intro p hp q hq
      have hp' : p ∈ inverseRectangle d := by rw [inverseRectangle_eq_box]; exact hp
      have hq' : q ∈ inverseRectangle d := by rw [inverseRectangle_eq_box]; exact hq
      simpa only [dist_eq_norm] using hL.dist_le_mul p hp' q hq'
    have hb : ∀ p : Plane, (∀ i, p i ∈ Icc (![-1, -1] i) (![1, 1 / 2 + d / 2] i)) →
        ‖field d p‖ ≤ B := by
      intro p hp
      exact hbound p (by rwa [inverseRectangle_eq_box])
    have htarget : ∀ i : Fin 2,
        ![-1, -1] i + margin ≤ vec2 y t i ∧
        vec2 y t i ≤ ![1, 1 / 2 + d / 2] i - margin := by
      have hm1 : margin ≤ 1 / 2 := min_le_left _ _
      have hmd : margin ≤ d / 2 := min_le_right _ _
      have hy' := abs_le.mp hy
      have ht' := abs_le.mp ht
      intro i
      fin_cases i
      · change -1 + margin ≤ y ∧ y ≤ 1 - margin
        constructor <;> linarith
      · change -1 + margin ≤ t ∧ t ≤ 1 / 2 + d / 2 - margin
        constructor <;> linarith
    have hex := hbox hlip hb (by linarith) hsB (vec2 y t) htarget
    simpa only [inverseRectangle_eq_box, tiltedMap, Set.mem_ofPred_eq] using hex
  · intro p hp q hq hhorizontal hvertical
    apply CylinderCovering.ThresholdInversion.inverse_coordinate_strict (i := (1 : Fin 2))
      (c := |s| * (L : ℝ)) (mul_nonneg (abs_nonneg _) L.coe_nonneg) hsL
      (g := fun z => s • field d z) (y := tiltedMap d s p) (z := tiltedMap d s q)
      rfl rfl
    · rw [← smul_sub, norm_smul, Real.norm_eq_abs]
      have hLip := hL.dist_le_mul q hq p hp
      simp only [dist_eq_norm] at hLip
      calc
        |s| * ‖field d q - field d p‖ ≤ |s| * ((L : ℝ) * ‖q - p‖) :=
          mul_le_mul_of_nonneg_left hLip (abs_nonneg _)
        _ = |s| * (L : ℝ) * ‖q - p‖ := by ring
    · intro j hj
      fin_cases j
      · exact hhorizontal.symm
      · exact (hj rfl).elim
    · exact hvertical

theorem rectangleInversion_main : RectangleInversionStatement := by
  intro d hd
  exact rectangleInversion_of_contDiff hd (field_contDiffOn_inverseRectangle hd)

end SlopeRational

end OAI
