import OAI.Geometry.IsometricImmersion.Caps.EllipticCutoff

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.Weighted
open SmoothLocal.Geometry

theorem coordLinear_norm_le (L : Coord →L[ℝ] ℝ) :
    ‖L‖ ≤ |L (Pi.single 0 1)| + |L (Pi.single 1 1)| := by
  apply L.opNorm_le_bound (add_nonneg (abs_nonneg _) (abs_nonneg _))
  intro v
  have he : v = v 0 • Pi.single 0 (1 : ℝ) + v 1 • Pi.single 1 (1 : ℝ) := by
    ext i
    fin_cases i <;> simp
  have hv0 : |v 0| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 0
  have hv1 : |v 1| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v 1
  calc
    ‖L v‖ = |v 0 * L (Pi.single 0 1) + v 1 * L (Pi.single 1 1)| := by
      conv_lhs => rw [he]
      simp only [map_add, map_smul, smul_eq_mul, Real.norm_eq_abs]
    _ ≤ |v 0| * |L (Pi.single 0 1)| + |v 1| * |L (Pi.single 1 1)| := by
      simpa only [abs_mul] using abs_add_le
        (v 0 * L (Pi.single 0 1)) (v 1 * L (Pi.single 1 1))
    _ ≤ ‖v‖ * |L (Pi.single 0 1)| + ‖v‖ * |L (Pi.single 1 1)| :=
      add_le_add (mul_le_mul_of_nonneg_right hv0 (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hv1 (abs_nonneg _))
    _ = (|L (Pi.single 0 1)| + |L (Pi.single 1 1)|) * ‖v‖ := by ring

def ellipticEdgeRaw (c : ℝ) : Coord → ℝ :=
  ellipticWeight 0 c (fun _ => 1) (fun p => p 0)

def ellipticEdgeKernel (c : ℝ) (p : Coord) : ℝ :=
  if p 1 < 0 then ellipticEdgeRaw c p else 0

def ellipticEdgeDerivative (c : ℝ) (p : Coord) : Coord →L[ℝ] ℝ :=
  if p 1 < 0 then fderiv ℝ (ellipticEdgeRaw c) p else 0

def ellipticEdgeDerivativeConstant (c : ℝ) : ℝ :=
  4 * (3 + (2 * transitionDerivativeBound / c) * (1 + c))

theorem ellipticEdgeRaw_contDiffOn (c : ℝ) :
    ContDiffOn ℝ ∞ (ellipticEdgeRaw c) {p | p 1 < 0} := by
  exact ellipticWeight_contDiffOn 0 c contDiffOn_const
    (contDiffOn_apply ℝ ℝ 0 _) (fun _ h => h)

theorem ellipticEdgeHalfPlane_isOpen : IsOpen {p : Coord | p 1 < 0} :=
  isOpen_lt (continuous_apply 1) continuous_const

theorem ellipticEdgeKernel_norm_le (c : ℝ) (p : Coord) :
    ‖ellipticEdgeKernel c p‖ ≤ |p 1| ^ 6 := by
  unfold ellipticEdgeKernel
  split_ifs with hp
  · unfold ellipticEdgeRaw
    rw [Real.norm_eq_abs, abs_of_nonneg (ellipticWeight_nonneg _ _ _ _ _)]
    have h := ellipticWeight_le_distance_six 0 c (fun _ => 1) (fun p => p 0) p
      ⟨by norm_num, le_rfl⟩
    simpa only [edgeDistance, zero_sub, abs_of_neg hp] using h
  · simp

theorem ellipticEdgeRaw_partial_bound {c : ℝ} (hc : 0 < c) {p : Coord}
    (hp : p 1 < 0) (i : Fin 2) :
    |coordPartial i (ellipticEdgeRaw c) p| ≤
      (ellipticEdgeDerivativeConstant c / 2) * (-p 1) ^ 5 := by
  have hd : 0 < edgeDistance 0 p := by simpa only [edgeDistance, zero_sub] using neg_pos.mpr hp
  have hk : |coordPartial i (fun q : Coord => q 0) p| ≤ (1 : ℝ) := by
    unfold coordPartial
    rw [(hasFDerivAt_apply (𝕜 := ℝ) 0 p).fderiv]
    fin_cases i <;> norm_num [Pi.single_apply]
  have hx : |coordPartial i (fun _ : Coord => (1 : ℝ)) p| ≤ (0 : ℝ) := by
    simp [coordPartial]
  have hh := ellipticWeight_partial_bound (b := 0) (c := c) (M := 1) (X := 0)
    hc hd (by norm_num) (differentiableAt_const 1)
    (differentiableAt_apply (𝕜 := ℝ) 0 p) ⟨by norm_num, le_rfl⟩ i hx hk
  have hsqrt : Real.sqrt (ellipticEdgeRaw c p) ≤ (edgeDistance 0 p) ^ 3 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨(pow_pos hd 3).le, ?_⟩
    dsimp only [ellipticEdgeRaw]
    convert ellipticWeight_le_distance_six 0 c (fun _ => 1) (fun p => p 0) p
      ⟨by norm_num, le_rfl⟩ using 1
    ring
  have hP : 0 ≤ (2 * transitionDerivativeBound / c) * (1 + c) :=
    mul_nonneg (div_nonneg (mul_nonneg (by norm_num) transitionDerivativeBound_pos.le) hc.le)
      (by linarith)
  calc
    _ ≤ 2 * Real.sqrt (ellipticEdgeRaw c p) *
        (3 * edgeDistance 0 p ^ 2 + edgeDistance 0 p ^ 3 * 0 +
          edgeDistance 0 p ^ 2 * ((2 * transitionDerivativeBound / c) * (1 + c))) := hh
    _ ≤ 2 * edgeDistance 0 p ^ 3 *
        (3 * edgeDistance 0 p ^ 2 + edgeDistance 0 p ^ 3 * 0 +
          edgeDistance 0 p ^ 2 * ((2 * transitionDerivativeBound / c) * (1 + c))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt (by norm_num))
        (by positivity)
    _ = _ := by unfold ellipticEdgeDerivativeConstant edgeDistance; ring

theorem ellipticEdgeDerivative_norm_le {c : ℝ} (hc : 0 < c) (p : Coord) :
    ‖ellipticEdgeDerivative c p‖ ≤ ellipticEdgeDerivativeConstant c * |p 1| ^ 5 := by
  have hC : 0 ≤ ellipticEdgeDerivativeConstant c := by
    unfold ellipticEdgeDerivativeConstant
    have := transitionDerivativeBound_pos
    positivity
  unfold ellipticEdgeDerivative
  split_ifs with hp
  · calc
      _ ≤ |coordPartial 0 (ellipticEdgeRaw c) p| +
          |coordPartial 1 (ellipticEdgeRaw c) p| := coordLinear_norm_le _
      _ ≤ (ellipticEdgeDerivativeConstant c / 2) * (-p 1) ^ 5 +
          (ellipticEdgeDerivativeConstant c / 2) * (-p 1) ^ 5 :=
        add_le_add (ellipticEdgeRaw_partial_bound hc hp 0)
          (ellipticEdgeRaw_partial_bound hc hp 1)
      _ = _ := by rw [abs_of_neg hp]; ring
  · simp only [norm_zero]
    exact mul_nonneg hC (pow_nonneg (abs_nonneg _) _)

theorem ellipticEdgeKernel_hasFDerivAt_boundary (c : ℝ) {p : Coord} (hp : p 1 = 0) :
    HasFDerivAt (ellipticEdgeKernel c) (0 : Coord →L[ℝ] ℝ) p := by
  have hpzero : ellipticEdgeKernel c p = 0 := by simp [ellipticEdgeKernel, hp]
  rw [hasFDerivAt_iff_tendsto]
  simp only [hpzero, sub_zero, zero_apply]
  apply squeeze_zero (fun q => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
  · intro q
    have hcoord : |q 1| ≤ ‖q - p‖ := by
      simpa only [Pi.sub_apply, hp, sub_zero, Real.norm_eq_abs] using norm_le_pi_norm (q - p) 1
    have hb : ‖ellipticEdgeKernel c q‖ ≤ ‖q - p‖ ^ 6 :=
      (ellipticEdgeKernel_norm_le c q).trans (pow_le_pow_left₀ (abs_nonneg _) hcoord 6)
    calc
      ‖q - p‖⁻¹ * ‖ellipticEdgeKernel c q‖ ≤ ‖q - p‖⁻¹ * ‖q - p‖ ^ 6 :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (norm_nonneg _))
      _ = ‖q - p‖ ^ 5 := by
        by_cases hz : ‖q - p‖ = 0
        · simp [hz]
        · field_simp [hz]
  · have hcont : Continuous (fun q : Coord => ‖q - p‖ ^ 5) :=
      (continuous_id.sub continuous_const).norm.pow 5
    simpa using hcont.tendsto p

theorem ellipticEdgeKernel_hasFDerivAt (c : ℝ) (p : Coord) :
    HasFDerivAt (ellipticEdgeKernel c) (ellipticEdgeDerivative c p) p := by
  rcases lt_trichotomy (p 1) 0 with hp | hp | hp
  · have hn := ellipticEdgeHalfPlane_isOpen.mem_nhds hp
    have hd := ((ellipticEdgeRaw_contDiffOn c).contDiffAt hn).differentiableAt (by simp)
    have he : ellipticEdgeKernel c =ᶠ[𝓝 p] ellipticEdgeRaw c := by
      filter_upwards [hn] with q hq
      simp [ellipticEdgeKernel, hq]
    simpa only [ellipticEdgeDerivative, hp, ite_eq_left] using hd.hasFDerivAt.congr_of_eventuallyEq he
  · simpa [ellipticEdgeDerivative, hp] using ellipticEdgeKernel_hasFDerivAt_boundary c hp
  · have hn : {q : Coord | 0 < q 1} ∈ 𝓝 p :=
      (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hp
    have he : ellipticEdgeKernel c =ᶠ[𝓝 p] (fun _ => 0) := by
      filter_upwards [hn] with q hq
      simp [ellipticEdgeKernel, not_lt_of_ge hq.le]
    simpa [ellipticEdgeDerivative, not_lt_of_ge hp.le] using
      (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) p).congr_of_eventuallyEq he

theorem ellipticEdgeDerivative_continuous {c : ℝ} (hc : 0 < c) :
    Continuous (ellipticEdgeDerivative c) := by
  rw [continuous_iff_continuousAt]
  intro p
  rcases lt_trichotomy (p 1) 0 with hp | hp | hp
  · have hn := ellipticEdgeHalfPlane_isOpen.mem_nhds hp
    have hd := ((ellipticEdgeRaw_contDiffOn c).continuousOn_fderiv_of_isOpen
      ellipticEdgeHalfPlane_isOpen (by simp)).continuousAt hn
    apply hd.congr_of_eventuallyEq
    filter_upwards [hn] with q hq
    simp [ellipticEdgeDerivative, hq]
  · have hz : ellipticEdgeDerivative c p = 0 := by simp [ellipticEdgeDerivative, hp]
    change Tendsto (ellipticEdgeDerivative c) (𝓝 p) (𝓝 (ellipticEdgeDerivative c p))
    rw [hz, tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) (ellipticEdgeDerivative_norm_le hc)
    have hcont : Continuous (fun q : Coord => ellipticEdgeDerivativeConstant c * |q 1| ^ 5) :=
      continuous_const.mul (((continuous_apply 1).abs).pow 5)
    simpa [hp] using hcont.tendsto p
  · have hn : {q : Coord | 0 < q 1} ∈ 𝓝 p :=
      (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hp
    apply (continuousAt_const (y := (0 : Coord →L[ℝ] ℝ))).congr_of_eventuallyEq
    filter_upwards [hn] with q hq
    simp [ellipticEdgeDerivative, not_lt_of_ge hq.le]

theorem ellipticEdgeKernel_contDiff_one {c : ℝ} (hc : 0 < c) :
    ContDiff ℝ 1 (ellipticEdgeKernel c) :=
  contDiff_one_iff_hasFDerivAt.mpr
    ⟨ellipticEdgeDerivative c, ellipticEdgeDerivative_continuous hc,
      ellipticEdgeKernel_hasFDerivAt c⟩

def ellipticWeightC1 (b c : ℝ) (chi K : Coord → ℝ) (p : Coord) : ℝ :=
  chi p ^ 2 * ellipticEdgeKernel c ![K p, p 1 - b]

theorem ellipticWeightC1_eq {b c : ℝ} {chi K : Coord → ℝ} {p : Coord}
    (hp : p 1 ≤ b) : ellipticWeightC1 b c chi K p = ellipticWeight b c chi K p := by
  rcases hp.eq_or_lt with he | hl
  · simp [ellipticWeightC1, ellipticEdgeKernel, ellipticWeight, edgeDistance, he]
  · have hs : p 1 - b < 0 := sub_neg.mpr hl
    simp only [ellipticWeightC1, ellipticEdgeKernel, Matrix.cons_val_one, Matrix.cons_val_zero,
      hs, ite_eq_left, ellipticEdgeRaw, ellipticWeight, edgeDistance]
    simp only [one_pow, mul_one]
    have hd : 0 - (p 1 - b) = b - p 1 := by ring
    rw [hd]
    ring

theorem ellipticWeightC1_zero {b c : ℝ} {chi K : Coord → ℝ} {p : Coord}
    (hp : b ≤ p 1) : ellipticWeightC1 b c chi K p = 0 := by
  simp [ellipticWeightC1, ellipticEdgeKernel, not_lt_of_ge (sub_nonneg.mpr hp)]

theorem ellipticWeightC1_nonneg (b c : ℝ) (chi K : Coord → ℝ) (p : Coord) :
    0 ≤ ellipticWeightC1 b c chi K p := by
  by_cases hp : p 1 ≤ b
  · rw [ellipticWeightC1_eq hp]
    exact ellipticWeight_nonneg _ _ _ _ _
  · rw [ellipticWeightC1_zero (lt_of_not_ge hp).le]

theorem ellipticWeightC1_le_distance_six (b c : ℝ) (chi K : Coord → ℝ) (p : Coord)
    (hchi : 0 ≤ chi p ∧ chi p ≤ 1) :
    ellipticWeightC1 b c chi K p ≤ edgeDistance b p ^ 6 := by
  by_cases hp : p 1 ≤ b
  · rw [ellipticWeightC1_eq hp]
    exact ellipticWeight_le_distance_six _ _ _ _ _ hchi
  · rw [ellipticWeightC1_zero (lt_of_not_ge hp).le]
    positivity

theorem ellipticWeightC1_partial_eq {b c : ℝ} {chi K : Coord → ℝ} {p : Coord}
    (hp : p 1 < b) (i : Fin 2) :
    coordPartial i (ellipticWeightC1 b c chi K) p =
      coordPartial i (ellipticWeight b c chi K) p := by
  have he : ellipticWeightC1 b c chi K =ᶠ[𝓝 p] ellipticWeight b c chi K := by
    filter_upwards [(isOpen_lt (continuous_apply 1) continuous_const).mem_nhds hp] with q hq
    exact ellipticWeightC1_eq hq.le
  unfold coordPartial
  rw [he.fderiv_eq]

theorem ellipticWeightC1_contDiffOn {b c : ℝ} {chi K : Coord → ℝ} {U : Set Coord}
    (hc : 0 < c) (hchi : ContDiffOn ℝ 1 chi U) (hK : ContDiffOn ℝ 1 K U) :
    ContDiffOn ℝ 1 (ellipticWeightC1 b c chi K) U := by
  have hmap : ContDiffOn ℝ 1 (fun p : Coord => ![K p, p 1 - b]) U := by
    apply contDiffOn_pi.mpr
    intro i
    fin_cases i
    · simpa using hK
    · simpa using (contDiffOn_apply ℝ ℝ 1 U).sub contDiffOn_const
  exact (hchi.pow 2).mul ((ellipticEdgeKernel_contDiff_one hc).comp_contDiffOn hmap)

end SmoothLocal.Weighted

end

end OAI
