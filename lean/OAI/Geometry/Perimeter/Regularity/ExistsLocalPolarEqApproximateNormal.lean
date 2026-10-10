import OAI.Geometry.Perimeter.Regularity.TsupportBlowdownSubsetBall

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPISingularHarnack

theorem exists_local_polar_eq_approximateNormal {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (U : Set (Euc n)) (hU : IsOpen U) (hP : perimeter E U ≠ ⊤) :
    ∃ G : Euc n → Euc n,
      StronglyMeasurable G ∧ MemLp G 2 ((perimeterMeasure E).restrict U) ∧
      (∀ᵐ x ∂(perimeterMeasure E).restrict U, HasHalfspaceBlowup E x (G x)) ∧
      (∀ᵐ x ∂(perimeterMeasure E).restrict U, approximateNormal E x = G x) ∧
      ∀ V : Euc n → Euc n, ContDiff ℝ ∞ V → HasCompactSupport V → tsupport V ⊆ U →
        (∫ x in E, divergence V x) = ∫ x in U, inner ℝ (G x) (V x) ∂perimeterMeasure E := by
  let μ := (perimeterMeasure E).restrict U
  let : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open E hU]; exact hP.lt_top⟩
  obtain ⟨G, hG, hGp, hGn, hdiff, hrep⟩ :=
    exists_differentiating_unit_polar (lt_trans (by norm_num) hn) hmin U hU hP
  have hsupp : ∀ᵐ x ∂μ, x ∈ perimeterSupport E := by
    have hs : ∀ᵐ x ∂perimeterMeasure E, x ∈ perimeterSupport E := by
      rw [← perimeterMeasure_support E]
      exact (perimeterMeasure E).support_mem_ae
    exact ae_restrict_of_ae hs
  have hUae : ∀ᵐ x ∂μ, x ∈ U := ae_restrict_mem hU.measurableSet
  have hblow : ∀ᵐ x ∂μ, HasHalfspaceBlowup E x (G x) := by
    filter_upwards [hGn, hdiff, hsupp, hUae] with x hx hdx hsx hux
    exact hasHalfspaceBlowup_of_differentiating_polar hn hmin hU μ
      (MemLp.integrable (by norm_num) hGp) hrep x (G x) hux hsx hx hdx
  exact ⟨G, hG, hGp, hblow,
    hblow.mono (fun x hx ↦ approximateNormal_eq_of_blowup hmin.1 hx), hrep⟩

theorem minimizing_gaussGreen_local {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (U : Set (Euc n)) (hU : IsOpen U) (hP : perimeter E U ≠ ⊤)
    (V : Euc n → Euc n) (hV : ContDiff ℝ ∞ V) (hVc : HasCompactSupport V)
    (hVU : tsupport V ⊆ U) :
    (∫ x in E, divergence V x) =
      ∫ x in U, inner ℝ (approximateNormal E x) (V x) ∂perimeterMeasure E := by
  obtain ⟨G, _, _, _, heq, hrep⟩ := exists_local_polar_eq_approximateNormal hn hmin U hU hP
  rw [hrep V hV hVc hVU]
  apply integral_congr_ae
  exact heq.mono fun x hx ↦ by
    change inner ℝ (G x) (V x) = inner ℝ (approximateNormal E x) (V x)
    rw [hx]

theorem minimizing_halfspaceBlowup_ae {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E) :
    ∀ᵐ x ∂perimeterMeasure E, HasHalfspaceBlowup E x (approximateNormal E x) := by
  let U : ℕ → Set (Euc n) := fun j ↦ Metric.ball 0 (j + 1 : ℝ)
  have hcover : (⋃ j, U j) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨j, hj⟩ := exists_nat_gt ‖x‖
    exact mem_iUnion.mpr ⟨j, by simpa [U, Metric.mem_ball, dist_zero_right] using
      (show ‖x‖ < (j : ℝ) + 1 by linarith)⟩
  have hall : ∀ j, ∀ᵐ x ∂(perimeterMeasure E).restrict (U j),
      HasHalfspaceBlowup E x (approximateNormal E x) := by
    intro j
    obtain ⟨G, _, _, hG, heq, _⟩ := exists_local_polar_eq_approximateNormal hn hmin
      (U j) Metric.isOpen_ball (ne_of_lt (hmin.2.1 0 (j + 1) (by positivity)))
    filter_upwards [hG, heq] with x hx he
    rwa [he]
  have hh := (ae_restrict_iUnion_iff U
    (fun x ↦ HasHalfspaceBlowup E x (approximateNormal E x))).mpr hall
  simpa only [hcover, Measure.restrict_univ] using hh

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPI
section BoundedCoefficientLimits
variable {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]
  [NormedSpace ℝ V] {μ : Measure X}

theorem vectorEnergy_bounded_coefficient_tendsto {G : X → V} (hG : MemLp G 2 μ)
    (a : ℕ → X → ℝ) (hm : ∀ j, AEStronglyMeasurable (a j) μ)
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ j, ∀ᵐ x ∂μ, ‖a j x‖ ≤ M)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun j ↦ a j x) atTop (𝓝 0)) :
    Tendsto (fun j ↦ vectorEnergy μ (fun x ↦ a j x • G x)) atTop (𝓝 0) := by
  have hfin : (∫⁻ x, ENNReal.ofReal (M ^ 2) * ENNReal.ofReal (‖G x‖ ^ 2) ∂μ) ≠ ⊤ := by
    rw [lintegral_const_mul' (ENNReal.ofReal (M ^ 2)) (fun x ↦ ENNReal.ofReal (‖G x‖ ^ 2)) ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ((memLp_two_iff_vectorEnergy hG.aestronglyMeasurable).mp hG).ne
  have hlim := tendsto_lintegral_of_dominated_convergence'
    (fun x ↦ ENNReal.ofReal (M ^ 2) * ENNReal.ofReal (‖G x‖ ^ 2))
    (f := fun _ ↦ (0 : ℝ≥0∞))
    (F := fun j x ↦ ENNReal.ofReal (‖a j x • G x‖ ^ 2))
    (fun j ↦ (((hm j).smul hG.aestronglyMeasurable).norm.pow 2).aemeasurable.ennreal_ofReal) ?_ hfin ?_
  · simpa only [vectorEnergy, lintegral_zero] using hlim
  · intro j
    filter_upwards [hb j] with x hx
    rw [← ENNReal.ofReal_mul (sq_nonneg M)]
    apply ENNReal.ofReal_le_ofReal
    rw [norm_smul, mul_pow]
    exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) hM).mpr hx) (sq_nonneg _)
  · filter_upwards [ht] with x hx
    have hv : Tendsto (fun j ↦ a j x • G x) atTop (𝓝 (0 : V)) := by
      simpa only [zero_smul] using hx.smul_const (G x)
    simpa only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (hv.norm.pow 2)

theorem vectorEnergy_varying_bounded_smul_zero {F : ℕ → X → V}
    (a : ℕ → X → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (ha : ∀ j, ∀ᵐ x ∂μ, ‖a j x‖ ≤ M)
    (hF : Tendsto (fun j ↦ vectorEnergy μ (F j)) atTop (𝓝 0)) :
    Tendsto (fun j ↦ vectorEnergy μ (fun x ↦ a j x • F j x)) atTop (𝓝 0) := by
  have hh : Tendsto (fun j ↦ ENNReal.ofReal (M ^ 2) * vectorEnergy μ (F j))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hF (Or.inr ENNReal.ofReal_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hh
    (fun _ ↦ bot_le) (fun j ↦ vectorEnergy_bounded_smul hM (ha j))

theorem vectorEnergy_composed_gradient_tendsto
    {u : ℕ → X → ℝ} {h : X → ℝ} {F : ℕ → X → V} {G : X → V}
    (hu : ∀ j, AEStronglyMeasurable (u j) μ) (hh : AEStronglyMeasurable h μ)
    (hF : ∀ j, MemLp (F j) 2 μ) (hG : MemLp G 2 μ)
    (hFG : Tendsto (fun j ↦ vectorEnergy μ (fun x ↦ F j x - G x)) atTop (𝓝 0))
    (huh : ∀ᵐ x ∂μ, Tendsto (fun j ↦ u j x) atTop (𝓝 (h x)))
    (b : ℝ → ℝ) (hb : Continuous b) {M : ℝ} (hM : 0 ≤ M)
    (hbM : ∀ t, ‖b t‖ ≤ M) :
    Tendsto (fun j ↦ vectorEnergy μ
      (fun x ↦ b (u j x) • F j x - b (h x) • G x)) atTop (𝓝 0) := by
  let A : ℕ → X → V := fun j x ↦ b (u j x) • (F j x - G x)
  let B : ℕ → X → V := fun j x ↦ (b (u j x) - b (h x)) • G x
  have hAm : ∀ j, AEStronglyMeasurable (A j) μ := fun j ↦
    (hb.comp_aestronglyMeasurable (hu j)).smul
      ((hF j).aestronglyMeasurable.sub hG.aestronglyMeasurable)
  have hBm : ∀ j, AEStronglyMeasurable (B j) μ := fun j ↦
    ((hb.comp_aestronglyMeasurable (hu j)).sub
      (hb.comp_aestronglyMeasurable hh)).smul hG.aestronglyMeasurable
  have hA0 : Tendsto (fun j ↦ vectorEnergy μ (A j)) atTop (𝓝 0) :=
    vectorEnergy_varying_bounded_smul_zero (fun j x ↦ b (u j x)) hM
      (fun j ↦ ae_of_all _ fun x ↦ hbM _) hFG
  have hB0 : Tendsto (fun j ↦ vectorEnergy μ (B j)) atTop (𝓝 0) := by
    apply vectorEnergy_bounded_coefficient_tendsto hG
      (fun j x ↦ b (u j x) - b (h x))
      (fun j ↦ (hb.comp_aestronglyMeasurable (hu j)).sub (hb.comp_aestronglyMeasurable hh))
      (M := 2 * M) (by positivity)
    · intro j
      exact ae_of_all _ fun x ↦ (norm_sub_le _ _).trans (by linarith [hbM (u j x), hbM (h x)])
    · filter_upwards [huh] with x hx
      simpa only [sub_self, Function.comp_def] using (hb.continuousAt.tendsto.comp hx).sub_const (b (h x))
  have hbound : ∀ j, vectorEnergy μ (fun x ↦ b (u j x) • F j x - b (h x) • G x) ≤
      2 * vectorEnergy μ (A j) + 2 * vectorEnergy μ (B j) := by
    intro j
    have heq : (fun x ↦ b (u j x) • F j x - b (h x) • G x) =
        fun x ↦ A j x + B j x := by funext x; dsimp [A, B]; module
    rw [heq]
    exact vectorEnergy_add_le (hAm j) (hBm j)
  have hlim : Tendsto (fun j ↦ 2 * vectorEnergy μ (A j) + 2 * vectorEnergy μ (B j))
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (ENNReal.Tendsto.const_mul hA0 (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))).add
        (ENNReal.Tendsto.const_mul hB0 (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ bot_le) hbound

end BoundedCoefficientLimits
end RPI

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPI
section NonlinearTests
variable {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]
  [NormedSpace ℝ V] {μ : Measure X}

theorem vectorEnergy_smul_bounded_field_le {a : X → ℝ} {D : X → V} {M : ℝ}
    (hM : 0 ≤ M) (hD : ∀ᵐ x ∂μ, ‖D x‖ ≤ M) :
    vectorEnergy μ (fun x ↦ a x • D x) ≤ ENNReal.ofReal (M ^ 2) * vectorEnergy μ a := by
  unfold vectorEnergy
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  · apply lintegral_mono_ae
    filter_upwards [hD] with x hx
    rw [← ENNReal.ofReal_mul (sq_nonneg M)]
    apply ENNReal.ofReal_le_ofReal
    rw [norm_smul, mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) hM).mpr hx) (sq_nonneg ‖a x‖)]

theorem vectorEnergy_lipschitz_comp_zero {u : ℕ → X → ℝ} {h : X → ℝ}
    {ψ : ℝ → ℝ} {K : ℝ≥0} (hψ : LipschitzWith K ψ)
    (hu : Tendsto (fun j ↦ vectorEnergy μ (fun x ↦ u j x - h x)) atTop (𝓝 0)) :
    Tendsto (fun j ↦ vectorEnergy μ (fun x ↦ ψ (u j x) - ψ (h x))) atTop (𝓝 0) := by
  have hb : ∀ j, vectorEnergy μ (fun x ↦ ψ (u j x) - ψ (h x)) ≤
      ENNReal.ofReal ((K : ℝ) ^ 2) * vectorEnergy μ (fun x ↦ u j x - h x) := by
    intro j
    unfold vectorEnergy
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    · apply lintegral_mono
      intro x
      dsimp only
      rw [← ENNReal.ofReal_mul (sq_nonneg (K : ℝ))]
      apply ENNReal.ofReal_le_ofReal
      have hh := hψ.norm_sub_le (u j x) (h x)
      simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hh
  have hlim : Tendsto (fun j ↦ ENNReal.ofReal ((K : ℝ) ^ 2) *
      vectorEnergy μ (fun x ↦ u j x - h x)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hu (Or.inr ENNReal.ofReal_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ bot_le) hb

theorem vectorEnergy_nonlinear_test_tendsto
    {u : ℕ → X → ℝ} {h η : X → ℝ} {F : ℕ → X → V} {G D : X → V}
    (hu : ∀ j, AEStronglyMeasurable (u j) μ) (hh : AEStronglyMeasurable h μ)
    (hη : AEStronglyMeasurable η μ) (hD : AEStronglyMeasurable D μ)
    (hF : ∀ j, MemLp (F j) 2 μ) (hG : MemLp G 2 μ)
    {M N : ℝ} (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hηM : ∀ᵐ x ∂μ, ‖η x‖ ≤ M) (hDN : ∀ᵐ x ∂μ, ‖D x‖ ≤ N)
    (huh : Tendsto (fun j ↦ vectorEnergy μ (fun x ↦ u j x - h x)) atTop (𝓝 0))
    (hFG : Tendsto (fun j ↦ vectorEnergy μ (fun x ↦ F j x - G x)) atTop (𝓝 0))
    (hpoint : ∀ᵐ x ∂μ, Tendsto (fun j ↦ u j x) atTop (𝓝 (h x)))
    {ψ : ℝ → ℝ} {K : ℝ≥0} (hψ : LipschitzWith K ψ)
    (b : ℝ → ℝ) (hb : Continuous b) {L : ℝ} (hL : 0 ≤ L) (hbL : ∀ t, ‖b t‖ ≤ L) :
    Tendsto (fun j ↦ vectorEnergy μ (fun x ↦
      ((2 * η x * ψ (u j x)) • D x + (η x ^ 2 * b (u j x)) • F j x) -
      ((2 * η x * ψ (h x)) • D x + (η x ^ 2 * b (h x)) • G x))) atTop (𝓝 0) := by
  let A : ℕ → X → V := fun j x ↦ (2 * η x) • ((ψ (u j x) - ψ (h x)) • D x)
  let B : ℕ → X → V := fun j x ↦ η x ^ 2 • (b (u j x) • F j x - b (h x) • G x)
  have hψm := hψ.continuous
  have hAm : ∀ j, AEStronglyMeasurable (A j) μ := fun j ↦
    (aestronglyMeasurable_const.mul hη).smul
      (((hψm.comp_aestronglyMeasurable (hu j)).sub
        (hψm.comp_aestronglyMeasurable hh)).smul hD)
  have hBm : ∀ j, AEStronglyMeasurable (B j) μ := fun j ↦
    (hη.pow 2).smul
      (((hb.comp_aestronglyMeasurable (hu j)).smul (hF j).aestronglyMeasurable).sub
        ((hb.comp_aestronglyMeasurable hh).smul hG.aestronglyMeasurable))
  have hc : Tendsto (fun j ↦ vectorEnergy μ (fun x ↦ (ψ (u j x) - ψ (h x)) • D x))
      atTop (𝓝 0) := by
    have hh0 := vectorEnergy_lipschitz_comp_zero hψ huh
    have hlim : Tendsto (fun j ↦ ENNReal.ofReal (N ^ 2) *
        vectorEnergy μ (fun x ↦ ψ (u j x) - ψ (h x))) atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul hh0 (Or.inr ENNReal.ofReal_ne_top)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ ↦ bot_le) (fun _ ↦ vectorEnergy_smul_bounded_field_le hN hDN)
  have hA0 : Tendsto (fun j ↦ vectorEnergy μ (A j)) atTop (𝓝 0) := by
    apply vectorEnergy_varying_bounded_smul_zero (fun _ x ↦ 2 * η x) (M := 2 * M) (by positivity) _ hc
    intro j
    filter_upwards [hηM] with x hx
    simpa only [norm_mul, Real.norm_ofNat] using mul_le_mul_of_nonneg_left hx (by norm_num : (0 : ℝ) ≤ 2)
  have hB0 : Tendsto (fun j ↦ vectorEnergy μ (B j)) atTop (𝓝 0) := by
    apply vectorEnergy_varying_bounded_smul_zero (fun _ x ↦ η x ^ 2) (M := M ^ 2) (sq_nonneg M) _
      (vectorEnergy_composed_gradient_tendsto hu hh hF hG hFG hpoint b hb hL hbL)
    intro j
    filter_upwards [hηM] with x hx
    simpa only [norm_pow] using (sq_le_sq₀ (norm_nonneg _) hM).mpr hx
  have hlim : Tendsto (fun j ↦ 2 * vectorEnergy μ (A j) + 2 * vectorEnergy μ (B j))
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (ENNReal.Tendsto.const_mul hA0 (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))).add
        (ENNReal.Tendsto.const_mul hB0 (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ ↦ bot_le)
  intro j
  have heq : (fun x ↦
      ((2 * η x * ψ (u j x)) • D x + (η x ^ 2 * b (u j x)) • F j x) -
      ((2 * η x * ψ (h x)) • D x + (η x ^ 2 * b (h x)) • G x)) =
      fun x ↦ A j x + B j x := by funext x; dsimp [A, B]; module
  dsimp only
  rw [heq]
  exact vectorEnergy_add_le (hAm j) (hBm j)

end NonlinearTests
end RPI

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
namespace RPISingularHarnack

def logTest (ε t : ℝ) : ℝ := (Real.sqrt (t ^ 2 + ε ^ 2) - t) / ε ^ 2

def logSlope (ε t : ℝ) : ℝ := (t / Real.sqrt (t ^ 2 + ε ^ 2) - 1) / ε ^ 2

lemma logTest_root_pos {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    0 < Real.sqrt (t ^ 2 + ε ^ 2) := Real.sqrt_pos.2 (by positivity)

lemma logTest_root_sq {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Real.sqrt (t ^ 2 + ε ^ 2) ^ 2 = t ^ 2 + ε ^ 2 :=
  Real.sq_sqrt (by positivity)

lemma logTest_abs_lt_root {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    |t| < Real.sqrt (t ^ 2 + ε ^ 2) := by
  have hs := logTest_root_sq hε t
  have hr := logTest_root_pos hε t
  nlinarith [sq_abs t, sq_pos_of_pos hε]

theorem logTest_contDiff {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (logTest ε) := by
  unfold logTest
  exact ((((contDiff_id.pow 2).add contDiff_const).sqrt
    (fun t ↦ ne_of_gt (by positivity : 0 < t ^ 2 + ε ^ 2))).sub contDiff_id).div_const _

theorem logTest_hasDerivAt {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (logTest ε) (logSlope ε t) t := by
  have hh := (((hasDerivAt_id t).pow 2).add_const (ε ^ 2)).sqrt
    (ne_of_gt (by positivity : 0 < t ^ 2 + ε ^ 2))
  have h := (hh.sub (hasDerivAt_id t)).div_const (ε ^ 2)
  apply h.congr_deriv
  dsimp [logSlope]
  ring

theorem logSlope_continuous {ε : ℝ} (hε : 0 < ε) : Continuous (logSlope ε) := by
  unfold logSlope
  exact ((continuous_id.div (Real.continuous_sqrt.comp
    ((continuous_id.pow 2).add continuous_const))
    (fun t ↦ (logTest_root_pos hε t).ne')).sub continuous_const).div_const _

theorem logTest_pos {ε : ℝ} (hε : 0 < ε) (t : ℝ) : 0 < logTest ε t := by
  unfold logTest
  exact div_pos (sub_pos.mpr ((le_abs_self t).trans_lt (logTest_abs_lt_root hε t)))
    (sq_pos_of_pos hε)

theorem logTest_reciprocal {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    logTest ε t = 1 / (Real.sqrt (t ^ 2 + ε ^ 2) + t) := by
  have hr : 0 < Real.sqrt (t ^ 2 + ε ^ 2) + t := by
    have hh := (neg_le_abs t).trans_lt (logTest_abs_lt_root hε t)
    linarith
  unfold logTest
  apply (div_eq_div_iff (pow_ne_zero _ hε.ne') hr.ne').2
  nlinarith [logTest_root_sq hε t]

theorem logSlope_eq {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    logSlope ε t = -logTest ε t / Real.sqrt (t ^ 2 + ε ^ 2) := by
  unfold logSlope logTest
  field_simp [(logTest_root_pos hε t).ne', hε.ne']
  ring

theorem logSlope_neg {ε : ℝ} (hε : 0 < ε) (t : ℝ) : logSlope ε t < 0 := by
  rw [logSlope_eq hε]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (logTest_pos hε t)) (logTest_root_pos hε t)

theorem logSlope_bound {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ‖logSlope ε t‖ ≤ 2 / ε ^ 2 := by
  have hr := logTest_root_pos hε t
  have ht : |t / Real.sqrt (t ^ 2 + ε ^ 2)| ≤ 1 := by
    rw [abs_div, abs_of_pos hr]
    exact (div_le_one hr).2 (logTest_abs_lt_root hε t).le
  unfold logSlope
  rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (sq_pos_of_pos hε)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg ε)
  exact (abs_sub (t / Real.sqrt (t ^ 2 + ε ^ 2)) 1).trans (by
    simpa only [abs_one, add_comm, one_add_one_eq_two] using add_le_add_right ht 1)

theorem logTest_sq_le_neg_slope {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    logTest ε t ^ 2 ≤ -logSlope ε t := by
  have hr := logTest_root_pos hε t
  have hp := logTest_pos hε t
  rw [logSlope_eq hε, neg_div, neg_neg]
  have hmul : logTest ε t * Real.sqrt (t ^ 2 + ε ^ 2) ≤ 1 := by
    rw [logTest_reciprocal hε, one_div, inv_mul_eq_div]
    exact (div_le_one (by linarith : 0 < Real.sqrt (t ^ 2 + ε ^ 2) + t)).2 (by linarith)
  apply (le_div_iff₀ hr).2
  nlinarith [mul_le_mul_of_nonneg_left hmul hp.le]

theorem logSlope_controls_log_weight {ε t : ℝ} (hε : 0 < ε) (ht : 0 ≤ t) :
    1 / (t + ε) ^ 2 ≤ 2 * (-logSlope ε t) := by
  have hr := logTest_root_pos hε t
  have hte : 0 < t + ε := by positivity
  have hroot : Real.sqrt (t ^ 2 + ε ^ 2) ≤ t + ε := by
    nlinarith [logTest_root_sq hε t, mul_nonneg ht hε.le]
  have hplus : 0 < Real.sqrt (t ^ 2 + ε ^ 2) + t := by positivity
  rw [logSlope_eq hε, neg_div, neg_neg, logTest_reciprocal hε]
  apply (div_le_iff₀ (sq_pos_of_pos hte)).2
  field_simp [hr.ne', hplus.ne']
  nlinarith [mul_le_mul hroot (show Real.sqrt (t ^ 2 + ε ^ 2) + t ≤ 2 * (t + ε) by linarith)
    hplus.le hte.le]

end RPISingularHarnack

end

end OAI
