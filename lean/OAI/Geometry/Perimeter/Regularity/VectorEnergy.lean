import OAI.Geometry.Perimeter.Regularity.Space

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
namespace RPI
section Energy
variable {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]
variable {μ : Measure X}

noncomputable def vectorEnergy (μ : Measure X) (F : X → V) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (‖F x‖ ^ 2) ∂μ

theorem memLp_two_iff_vectorEnergy {F : X → V} (hF : AEStronglyMeasurable F μ) :
    MemLp F 2 μ ↔ vectorEnergy μ F < ⊤ := by
  rw [memLp_two_iff_integrable_sq_norm hF]
  have hm : AEStronglyMeasurable (fun x ↦ ‖F x‖ ^ 2) μ := hF.norm.pow 2
  change (AEStronglyMeasurable (fun x ↦ ‖F x‖ ^ 2) μ ∧ HasFiniteIntegral (fun x ↦ ‖F x‖ ^ 2) μ) ↔ _
  rw [and_iff_right hm, hasFiniteIntegral_iff_ofReal (ae_of_all μ (fun x ↦ sq_nonneg _))]
  rfl

theorem eLpNorm_two_eq_vectorEnergy_rpow (F : X → V) :
    eLpNorm' F 2 μ = vectorEnergy μ F ^ (1 / 2 : ℝ) := by
  rw [eLpNorm'_eq_lintegral_enorm]
  congr 1
  apply lintegral_congr
  intro x
  rw [ENNReal.rpow_two, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem eLpNorm_two_eq_vectorEnergy_rpow_of_aestronglyMeasurable {F : X → V}
    (hF : AEStronglyMeasurable F μ) :
    eLpNorm F 2 μ = vectorEnergy μ F ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_eLpNorm' (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hF, ENNReal.toReal_ofNat,
    eLpNorm_two_eq_vectorEnergy_rpow]

theorem vectorEnergy_le_of_ae_tendsto {F : ℕ → X → V} {G : X → V}
    (hF : ∀ i, AEStronglyMeasurable (F i) μ)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ F i x) atTop (𝓝 (G x)))
    {b : ℕ → ℝ≥0∞} {B : ℝ≥0∞}
    (hb : ∀ᶠ i in atTop, vectorEnergy μ (F i) ≤ b i)
    (hbB : Tendsto b atTop (𝓝 B)) : vectorEnergy μ G ≤ B := by
  have ht : ∀ᵐ x ∂μ, Tendsto (fun i ↦ ENNReal.ofReal (‖F i x‖ ^ 2))
      atTop (𝓝 (ENNReal.ofReal (‖G x‖ ^ 2))) := by
    filter_upwards [hlim] with x hx
    exact ENNReal.tendsto_ofReal (hx.norm.pow 2)
  calc
    vectorEnergy μ G = ∫⁻ x, liminf (fun i ↦ ENNReal.ofReal (‖F i x‖ ^ 2)) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ht] with x hx using hx.liminf_eq.symm
    _ ≤ liminf (fun i ↦ vectorEnergy μ (F i)) atTop :=
      lintegral_liminf_le' (fun i ↦ ((hF i).norm.pow 2).aemeasurable.ennreal_ofReal)
    _ ≤ liminf b atTop := liminf_le_liminf hb
    _ = B := hbB.liminf_eq

theorem tendsto_eLpNorm_two_of_vectorEnergy_zero {F : ℕ → X → V}
    (hF : Tendsto (fun i ↦ vectorEnergy μ (F i)) atTop (𝓝 0)) :
    Tendsto (fun i ↦ eLpNorm' (F i) 2 μ) atTop (𝓝 0) := by
  simp_rw [eLpNorm_two_eq_vectorEnergy_rpow]
  simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using
    (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).continuousAt.tendsto.comp hF

theorem tendsto_eLpNorm_two_toReal_of_vectorEnergy_zero {F : ℕ → X → V}
    (hF : Tendsto (fun i ↦ vectorEnergy μ (F i)) atTop (𝓝 0)) :
    Tendsto (fun i ↦ (eLpNorm' (F i) 2 μ).toReal) atTop (𝓝 0) := by
  simpa only [Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp
      (tendsto_eLpNorm_two_of_vectorEnergy_zero hF)

theorem tendsto_eLpNorm_two_of_vectorEnergy_zero_of_aestronglyMeasurable {F : ℕ → X → V}
    (hFm : ∀ i, AEStronglyMeasurable (F i) μ)
    (hF : Tendsto (fun i ↦ vectorEnergy μ (F i)) atTop (𝓝 0)) :
    Tendsto (fun i ↦ eLpNorm (F i) 2 μ) atTop (𝓝 0) := by
  simp_rw [eLpNorm_two_eq_vectorEnergy_rpow_of_aestronglyMeasurable (hFm _)]
  simpa only [eLpNorm_two_eq_vectorEnergy_rpow] using
    (tendsto_eLpNorm_two_of_vectorEnergy_zero hF)

theorem tendsto_eLpNorm_two_toReal_of_vectorEnergy_zero_of_aestronglyMeasurable
    {F : ℕ → X → V} (hFm : ∀ i, AEStronglyMeasurable (F i) μ)
    (hF : Tendsto (fun i ↦ vectorEnergy μ (F i)) atTop (𝓝 0)) :
    Tendsto (fun i ↦ (eLpNorm (F i) 2 μ).toReal) atTop (𝓝 0) := by
  simpa only [Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp
      (tendsto_eLpNorm_two_of_vectorEnergy_zero_of_aestronglyMeasurable hFm hF)

end Energy

section SobolevLimits
variable {X V : Type*} [MeasurableSpace X]
  [NormedAddCommGroup V] [NormedSpace ℝ V] {μ : Measure X}

theorem vectorEnergy_bounded_smul {a : X → ℝ} {F : X → V} {M : ℝ}
    (hM : 0 ≤ M) (ha : ∀ᵐ x ∂μ, ‖a x‖ ≤ M) :
    vectorEnergy μ (fun x ↦ a x • F x) ≤ ENNReal.ofReal (M ^ 2) * vectorEnergy μ F := by
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (M ^ 2) * ENNReal.ofReal (‖F x‖ ^ 2) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ha] with x hx
      rw [← ENNReal.ofReal_mul (sq_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      rw [norm_smul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ (norm_nonneg _) hM).mpr hx) (sq_nonneg _)
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

omit [NormedSpace ℝ V] in
theorem vectorEnergy_add_le {F G : X → V}
    (hF : AEStronglyMeasurable F μ) (hG : AEStronglyMeasurable G μ) :
    vectorEnergy μ (fun x ↦ F x + G x) ≤
      2 * vectorEnergy μ F + 2 * vectorEnergy μ G := by
  have hFm : AEMeasurable (fun x ↦ (2 : ℝ≥0∞) * ENNReal.ofReal (‖F x‖ ^ 2)) μ :=
    aemeasurable_const.mul (hF.norm.pow 2 |>.aemeasurable.ennreal_ofReal)
  have hGm : AEMeasurable (fun x ↦ (2 : ℝ≥0∞) * ENNReal.ofReal (‖G x‖ ^ 2)) μ :=
    aemeasurable_const.mul (hG.norm.pow 2 |>.aemeasurable.ennreal_ofReal)
  calc
    _ ≤ ∫⁻ x, 2 * ENNReal.ofReal (‖F x‖ ^ 2) + 2 * ENNReal.ofReal (‖G x‖ ^ 2) ∂μ := by
      apply lintegral_mono
      intro x
      have hb : ‖F x + G x‖ ^ 2 ≤ 2 * ‖F x‖ ^ 2 + 2 * ‖G x‖ ^ 2 := by
        have hsq := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
          (norm_add_le (F x) (G x))
        nlinarith [sq_nonneg (‖F x‖ - ‖G x‖)]
      calc
        _ ≤ ENNReal.ofReal (2 * ‖F x‖ ^ 2 + 2 * ‖G x‖ ^ 2) := ENNReal.ofReal_le_ofReal hb
        _ = _ := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
    _ = _ := by
      rw [lintegral_congr_ae (hFm.ae_eq_mk.fun_add hGm.ae_eq_mk),
        lintegral_add_aux hFm.measurable_mk hGm.measurable_mk,
        ← lintegral_congr_ae hFm.ae_eq_mk, ← lintegral_congr_ae hGm.ae_eq_mk,
        lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
        lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
      rfl

theorem vectorEnergy_omitted_tendsto_zero {G : X → V} (hG : MemLp G 2 μ)
    (χ : ℕ → X → ℝ) (hχ : ∀ i, AEStronglyMeasurable (χ i) μ)
    (hχb : ∀ i, ∀ᵐ x ∂μ, χ i x ∈ Icc (0 : ℝ) 1)
    (hχlim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ χ i x) atTop (𝓝 1)) :
    Tendsto (fun i ↦ vectorEnergy μ (fun x ↦ (χ i x - 1) • G x)) atTop (𝓝 0) := by
  have hfin : vectorEnergy μ G ≠ ⊤ :=
    (memLp_two_iff_vectorEnergy hG.aestronglyMeasurable).mp hG |>.ne
  have hlim := tendsto_lintegral_of_dominated_convergence'
    (fun x ↦ ENNReal.ofReal (‖G x‖ ^ 2))
    (f := fun _ ↦ (0 : ℝ≥0∞))
    (F := fun i x ↦ ENNReal.ofReal (‖(χ i x - 1) • G x‖ ^ 2))
    (fun i ↦ (((hχ i).sub aestronglyMeasurable_const).smul hG.aestronglyMeasurable).norm.pow 2
      |>.aemeasurable.ennreal_ofReal) ?_ hfin ?_
  · simpa only [vectorEnergy, lintegral_zero] using hlim
  · intro i
    filter_upwards [hχb i] with x hx
    apply ENNReal.ofReal_le_ofReal
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith [hx.2])]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [hx.1])
  · filter_upwards [hχlim] with x hx
    have hv : Tendsto (fun i ↦ (χ i x - 1) • G x) atTop (𝓝 (0 : V)) := by
      simpa only [sub_self, zero_smul] using (hx.sub_const 1).smul_const (G x)
    simpa only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (hv.norm.pow 2)

theorem vectorEnergy_bounded_smul_tendsto_zero {h : X → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hh : ∀ᵐ x ∂μ, ‖h x‖ ≤ M)
    (C : ℕ → X → V)
    (hC : Tendsto (fun i ↦ vectorEnergy μ (C i)) atTop (𝓝 0)) :
    Tendsto (fun i ↦ vectorEnergy μ (fun x ↦ h x • C i x)) atTop (𝓝 0) := by
  have ha : Tendsto (fun i ↦ ENNReal.ofReal (M ^ 2) * vectorEnergy μ (C i)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hC (Or.inr ENNReal.ofReal_ne_top)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ha
    (fun _ ↦ zero_le) (fun _ ↦ vectorEnergy_bounded_smul hM hh)

theorem memLp_of_capacity_energy_bounds {G : X → V}
    (χ : ℕ → X → ℝ)
    (hF : ∀ i, MemLp (fun x ↦ χ i x • G x) 2 μ)
    (hχlim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ χ i x) atTop (𝓝 1))
    {a : ℕ → ℝ≥0∞} (ha : Tendsto a atTop (𝓝 0))
    {A B : ℝ≥0∞} (hA : A ≠ ⊤) (hB : B < ⊤)
    (hbound : ∀ᶠ i in atTop, vectorEnergy μ (fun x ↦ χ i x • G x) ≤ B + A * a i) :
    MemLp G 2 μ ∧ vectorEnergy μ G ≤ B := by
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ χ i x • G x) atTop (𝓝 (G x)) := by
    filter_upwards [hχlim] with x hx
    simpa only [one_smul] using hx.smul_const (G x)
  have hG : AEStronglyMeasurable G μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun i ↦ (hF i).aestronglyMeasurable) hlim
  have hbB : Tendsto (fun i ↦ B + A * a i) atTop (𝓝 B) := by
    simpa only [mul_zero, add_zero] using
      tendsto_const_nhds.add (ENNReal.Tendsto.const_mul ha (Or.inr hA))
  have hE := vectorEnergy_le_of_ae_tendsto (fun i ↦ (hF i).aestronglyMeasurable) hlim hbound hbB
  exact ⟨(memLp_two_iff_vectorEnergy hG).mpr (hE.trans_lt hB), hE⟩

theorem capacity_productGradient_tendsto {G : X → V} (hG : MemLp G 2 μ)
    (χ : ℕ → X → ℝ) (hχ : ∀ i, AEStronglyMeasurable (χ i) μ)
    (hχb : ∀ i, ∀ᵐ x ∂μ, χ i x ∈ Icc (0 : ℝ) 1)
    (hχlim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ χ i x) atTop (𝓝 1))
    {h : X → ℝ} (hh : AEStronglyMeasurable h μ) {M : ℝ} (hM : 0 ≤ M)
    (hhb : ∀ᵐ x ∂μ, ‖h x‖ ≤ M)
    (C : ℕ → X → V) (hC : ∀ i, MemLp (C i) 2 μ)
    (hC0 : Tendsto (fun i ↦ vectorEnergy μ (C i)) atTop (𝓝 0)) :
    Tendsto (fun i ↦ vectorEnergy μ (fun x ↦ χ i x • G x + h x • C i x - G x))
      atTop (𝓝 0) := by
  have ho := vectorEnergy_omitted_tendsto_zero hG χ hχ hχb hχlim
  have he := vectorEnergy_bounded_smul_tendsto_zero hM hhb C hC0
  have htwo : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hsum : Tendsto (fun i ↦
      2 * vectorEnergy μ (fun x ↦ (χ i x - 1) • G x) +
      2 * vectorEnergy μ (fun x ↦ h x • C i x)) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (ENNReal.Tendsto.const_mul ho (Or.inr htwo)).add
        (ENNReal.Tendsto.const_mul he (Or.inr htwo))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ ↦ zero_le)
  intro i
  have h₁ : AEStronglyMeasurable (fun x ↦ (χ i x - 1) • G x) μ :=
    ((hχ i).sub aestronglyMeasurable_const).smul hG.aestronglyMeasurable
  have h₂ : AEStronglyMeasurable (fun x ↦ h x • C i x) μ :=
    hh.smul (hC i).aestronglyMeasurable
  have hid : (fun x ↦ χ i x • G x + h x • C i x - G x) =
      (fun x ↦ (χ i x - 1) • G x + h x • C i x) := by
    funext x
    simp only [sub_smul, one_smul]
    abel
  change vectorEnergy μ (fun x ↦ χ i x • G x + h x • C i x - G x) ≤
    2 * vectorEnergy μ (fun x ↦ (χ i x - 1) • G x) +
    2 * vectorEnergy μ (fun x ↦ h x • C i x)
  rw [hid]
  exact vectorEnergy_add_le h₁ h₂

theorem capacity_product_pair_tendsto {h : X → ℝ} {G : X → V}
    (hh : MemLp h 2 μ) (hG : MemLp G 2 μ)
    (χ : ℕ → X → ℝ) (hχ : ∀ i, AEStronglyMeasurable (χ i) μ)
    (hχb : ∀ i, ∀ᵐ x ∂μ, χ i x ∈ Icc (0 : ℝ) 1)
    (hχlim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ χ i x) atTop (𝓝 1))
    {M : ℝ} (hM : 0 ≤ M) (hhb : ∀ᵐ x ∂μ, ‖h x‖ ≤ M)
    (C : ℕ → X → V) (hC : ∀ i, MemLp (C i) 2 μ)
    (hC0 : Tendsto (fun i ↦ vectorEnergy μ (C i)) atTop (𝓝 0)) :
    ∃ (hm : ∀ i, MemLp (fun x ↦ χ i x * h x) 2 μ)
      (hg : ∀ i, MemLp (fun x ↦ χ i x • G x + h x • C i x) 2 μ),
      Tendsto (fun i ↦ ((hm i).toLp (fun x ↦ χ i x * h x),
        (hg i).toLp (fun x ↦ χ i x • G x + h x • C i x))) atTop
        (𝓝 (hh.toLp h, hG.toLp G)) := by
  have hχnorm : ∀ i, ∀ᵐ x ∂μ, ‖χ i x‖ ≤ 1 := by
    intro i
    filter_upwards [hχb i] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  have hm : ∀ i, MemLp (fun x ↦ χ i x * h x) 2 μ := by
    intro i
    apply hh.of_le_mul (c := 1) ((hχ i).mul hh.aestronglyMeasurable)
    filter_upwards [hχnorm i] with x hx
    change ‖χ i x * h x‖ ≤ 1 * ‖h x‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  have hg : ∀ i, MemLp (fun x ↦ χ i x • G x + h x • C i x) 2 μ := by
    intro i
    have hg₁ : MemLp (fun x ↦ χ i x • G x) 2 μ := by
      apply hG.of_le_mul (c := 1) ((hχ i).smul hG.aestronglyMeasurable)
      filter_upwards [hχnorm i] with x hx
      change ‖χ i x • G x‖ ≤ 1 * ‖G x‖
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    have hg₂ : MemLp (fun x ↦ h x • C i x) 2 μ := by
      apply (hC i).of_le_mul (c := M) (hh.aestronglyMeasurable.smul (hC i).aestronglyMeasurable)
      filter_upwards [hhb] with x hx
      change ‖h x • C i x‖ ≤ M * ‖C i x‖
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    exact hg₁.add hg₂
  refine ⟨hm, hg, ?_⟩
  apply Filter.Tendsto.prodMk_nhds
  · apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hm h hh).mpr
    apply tendsto_eLpNorm_two_of_vectorEnergy_zero_of_aestronglyMeasurable
      (fun i ↦ ((hm i).sub hh).aestronglyMeasurable)
    change Tendsto (fun i ↦ vectorEnergy μ (fun x ↦ χ i x * h x - h x)) atTop (𝓝 0)
    have hid : (fun i ↦ vectorEnergy μ (fun x ↦ χ i x * h x - h x)) =
        (fun i ↦ vectorEnergy μ (fun x ↦ (χ i x - 1) • h x)) := by
      funext i
      congr 1
      funext x
      change χ i x * h x - h x = (χ i x - 1) * h x
      ring
    rw [hid]
    exact vectorEnergy_omitted_tendsto_zero hh χ hχ hχb hχlim
  · apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hg G hG).mpr
    apply tendsto_eLpNorm_two_of_vectorEnergy_zero_of_aestronglyMeasurable
      (fun i ↦ ((hg i).sub hG).aestronglyMeasurable)
    exact capacity_productGradient_tendsto hG χ hχ hχb hχlim
      hh.aestronglyMeasurable hM hhb C hC hC0

end SobolevLimits

section Caccioppoli
variable {X V : Type*} [MeasurableSpace X]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] {μ : Measure X}

theorem truncation_test_pointwise (A B : V) {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    inner ℝ A ((2 * (1 - h)) • B - A) ≤
      2 * ‖B‖ ^ 2 - (1 / 2 : ℝ) * ‖A‖ ^ 2 := by
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hcoef : 0 ≤ 2 * (1 - h) := by positivity
  have hi := mul_le_mul_of_nonneg_left (real_inner_le_norm A B) hcoef
  have hn : 0 ≤ ‖A‖ * ‖B‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hh := mul_nonneg h0 hn
  nlinarith [sq_nonneg (‖A‖ - 2 * ‖B‖)]

theorem truncation_test_energy {A B : X → V}
    (hA : MemLp A 2 μ) (hB : MemLp B 2 μ)
    {h : X → ℝ} (hh : AEStronglyMeasurable h μ)
    (hb : ∀ᵐ x ∂μ, h x ∈ Icc (0 : ℝ) 1)
    (htest : 0 ≤ ∫ x, inner ℝ (A x) ((2 * (1 - h x)) • B x - A x) ∂μ) :
    (∫ x, ‖A x‖ ^ 2 ∂μ) ≤ 4 * ∫ x, ‖B x‖ ^ 2 ∂μ := by
  have hC : MemLp (fun x ↦ (2 * (1 - h x)) • B x) 2 μ := by
    apply hB.of_le_mul (c := 2) ((aestronglyMeasurable_const.mul
      (aestronglyMeasurable_const.sub hh)).smul hB.aestronglyMeasurable)
    filter_upwards [hb] with x hx
    change ‖(2 * (1 - h x)) • B x‖ ≤ 2 * ‖B x‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by nlinarith [hx.2])]
    exact mul_le_mul_of_nonneg_right (by linarith [hx.1]) (norm_nonneg _)
  have hCsub : MemLp (fun x ↦ (2 * (1 - h x)) • B x - A x) 2 μ := hC.sub hA
  have hi : Integrable (fun x ↦ inner ℝ (A x)
      ((2 * (1 - h x)) • B x - A x)) μ := by
    apply (L2.integrable_inner (𝕜 := ℝ) (hA.toLp A)
      (hCsub.toLp (fun x ↦ (2 * (1 - h x)) • B x - A x))).congr
    filter_upwards [hA.coeFn_toLp, hCsub.coeFn_toLp] with x hx hy
    rw [hx, hy]
  have hAs := (memLp_two_iff_integrable_sq_norm hA.aestronglyMeasurable).mp hA
  have hBs := (memLp_two_iff_integrable_sq_norm hB.aestronglyMeasurable).mp hB
  have hu : Integrable (fun x ↦ 2 * ‖B x‖ ^ 2 - (1 / 2 : ℝ) * ‖A x‖ ^ 2) μ :=
    (hBs.const_mul 2).sub (hAs.const_mul (1 / 2))
  have hle := integral_mono_ae hi hu (by
    filter_upwards [hb] with x hx using truncation_test_pointwise (A x) (B x) hx.1 hx.2)
  rw [integral_sub (hBs.const_mul 2) (hAs.const_mul (1 / 2)),
    integral_const_mul, integral_const_mul] at hle
  linarith

end Caccioppoli
end RPI

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
namespace RPI.Boundary

theorem capacity_trace_mem_sobolevGraph {n : ℕ} {S Z : Set (Space n)}
    (hS : IsClosed S) (V : Set (Space n))
    {h : Space n → ℝ} {G : Space n → Space n}
    (hreg : ∀ x ∈ S \ Z, HasSmoothTraceJetAt S h G x)
    (hh : MemLp h 2 ((surfaceMeasure S).restrict V))
    (hG : MemLp G 2 ((surfaceMeasure S).restrict V))
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᵐ x ∂(surfaceMeasure S).restrict V, ‖h x‖ ≤ M)
    (χ : ℕ → Space n → ℝ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hχzero : ∀ i, ∃ U : Set (Space n), IsOpen U ∧ Z ⊆ U ∧ ∀ x ∈ U, χ i x = 0)
    (hχb : ∀ i, ∀ᵐ x ∂(surfaceMeasure S).restrict V, χ i x ∈ Icc (0 : ℝ) 1)
    (hχlim : ∀ᵐ x ∂(surfaceMeasure S).restrict V,
      Tendsto (fun i ↦ χ i x) atTop (𝓝 1))
    (hC : ∀ i, MemLp (surfaceGradient S (χ i)) 2 ((surfaceMeasure S).restrict V))
    (hC0 : Tendsto (fun i ↦ vectorEnergy ((surfaceMeasure S).restrict V)
      (surfaceGradient S (χ i))) atTop (𝓝 0)) :
    (hh.toLp h, hG.toLp G) ∈ closure (smoothGradientGraph S V) := by
  obtain ⟨hm, hg, ht⟩ := capacity_product_pair_tendsto hh hG χ
    (fun i ↦ (hχ i).continuous.aestronglyMeasurable) hχb hχlim hM hbound
    (fun i ↦ surfaceGradient S (χ i)) hC hC0
  apply mem_closure_of_tendsto ht
  apply Filter.Eventually.of_forall
  intro i
  obtain ⟨F, hF, hFe, hFG⟩ := exists_smooth_cutoff_trace hS hreg (χ i) (hχ i) (hχzero i)
  have hμS : ∀ᵐ x ∂(surfaceMeasure S).restrict V, x ∈ S :=
    ae_restrict_of_ae (ae_restrict_mem hS.measurableSet)
  have he : F =ᵐ[(surfaceMeasure S).restrict V] (fun x ↦ χ i x * h x) := by
    filter_upwards [hμS] with x hx using hFe hx
  have hge : surfaceGradient S F =ᵐ[(surfaceMeasure S).restrict V]
      (fun x ↦ χ i x • G x + h x • surfaceGradient S (χ i) x) := by
    filter_upwards [hμS] with x hx using hFG hx
  let hfmem := MemLp.ae_eq he.symm (hm i)
  let hgfmem := MemLp.ae_eq hge.symm (hg i)
  exact ⟨F, hF, hfmem, hgfmem, Prod.ext
    ((hm i).toLp_congr hfmem he.symm) ((hg i).toLp_congr hgfmem hge.symm)⟩

end RPI.Boundary

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
namespace RPI
section EnergyClosure
variable {X V : Type*} [MeasurableSpace X]
  [NormedAddCommGroup V] {μ : Measure X}

theorem vectorEnergy_eq_enorm_toLp_sq {F : X → V} (hF : MemLp F 2 μ) :
    vectorEnergy μ F = ‖hF.toLp F‖ₑ ^ 2 := by
  rw [Lp.enorm_toLp,
    eLpNorm_two_eq_vectorEnergy_rpow_of_aestronglyMeasurable hF.aestronglyMeasurable,
    ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

theorem vectorEnergy_tendsto_of_toLp_tendsto {F : ℕ → X → V} {G : X → V}
    (hF : ∀ i, MemLp (F i) 2 μ) (hG : MemLp G 2 μ)
    (ht : Tendsto (fun i ↦ (hF i).toLp (F i)) atTop (𝓝 (hG.toLp G))) :
    Tendsto (fun i ↦ vectorEnergy μ (F i)) atTop (𝓝 (vectorEnergy μ G)) := by
  have he : (fun i ↦ vectorEnergy μ (F i)) =
      (fun i ↦ ‖(hF i).toLp (F i)‖ₑ ^ 2) :=
    funext (fun i ↦ vectorEnergy_eq_enorm_toLp_sq (hF i))
  rw [he, vectorEnergy_eq_enorm_toLp_sq hG]
  exact ENNReal.Tendsto.pow ht.enorm

variable [InnerProductSpace ℝ V]

theorem memLp_of_regular_caccioppoli
    {h η : X → ℝ} {H D : X → V}
    (hh : AEStronglyMeasurable h μ)
    (hb : ∀ᵐ x ∂μ, h x ∈ Icc (0 : ℝ) 1)
    (hη : MemLp η 2 μ) (hD : MemLp D 2 μ)
    {M : ℝ} (hM : 0 ≤ M) (hηb : ∀ᵐ x ∂μ, ‖η x‖ ≤ M)
    (χ : ℕ → X → ℝ) (hχ : ∀ i, AEStronglyMeasurable (χ i) μ)
    (hχb : ∀ i, ∀ᵐ x ∂μ, χ i x ∈ Icc (0 : ℝ) 1)
    (hχlim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ χ i x) atTop (𝓝 1))
    (C : ℕ → X → V) (hC : ∀ i, MemLp (C i) 2 μ)
    (hC0 : Tendsto (fun i ↦ vectorEnergy μ (C i)) atTop (𝓝 0))
    (hA : ∀ i, MemLp (fun x ↦ χ i x • H x) 2 μ)
    (htest : ∀ i, 0 ≤ ∫ x, inner ℝ (χ i x • H x)
      ((2 * (1 - h x)) • (χ i x • D x + η x • C i x) - χ i x • H x) ∂μ) :
    MemLp H 2 μ ∧ vectorEnergy μ H ≤ 4 * vectorEnergy μ D := by
  obtain ⟨_, hB, hBt⟩ := capacity_product_pair_tendsto hη hD χ hχ hχb hχlim
    hM hηb C hC hC0
  have hBE := vectorEnergy_tendsto_of_toLp_tendsto hB hD hBt.snd_nhds
  have hbound : ∀ i, vectorEnergy μ (fun x ↦ χ i x • H x) ≤
      4 * vectorEnergy μ (fun x ↦ χ i x • D x + η x • C i x) := by
    intro i
    have he := truncation_test_energy (hA i) (hB i) hh hb (htest i)
    have he' := ENNReal.ofReal_le_ofReal he
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)] at he'
    simpa only [vectorEnergy, ofReal_integral_eq_lintegral_ofReal
      ((memLp_two_iff_integrable_sq_norm (hA i).aestronglyMeasurable).mp (hA i))
      (ae_of_all μ (fun x ↦ sq_nonneg ‖χ i x • H x‖)),
      ofReal_integral_eq_lintegral_ofReal
      ((memLp_two_iff_integrable_sq_norm (hB i).aestronglyMeasurable).mp (hB i))
      (ae_of_all μ (fun x ↦ sq_nonneg ‖χ i x • D x + η x • C i x‖)),
      ENNReal.ofReal_ofNat] using he'
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun i ↦ χ i x • H x) atTop (𝓝 (H x)) := by
    filter_upwards [hχlim] with x hx
    simpa only [one_smul] using hx.smul_const (H x)
  have hH : AEStronglyMeasurable H μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun i ↦ (hA i).aestronglyMeasurable) hlim
  have hBE' : Tendsto (fun i ↦ 4 * vectorEnergy μ
      (fun x ↦ χ i x • D x + η x • C i x)) atTop (𝓝 (4 * vectorEnergy μ D)) :=
    ENNReal.Tendsto.const_mul hBE (Or.inr (by norm_num))
  have he := vectorEnergy_le_of_ae_tendsto (fun i ↦ (hA i).aestronglyMeasurable) hlim
    (Eventually.of_forall hbound) hBE'
  refine ⟨(memLp_two_iff_vectorEnergy hH).mpr (he.trans_lt ?_), he⟩
  exact ENNReal.mul_lt_top (by norm_num)
    ((memLp_two_iff_vectorEnergy hD.aestronglyMeasurable).mp hD)

end EnergyClosure
end RPI

end

end OAI
