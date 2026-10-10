import Mathlib

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: WeightedRenyi. -/




open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace RegularPointCoordinates

 

theorem density_power_hasDerivAt {a q : ℝ} (ha : 0 ≤ a) (hq : 0 < q) :
    HasDerivAt (fun p : ℝ => a^p) (Real.log a*a^q) q := by
  rcases eq_or_lt_of_le ha with rfl | ha
  · simp only [Real.log_zero, zero_mul]
    apply (hasDerivAt_const q (0:ℝ)).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hq] with p hp
    exact Real.zero_rpow hp.ne'
  · simpa using (hasDerivAt_id q).const_rpow ha

 

theorem density_power_secant_lower {a q : ℝ} (ha : 0 ≤ a) (hq : 1/2 ≤ q)
    (hq1 : q < 1) : -2 ≤ (a-a^q)/(1-q) := by
  rcases eq_or_lt_of_le ha with rfl | ha
  · rw [Real.zero_rpow (by linarith : q ≠ 0)]
    norm_num
  obtain ⟨c, hc, hd⟩ := exists_hasDerivAt_eq_slope (fun p : ℝ => a^p)
    (fun p => Real.log a*a^p) hq1 (Real.continuous_const_rpow ha.ne').continuousOn
    (fun c hc => density_power_hasDerivAt ha.le (by linarith [hc.1]))
  rw [Real.rpow_one] at hd
  rw [← hd]
  by_cases ha1 : a ≤ 1
  · have hbound := (Real.abs_log_mul_self_rpow_lt a c ha ha1 (by linarith [hc.1])).le
    have hi : 1/c ≤ 2 := (div_le_iff₀ (by linarith [hc.1] : 0 < c)).mpr (by linarith [hc.1])
    have := neg_le_of_abs_le (hbound.trans hi)
    linarith
  · exact (by norm_num : (-2:ℝ) ≤ 0).trans
      (mul_nonneg (Real.log_nonneg (le_of_not_ge ha1)) (Real.rpow_nonneg ha.le _))

theorem entropy_density_lower {a : ℝ} (ha : 0 ≤ a) : -2 ≤ a*Real.log a := by
  rcases eq_or_lt_of_le ha with rfl | ha
  · simp
  by_cases ha1 : a ≤ 1
  · have hb := (Real.abs_log_mul_self_rpow_lt a 1 ha ha1 (by norm_num)).le
    simp only [Real.rpow_one, div_one] at hb
    nlinarith [neg_le_of_abs_le hb]
  · exact (by norm_num : (-2:ℝ) ≤ 0).trans
      (mul_nonneg ha.le (Real.log_nonneg (le_of_not_ge ha1)))

theorem density_power_secant_tendsto {a : ℝ} (ha : 0 ≤ a) (q : ℕ → ℝ)
    (hq : ∀ i, q i ≠ 1) (hqlim : Tendsto q atTop (𝓝 1)) :
    Tendsto (fun i => (a-a^(q i))/(1-q i)) atTop (𝓝 (a*Real.log a)) := by
  have hd := (density_power_hasDerivAt ha (by norm_num : (0:ℝ) < 1)).tendsto_slope
  have ht : Tendsto q atTop (𝓝[≠] (1:ℝ)) := tendsto_nhdsWithin_iff.mpr
    ⟨hqlim, Eventually.of_forall hq⟩
  have hs := hd.comp ht
  have heq : (fun i => (a-a^(q i))/(1-q i)) = (fun i => slope (fun p : ℝ => a^p) 1 (q i)) := by
    ext i
    rw [slope_def_field, Real.rpow_one]
    rw [show 1-q i = -(q i-1) by ring, div_neg, ← neg_div, neg_sub]
  rw [heq]
  simpa only [Function.comp_def, Real.rpow_one, mul_comm] using hs

 

theorem integrable_of_nonneg_fatou_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : ℕ → X → ℝ) (g : X → ℝ)
    (hf : ∀ i, Integrable (f i) μ) (hg : AEStronglyMeasurable g μ)
    (hf0 : ∀ i, 0 ≤ᵐ[μ] f i) (hg0 : 0 ≤ᵐ[μ] g)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => f i x) atTop (𝓝 (g x)))
    (b : ℕ → ℝ) (B : ℝ) (hb : ∀ i, (∫ x, f i x ∂μ) ≤ b i)
    (hbB : Tendsto b atTop (𝓝 B)) : Integrable g μ ∧ (∫ x, g x ∂μ) ≤ B := by
  have hB : 0 ≤ B := ge_of_tendsto hbB (Eventually.of_forall fun i =>
    (integral_nonneg_of_ae (hf0 i)).trans (hb i))
  have hlim' : ∀ᵐ x ∂μ, Tendsto (fun i => ENNReal.ofReal (f i x)) atTop
      (𝓝 (ENNReal.ofReal (g x))) := hlim.mono fun _ hx =>
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hx
  have hle : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) ≤ ENNReal.ofReal B := by
    calc
      _ = ∫⁻ x, liminf (fun i => ENNReal.ofReal (f i x)) atTop ∂μ :=
        lintegral_congr_ae (hlim'.mono fun _ h => h.liminf_eq.symm)
      _ ≤ liminf (fun i => ∫⁻ x, ENNReal.ofReal (f i x) ∂μ) atTop :=
        lintegral_liminf_le' fun i => (hf i).aestronglyMeasurable.aemeasurable.ennreal_ofReal
      _ ≤ liminf (fun i => ENNReal.ofReal (b i)) atTop := by
        apply liminf_le_liminf (Eventually.of_forall fun i => ?_)
        rw [← ofReal_integral_eq_lintegral_ofReal (hf i) (hf0 i)]
        exact ENNReal.ofReal_le_ofReal (hb i)
      _ = ENNReal.ofReal B :=
        (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hbB).liminf_eq
  have hI : Integrable g μ := ⟨hg, (hasFiniteIntegral_iff_ofReal hg0).mpr
    (lt_of_le_of_lt hle ENNReal.ofReal_lt_top)⟩
  refine ⟨hI, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hB).mp
  rwa [ofReal_integral_eq_lintegral_ofReal hI hg0]

 

theorem integrable_density_power {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (ρ : X → ℝ) (hρ : Measurable ρ)
    (hI : Integrable ρ μ) (hρ0 : 0 ≤ᵐ[μ] ρ) {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    Integrable (fun x => (ρ x)^q) μ := by
  apply ((integrable_const (1:ℝ)).add hI).mono' (hρ.pow_const q).aestronglyMeasurable
  filter_upwards [hρ0] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx q)]
  by_cases hx1 : ρ x ≤ 1
  · exact (Real.rpow_le_one hx hx1 hq).trans (le_add_of_nonneg_right hx)
  · have hh := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hx1) hq1
    rw [Real.rpow_one] at hh
    change ρ x ^ q ≤ 1+ρ x
    linarith

 

theorem entropy_le_of_renyi_variation_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (ρ : X → ℝ) (hρ : Measurable ρ)
    (hI : Integrable ρ μ) (hρ0 : 0 ≤ᵐ[μ] ρ)
    (q : ℕ → ℝ) (hq : ∀ i, 1/2 ≤ q i) (hq1 : ∀ i, q i < 1)
    (hqlim : Tendsto q atTop (𝓝 1)) (b : ℕ → ℝ) (B : ℝ)
    (hbB : Tendsto b atTop (𝓝 B))
    (hbound : ∀ i, ((∫ x, ρ x ∂μ) - (∫ x, (ρ x)^(q i) ∂μ))/(1-q i) ≤ b i) :
    Integrable (fun x => ρ x*Real.log (ρ x)) μ ∧
      (∫ x, ρ x*Real.log (ρ x) ∂μ) ≤ B := by
  let F : ℕ → X → ℝ := fun i x => (ρ x-(ρ x)^(q i))/(1-q i)+2
  let g : X → ℝ := fun x => ρ x*Real.log (ρ x)+2
  have hpow (i : ℕ) : Integrable (fun x => (ρ x)^(q i)) μ :=
    integrable_density_power μ ρ hρ hI hρ0 (by linarith [hq i]) (hq1 i).le
  have hFI (i : ℕ) : Integrable (F i) μ :=
    ((hI.sub (hpow i)).div_const (1-q i)).add (integrable_const 2)
  have hgm : AEStronglyMeasurable g μ :=
    ((hρ.mul (Real.measurable_log.comp hρ)).add measurable_const).aestronglyMeasurable
  have hF0 (i : ℕ) : 0 ≤ᵐ[μ] F i := by
    filter_upwards [hρ0] with x hx
    dsimp [F]
    linarith [density_power_secant_lower hx (hq i) (hq1 i)]
  have hg0 : 0 ≤ᵐ[μ] g := by
    filter_upwards [hρ0] with x hx
    dsimp [g]
    linarith [entropy_density_lower hx]
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) atTop (𝓝 (g x)) := by
    filter_upwards [hρ0] with x hx
    exact (density_power_secant_tendsto hx q (fun i => (hq1 i).ne) hqlim).add_const 2
  have hbound' (i : ℕ) : (∫ x, F i x ∂μ) ≤ b i + 2*(μ Set.univ).toReal := by
    dsimp [F]
    have hD : Integrable (fun x => (ρ x-(ρ x)^(q i))/(1-q i)) μ :=
      (hI.sub (hpow i)).div_const _
    rw [integral_add hD (integrable_const 2), integral_div,
      integral_sub hI (hpow i), integral_const]
    simp only [smul_eq_mul, measureReal_def]
    linarith [hbound i]
  obtain ⟨hgI, hgB⟩ := integrable_of_nonneg_fatou_bound μ F g hFI hgm hF0 hg0 hlim
    (fun i => b i + 2*(μ Set.univ).toReal) (B+2*(μ Set.univ).toReal) hbound'
    (hbB.add_const _)
  have hEnt : Integrable (fun x => ρ x*Real.log (ρ x)) μ := by
    convert hgI.sub (integrable_const (2:ℝ)) using 1
    ext x
    simp [g]
  refine ⟨hEnt, ?_⟩
  dsimp [g] at hgB
  rw [integral_add hEnt (integrable_const 2), integral_const, smul_eq_mul, measureReal_def] at hgB
  linarith

 

theorem entropy_le_of_renyi_variation_bound_on_support {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ρ : X → ℝ) (hρ : Measurable ρ) (hI : Integrable ρ μ)
    (hρ0 : 0 ≤ᵐ[μ] ρ) (s : Set X) (hsfin : μ s ≠ ∞)
    (hsupp : ∀ᵐ x ∂μ, x ∉ s → ρ x = 0)
    (q : ℕ → ℝ) (hq : ∀ i, 1/2 ≤ q i) (hq1 : ∀ i, q i < 1)
    (hqlim : Tendsto q atTop (𝓝 1)) (B : ℝ)
    (hbound : ∀ i, ((∫ x, ρ x ∂μ) - (∫ x, (ρ x)^(q i) ∂μ))/(1-q i) ≤ B) :
    Integrable (fun x => ρ x*Real.log (ρ x)) μ ∧
      (∫ x, ρ x*Real.log (ρ x) ∂μ) ≤ B := by
  let : IsFiniteMeasure (μ.restrict s) := ⟨by simpa using hsfin.lt_top⟩
  have hpows (i : ℕ) : ∀ᵐ x ∂μ, x ∉ s → (ρ x)^(q i) = 0 := by
    filter_upwards [hsupp] with x hx hxs
    rw [hx hxs, Real.zero_rpow (by linarith [hq i] : q i ≠ 0)]
  have hents : ∀ᵐ x ∂μ, x ∉ s → ρ x*Real.log (ρ x) = 0 := by
    filter_upwards [hsupp] with x hx hxs
    rw [hx hxs, zero_mul]
  obtain ⟨hEnt, hEntB⟩ := entropy_le_of_renyi_variation_bound (μ.restrict s) ρ hρ
    hI.integrableOn (ae_restrict_of_ae hρ0) q hq hq1 hqlim (fun _ => B) B
    tendsto_const_nhds (fun i => by
      rw [setIntegral_eq_integral_of_ae_compl_eq_zero hsupp,
        setIntegral_eq_integral_of_ae_compl_eq_zero (hpows i)]
      exact hbound i)
  exact ⟨IntegrableOn.integrable_of_ae_notMem_eq_zero hEnt hents, by
    rwa [setIntegral_eq_integral_of_ae_compl_eq_zero hents] at hEntB⟩

 
theorem density_power_secant_sqrt_lower {a q : ℝ} (ha : 0 ≤ a)
    (hq : 3/4 ≤ q) (hq1 : q < 1) : -4*(a^(1/2:ℝ)) ≤ (a-a^q)/(1-q) := by
  rcases eq_or_lt_of_le ha with rfl | ha
  · rw [Real.zero_rpow (by linarith : q ≠ 0), Real.zero_rpow (by norm_num : (1/2:ℝ) ≠ 0)]
    norm_num
  obtain ⟨c,hc,hd⟩ := exists_hasDerivAt_eq_slope (fun p : ℝ => a^p)
    (fun p => Real.log a*a^p) hq1 (Real.continuous_const_rpow ha.ne').continuousOn
    (fun c hc => density_power_hasDerivAt ha.le (by linarith [hc.1]))
  rw [Real.rpow_one] at hd
  rw [← hd]
  by_cases ha1 : a ≤ 1
  · have hb := (Real.abs_log_mul_self_rpow_lt a (c-1/2) ha ha1 (by linarith [hc.1])).le
    have hi : 1/(c-1/2) ≤ 4 := (div_le_iff₀ (by linarith [hc.1] : 0 < c-1/2)).mpr
      (by linarith [hc.1])
    have hh := mul_le_mul_of_nonneg_right (neg_le_of_abs_le (hb.trans hi))
      (Real.rpow_nonneg ha.le (1/2:ℝ))
    rw [mul_assoc,← Real.rpow_add ha,show c-1/2+1/2 = c by ring] at hh
    exact hh
  · have hh := mul_nonneg (Real.log_nonneg (le_of_not_ge ha1)) (Real.rpow_nonneg ha.le c)
    nlinarith [Real.rpow_nonneg ha.le (1/2:ℝ)]

theorem density_power_le_sqrt_add {a q : ℝ} (ha : 0 ≤ a) (hq : 1/2 ≤ q) (hq1 : q ≤ 1) :
    a^q ≤ a^(1/2:ℝ)+a := by
  by_cases h : a ≤ 1
  · exact (Real.rpow_le_rpow_of_exponent_ge' ha h (by norm_num) hq).trans (le_add_of_nonneg_right ha)
  · have hh := Real.rpow_le_rpow_of_exponent_le (le_of_not_ge h) hq1
    rw [Real.rpow_one] at hh
    exact hh.trans (le_add_of_nonneg_left (Real.rpow_nonneg ha _))

theorem integrable_density_power_of_sqrt {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ρ : X → ℝ) (hρ : Measurable ρ) (hI : Integrable ρ μ)
    (hρ0 : 0 ≤ᵐ[μ] ρ) (hS : Integrable (fun x => ρ x^(1/2:ℝ)) μ)
    {q : ℝ} (hq : 1/2 ≤ q) (hq1 : q ≤ 1) : Integrable (fun x => ρ x^q) μ := by
  apply (hS.add hI).mono' (hρ.pow_const q).aestronglyMeasurable
  filter_upwards [hρ0] with x hx
  rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hx _)]
  exact density_power_le_sqrt_add hx hq hq1

 

theorem entropy_le_of_renyi_variation_bound_sqrt {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ρ : X → ℝ) (hρ : Measurable ρ)
    (hI : Integrable ρ μ) (hρ0 : 0 ≤ᵐ[μ] ρ)
    (hS : Integrable (fun x => ρ x^(1/2:ℝ)) μ)
    (q : ℕ → ℝ) (hq : ∀ i, 3/4 ≤ q i) (hq1 : ∀ i, q i < 1)
    (hqlim : Tendsto q atTop (𝓝 1)) (b : ℕ → ℝ) (B : ℝ)
    (hbB : Tendsto b atTop (𝓝 B))
    (hbound : ∀ i, ((∫x, ρ x ∂μ)-(∫x, ρ x^(q i) ∂μ))/(1-q i) ≤ b i) :
    Integrable (fun x => ρ x*Real.log (ρ x)) μ ∧
      (∫x, ρ x*Real.log (ρ x) ∂μ) ≤ B := by
  let G : X → ℝ := fun x => 4*ρ x^(1/2:ℝ)
  let F : ℕ → X → ℝ := fun i x => (ρ x-ρ x^(q i))/(1-q i)+G x
  let g : X → ℝ := fun x => ρ x*Real.log (ρ x)+G x
  have hGI : Integrable G μ := hS.const_mul 4
  have hpow (i : ℕ) : Integrable (fun x => ρ x^(q i)) μ :=
    integrable_density_power_of_sqrt μ ρ hρ hI hρ0 hS (by linarith [hq i]) (hq1 i).le
  have hFI (i : ℕ) : Integrable (F i) μ := ((hI.sub (hpow i)).div_const _).add hGI
  have hgm : AEStronglyMeasurable g μ :=
    ((hρ.mul (Real.measurable_log.comp hρ)).aestronglyMeasurable).add hGI.aestronglyMeasurable
  have hF0 (i : ℕ) : 0 ≤ᵐ[μ] F i := by
    filter_upwards [hρ0] with x hx
    dsimp [F,G]
    linarith [density_power_secant_sqrt_lower hx (hq i) (hq1 i)]
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) atTop (𝓝 (g x)) := by
    filter_upwards [hρ0] with x hx
    exact (density_power_secant_tendsto hx q (fun i => (hq1 i).ne) hqlim).add_const _
  have hg0 : 0 ≤ᵐ[μ] g := by
    filter_upwards [ae_all_iff.mpr hF0,hlim] with x hx hlim
    exact ge_of_tendsto hlim (Eventually.of_forall hx)
  have hb' (i : ℕ) : (∫x, F i x ∂μ) ≤ b i+∫x, G x ∂μ := by
    dsimp only [F]
    have hD : Integrable (fun x => (ρ x-ρ x^(q i))/(1-q i)) μ := (hI.sub (hpow i)).div_const _
    rw [integral_add hD hGI,integral_div,
      integral_sub hI (hpow i)]
    linarith [hbound i]
  obtain ⟨hi,hb⟩ := integrable_of_nonneg_fatou_bound μ F g hFI hgm hF0 hg0 hlim
    (fun i => b i+∫x, G x ∂μ) (B+∫x, G x ∂μ) hb' (hbB.add_const _)
  have hE : Integrable (fun x => ρ x*Real.log (ρ x)) μ := by
    convert hi.sub hGI using 1
    ext x
    simp [g]
  refine ⟨hE,?_⟩
  dsimp only [g] at hb
  rw [integral_add hE hGI] at hb
  linarith
end RegularPointCoordinates

end OAI
