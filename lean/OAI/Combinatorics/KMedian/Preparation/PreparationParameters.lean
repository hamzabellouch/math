import Mathlib

namespace OAI

section
section
namespace MetricKMedian.Preparation

noncomputable def farFactor (δ p₀ α β γ : ℝ) : ℝ :=
  max (1/p₀) (1+2*δ/(1-β-δ))*((1+α)/(1-α))+(β+1+δ)*γ/δ
noncomputable def shortfallFactor (p₀ γ g : ℝ) : ℝ :=
  Real.sqrt g+Real.sqrt (g/p₀)+(γ+Real.sqrt (g*(1+γ)))/p₀
noncomputable def nearFactor (p₀ Q γ g : ℝ) : ℝ :=
  1/p₀+Q*shortfallFactor p₀ γ g
noncomputable def failureFactor (γ g : ℝ) : ℝ := 4*g*(1+γ)/γ
noncomputable def parameterEnvelopeFar (a : ℝ) : ℝ :=
  max (1/(1-a)) (1+2*a/(1-a^2-a))*((1+a)/(1-a))+(a^2+1+a)*a^5
noncomputable def parameterEnvelopeNear (a : ℝ) : ℝ :=
  1/(1-a)+9*(a^2+1+a)*a^2
noncomputable def parameterEnvelope (a : ℝ) : ℝ :=
  max (parameterEnvelopeFar a) (parameterEnvelopeNear a)/(1-8*a^8)

theorem parameter_envelope_bounds {a g : ℝ} (ha : 0 < a) (ha32 : a ≤ 1/32)
    (hg : 0 < g) (hg14 : g ≤ a^14) :
    shortfallFactor (1-a) (a^6) g ≤ 9*a^6 ∧
    failureFactor (a^6) g ≤ 8*a^8 ∧
    failureFactor (a^6) g < 1/2 ∧
    nearFactor (1-a) ((a^2+1+a)/a^4) (a^6) g ≤ parameterEnvelopeNear a := by
  have ha1 : a ≤ 1 := by linarith only [ha32]
  have hp0 : 0 < 1-a := by linarith only [ha32]
  have hp2 : (1/2:ℝ) ≤ 1-a := by linarith only [ha32]
  have ha6 : a^6 ≤ 1 := pow_le_one₀ ha.le ha1
  have ha76 : a^7 ≤ a^6 := pow_le_pow_of_le_one ha.le ha1 (by decide)
  have ha8 : a^8 ≤ a := by simpa only [pow_one] using
    (pow_le_pow_of_le_one ha.le ha1 (show 1 ≤ 8 by decide))
  have hroot : Real.sqrt g ≤ a^7 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    simpa only [← pow_mul] using hg14
  have hrootp : Real.sqrt (g/(1-a)) ≤ 2*a^7 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    rw [show (2*a^7)^2=4*a^14 by ring]
    apply (div_le_iff₀ hp0).mpr
    have he := mul_le_mul_of_nonneg_left hp2 (show 0 ≤ a^14 by positivity)
    nlinarith only [he,hg14,pow_nonneg ha.le 14]
  have hrootγ : Real.sqrt (g*(1+a^6)) ≤ 2*a^7 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    rw [show (2*a^7)^2=4*a^14 by ring]
    have he := mul_le_mul_of_nonneg_left ha6 hg.le
    nlinarith only [he,hg14,hg.le]
  have hdiv : (a^6+Real.sqrt (g*(1+a^6)))/(1-a) ≤ 2*(a^6+2*a^7) := by
    apply (div_le_iff₀ hp0).mpr
    have he := mul_le_mul_of_nonneg_left hp2 (show 0 ≤ a^6+2*a^7 by positivity)
    nlinarith only [he,hrootγ]
  have hH : shortfallFactor (1-a) (a^6) g ≤ 9*a^6 := by
    dsimp only [shortfallFactor]
    linarith only [hroot,hrootp,hdiv,ha76]
  have hρ : failureFactor (a^6) g ≤ 8*a^8 := by
    dsimp only [failureFactor]
    apply (div_le_iff₀ (show 0 < a^6 by positivity)).mpr
    have he := mul_le_mul_of_nonneg_left ha6 hg.le
    have hid : 8*a^8*a^6=8*a^14 := by ring
    rw [hid]
    nlinarith only [he,hg14]
  refine ⟨hH,hρ,by linarith only [hρ,ha8,ha32],?_⟩
  dsimp only [nearFactor,parameterEnvelopeNear]
  apply add_le_add le_rfl
  have he := mul_le_mul_of_nonneg_left hH (show 0 ≤ (a^2+1+a)/a^4 by positivity)
  apply he.trans_eq
  field_simp

theorem parameter_envelope_continuous : ContinuousAt parameterEnvelope 0 := by
  unfold parameterEnvelope parameterEnvelopeFar parameterEnvelopeNear
  fun_prop (disch := norm_num)

theorem parameter_envelope_zero : parameterEnvelope 0=1 := by
  norm_num [parameterEnvelope,parameterEnvelopeFar,parameterEnvelopeNear]

theorem exists_preparation_parameters {η : ℝ} (hη : 0 < η) :
    ∃ δ M T₁ γ : ℚ,
      0 < (δ:ℝ) ∧ (δ:ℝ) ≤ 1/4 ∧ 0 < (M:ℝ) ∧ 0 < (T₁:ℝ) ∧
      0 < (γ:ℝ) ∧ (γ:ℝ) ≤ 1 ∧
      1/((M:ℝ)*(δ:ℝ)) ≤ 1/8 ∧
      (M:ℝ)/((δ:ℝ)*(T₁:ℝ)) ≤ 1/4 ∧
      ∃ g₀ : ℝ, 0 < g₀ ∧ ∀ g : ℝ, 0 < g → g ≤ g₀ →
        failureFactor (γ:ℝ) g < 1/2 ∧
        max (farFactor (δ:ℝ) (1-1/((M:ℝ)*(δ:ℝ)))
              ((M:ℝ)/((δ:ℝ)*(T₁:ℝ))) ((M:ℝ)/(T₁:ℝ)) (γ:ℝ))
          (nearFactor (1-1/((M:ℝ)*(δ:ℝ))) ((M:ℝ)+(1+(δ:ℝ))*(T₁:ℝ)) (γ:ℝ) g)
          /(1-failureFactor (γ:ℝ) g) ≤ 1+η := by
  have hev := parameter_envelope_continuous.eventually_lt
    (continuousAt_const (y := 1+η)) (by rw [parameter_envelope_zero]; linarith only [hη])
  obtain ⟨r,hr,hev⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨a,ha,har⟩ := exists_rat_btwn (lt_min hr (show (0:ℝ) < 1/32 by norm_num))
  have ha32 : (a:ℝ) ≤ 1/32 := (har.trans_le (min_le_right _ _)).le
  have hclose : parameterEnvelope (a:ℝ) < 1+η := hev (by
    rw [Real.dist_eq,sub_zero,abs_of_pos ha]
    exact har.trans_le (min_le_left _ _))
  have hanz : (a:ℝ) ≠ 0 := ha.ne'
  have ha1 : (a:ℝ) ≤ 1 := by linarith only [ha32]
  have htheta : 1/((1/(a:ℝ)^2)*(a:ℝ))=(a:ℝ) := by field_simp
  have halpha : (1/(a:ℝ)^2)/((a:ℝ)*(1/(a:ℝ)^4))=(a:ℝ) := by field_simp
  have hbeta : (1/(a:ℝ)^2)/(1/(a:ℝ)^4)=(a:ℝ)^2 := by field_simp
  have hQ : (1/(a:ℝ)^2)+(1+(a:ℝ))*(1/(a:ℝ)^4)=
      ((a:ℝ)^2+1+(a:ℝ))/(a:ℝ)^4 := by field_simp; ring
  refine ⟨a,1/a^2,1/a^4,a^6,?_⟩
  push_cast
  rw [htheta,halpha,hbeta,hQ]
  refine ⟨ha,by linarith only [ha32],by positivity,by positivity,by positivity,
    pow_le_one₀ ha.le ha1,by linarith only [ha32],by linarith only [ha32],
    (a:ℝ)^14,by positivity,?_⟩
  intro g hg hg14
  obtain ⟨_,hρ,hρhalf,hnear⟩ := parameter_envelope_bounds ha ha32 hg hg14
  refine ⟨hρhalf,?_⟩
  have hfar : farFactor (a:ℝ) (1-(a:ℝ)) (a:ℝ) ((a:ℝ)^2) ((a:ℝ)^6)=
      parameterEnvelopeFar (a:ℝ) := by
    unfold farFactor parameterEnvelopeFar
    congr 1
    field_simp
  have ha8 : (a:ℝ)^8 ≤ (a:ℝ) := by simpa only [pow_one] using
    (pow_le_pow_of_le_one ha.le ha1 (show 1 ≤ 8 by decide))
  have hden : 0 < 1-8*(a:ℝ)^8 := by linarith only [ha8,ha32]
  have hnonneg : 0 ≤ max (parameterEnvelopeFar (a:ℝ)) (parameterEnvelopeNear (a:ℝ)) := by
    apply le_trans _ (le_max_right _ _)
    unfold parameterEnvelopeNear
    have hp : 0 < 1-(a:ℝ) := by linarith only [ha32]
    positivity
  rw [hfar]
  calc
    _ ≤ max (parameterEnvelopeFar (a:ℝ)) (parameterEnvelopeNear (a:ℝ))/(1-failureFactor ((a:ℝ)^6) g) :=
      div_le_div_of_nonneg_right (max_le_max le_rfl hnear) (by linarith only [hρhalf])
    _ ≤ parameterEnvelope (a:ℝ) := div_le_div_of_nonneg_left hnonneg hden (by linarith only [hρ])
    _ ≤ 1+η := hclose.le

theorem all_fine_grids {g₀ : ℝ} (hg₀ : 0 < g₀) :
    ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → 0 < Δ ∧ 0 < (1/(Δ:ℝ)) ∧ 1/(Δ:ℝ) ≤ g₀ := by
  obtain ⟨N,hN⟩ := exists_nat_gt (max 0 (1/g₀))
  refine ⟨N,?_⟩
  intro Δ hΔ
  have hD : 0 < (Δ:ℝ) := (lt_of_le_of_lt (le_max_left _ _) hN).trans_le (by exact_mod_cast hΔ)
  refine ⟨by exact_mod_cast hD,by positivity,?_⟩
  apply (div_le_iff₀ hD).mpr
  have hlarge : 1/g₀ < (Δ:ℝ) := (lt_of_le_of_lt (le_max_right _ _) hN).trans_le (by exact_mod_cast hΔ)
  exact ((div_lt_iff₀ hg₀).mp hlarge).le.trans_eq (mul_comm _ _)

end MetricKMedian.Preparation
end
end

end OAI
