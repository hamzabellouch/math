import OAI.Probability.SLE.Multipoint.MultipointRegularizer

namespace OAI

/-! The angular generator calculation for the regularized factors of the
fixed-order multipoint radius estimate. The angular clock has generator
`(1/2)∂² + ((1-p)/2) cot(θ) ∂`, with `p = 4a-1`. -/

noncomputable section
open Set

namespace SLEExactGauge.Multipoint

def sinePower (r θ : ℝ) : ℝ := Real.sin θ ^ r

def sinePowerFirst (r θ : ℝ) : ℝ := r * Real.sin θ ^ (r-1) * Real.cos θ

def sinePowerSecond (r θ : ℝ) : ℝ :=
  r * (r-1) * Real.sin θ ^ (r-2) * Real.cos θ ^ 2 - r * Real.sin θ ^ r

lemma sinePower_hasDerivAt {r θ : ℝ} (hθ : Real.sin θ ≠ 0) :
    HasDerivAt (sinePower r) (sinePowerFirst r θ) θ := by
  apply ((Real.hasDerivAt_sin θ).rpow_const (p := r) (Or.inl hθ)).congr_deriv
  unfold sinePowerFirst
  ring

lemma sinePowerFirst_hasDerivAt {r θ : ℝ} (hθ : Real.sin θ ≠ 0) :
    HasDerivAt (sinePowerFirst r) (sinePowerSecond r θ) θ := by
  have hd := (((Real.hasDerivAt_sin θ).rpow_const (p := r-1) (Or.inl hθ)).const_mul r).mul
    (Real.hasDerivAt_cos θ)
  apply hd.congr_deriv
  dsimp only [sinePowerSecond]
  rw [show r-1-1 = r-2 by ring]
  have hs : Real.sin θ ^ (r-1) * Real.sin θ = Real.sin θ ^ r := by
    rw [← Real.rpow_add_one hθ]
    congr 1
    ring
  calc
    _ = r * (r-1) * Real.sin θ ^ (r-2) * Real.cos θ ^ 2 -
        r * (Real.sin θ ^ (r-1) * Real.sin θ) := by ring
    _ = _ := by rw [hs]

def sineGenerator (p r θ : ℝ) : ℝ :=
  sinePowerSecond r θ / 2 + (1-p)/2 * (Real.cos θ/Real.sin θ) * sinePowerFirst r θ

lemma sineGenerator_eq {p r θ : ℝ} (hθ : 0 < Real.sin θ) :
    sineGenerator p r θ = r*(r-p)/2 * Real.sin θ ^ (r-2) -
      r*(r+1-p)/2 * Real.sin θ ^ r := by
  unfold sineGenerator sinePowerSecond sinePowerFirst
  rw [Real.rpow_sub hθ, Real.rpow_sub hθ, Real.rpow_two, Real.rpow_one]
  have hcos : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [hcos]
  field_simp [hθ.ne']
  ring_nf
  rw [hcos]
  ring

lemma sineGenerator_eigen {p θ : ℝ} (hθ : 0 < Real.sin θ) :
    sineGenerator p p θ + p/2 * sinePower p θ = 0 := by
  rw [sineGenerator_eq hθ]
  unfold sinePower
  ring

def angularFactor (p δ θ : ℝ) : ℝ := sinePower p θ + δ*(1+sinePower (q p) θ)

def damping (p δ θ : ℝ) : ℝ := δ / angularFactor p δ θ * sinePower (q p-2) θ

def negativeDrift (p : ℝ) : ℝ := q p * (p-q p)/2

def driftAllowance (p : ℝ) : ℝ := p/2 + (p-q p)*(1+q p)/2 + 2

lemma negativeDrift_pos {p : ℝ} (hp : 0 < p) : 0 < negativeDrift p := by
  exact div_pos (mul_pos (q_pos hp) (sub_pos.mpr (q_lt_p hp))) (by norm_num)

lemma driftAllowance_pos {p : ℝ} (hp : 0 < p) : 0 < driftAllowance p := by
  have hq := q_pos hp
  have hqp := q_lt_p hp
  dsimp [driftAllowance]
  positivity

lemma angularFactor_pos {p δ θ : ℝ} (hδ : 0 < δ) (hθ : 0 < Real.sin θ) :
    0 < angularFactor p δ θ := by
  unfold angularFactor sinePower
  positivity

/-- Exact algebraic drift before estimating its negative singular term. -/
lemma regularized_generator {p δ σ θ : ℝ} (hθ : 0 < Real.sin θ) :
    sineGenerator p p θ + δ*sineGenerator p (q p) θ +
      (p/2)*angularFactor p δ θ + δ*σ*(1+sinePower (q p) θ) =
    δ*(p/2 + (p-q p)*(1+q p)/2*sinePower (q p) θ -
      negativeDrift p*sinePower (q p-2) θ + σ*(1+sinePower (q p) θ)) := by
  rw [sineGenerator_eq hθ, sineGenerator_eq hθ]
  unfold angularFactor sinePower negativeDrift
  ring

lemma regularized_bracket_le {p σ θ : ℝ} (hp : 0 < p)
    (hσ : σ ≤ 1) (hθ : 0 ≤ Real.sin θ) (hθ1 : Real.sin θ ≤ 1) :
    p/2 + (p-q p)*(1+q p)/2*sinePower (q p) θ -
      negativeDrift p*sinePower (q p-2) θ + σ*(1+sinePower (q p) θ) ≤
    driftAllowance p - negativeDrift p*sinePower (q p-2) θ := by
  have hs0 : 0 ≤ sinePower (q p) θ := Real.rpow_nonneg hθ _
  have hs1 : sinePower (q p) θ ≤ 1 := Real.rpow_le_one hθ hθ1 (q_pos hp).le
  have hk : 0 ≤ (p-q p)*(1+q p)/2 := by
    have := q_lt_p hp
    have := q_pos hp
    positivity
  have h1 := mul_le_mul_of_nonneg_left hs1 hk
  have h2 := mul_le_mul_of_nonneg_right hσ (by linarith : 0 ≤ 1+sinePower (q p) θ)
  unfold driftAllowance
  nlinarith

lemma angularFactor_ge_delta {p δ θ : ℝ} (hδ : 0 ≤ δ) (hθ : 0 ≤ Real.sin θ) :
    δ ≤ angularFactor p δ θ := by
  unfold angularFactor sinePower
  have hp := Real.rpow_nonneg hθ p
  have hq := Real.rpow_nonneg hθ (q p)
  nlinarith

lemma angularFactor_le_three {p δ θ : ℝ} (hp : 0 < p)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hθ : 0 ≤ Real.sin θ) :
    angularFactor p δ θ ≤ 3 := by
  have hp1 : sinePower p θ ≤ 1 := Real.rpow_le_one hθ (Real.sin_le_one θ) hp.le
  have hq1 : sinePower (q p) θ ≤ 1 := Real.rpow_le_one hθ (Real.sin_le_one θ) (q_pos hp).le
  have hq0 : 0 ≤ sinePower (q p) θ := Real.rpow_nonneg hθ _
  unfold angularFactor
  nlinarith

lemma angularFactor_endpoint_bounds {p θ : ℝ} (hp : 0 < p) (hθ : 0 ≤ Real.sin θ) :
    1 ≤ angularFactor p 1 θ ∧ angularFactor p 1 θ ≤ 3 :=
  ⟨angularFactor_ge_delta zero_le_one hθ,
    angularFactor_le_three hp zero_le_one le_rfl hθ⟩

def angularFactorFirst (p δ θ : ℝ) : ℝ :=
  sinePowerFirst p θ + δ*sinePowerFirst (q p) θ

lemma angularFactor_hasDerivAt {p δ θ : ℝ} (hθ : Real.sin θ ≠ 0) :
    HasDerivAt (angularFactor p δ) (angularFactorFirst p δ θ) θ := by
  apply ((sinePower_hasDerivAt (r := p) hθ).add
    (((hasDerivAt_const θ 1).add (sinePower_hasDerivAt (r := q p) hθ)).const_mul δ)).congr_deriv
  simp only [angularFactorFirst, zero_add]

lemma angularFactorFirst_bound {p δ θ : ℝ} (hp : 0 < p)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hθ : 0 < Real.sin θ) :
    |angularFactorFirst p δ θ| ≤ (p+q p)*Real.sin θ ^ (q p-1) := by
  have hpq : Real.sin θ ^ (p-1) ≤ Real.sin θ ^ (q p-1) :=
    Real.rpow_le_rpow_of_exponent_ge hθ (Real.sin_le_one θ) (by linarith [q_lt_p hp])
  have hq := (q_pos hp).le
  have hpow : 0 ≤ Real.sin θ ^ (q p-1) := Real.rpow_nonneg hθ.le _
  have hcos : |Real.cos θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have hfirst (r : ℝ) (hr : 0 ≤ r) : |sinePowerFirst r θ| ≤ r * Real.sin θ ^ (r-1) := by
    unfold sinePowerFirst
    rw [abs_mul, abs_of_nonneg (mul_nonneg hr (Real.rpow_nonneg hθ.le _))]
    exact mul_le_of_le_one_right (mul_nonneg hr (Real.rpow_nonneg hθ.le _)) hcos
  calc
    _ ≤ |sinePowerFirst p θ| + |δ*sinePowerFirst (q p) θ| := abs_add_le _ _
    _ = |sinePowerFirst p θ| + δ*|sinePowerFirst (q p) θ| := by
      rw [abs_mul, abs_of_nonneg hδ]
    _ ≤ p*Real.sin θ ^ (p-1) + δ*(q p*Real.sin θ ^ (q p-1)) :=
      add_le_add (hfirst p hp.le) (mul_le_mul_of_nonneg_left (hfirst (q p) hq) hδ)
    _ ≤ p*Real.sin θ ^ (q p-1) + q p*Real.sin θ ^ (q p-1) :=
      add_le_add (mul_le_mul_of_nonneg_left hpq hp.le)
        (mul_le_of_le_one_left (mul_nonneg hq hpow) hδ1)
    _ = _ := by ring

/-- The singular angular derivative is controlled by the damping term.
The exponent is chosen so that `eta * (q - 2) = q - 1`. -/
lemma normalized_angularFactorFirst_bound {p δ θ : ℝ} (hp : 0 < p)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hθ : 0 < Real.sin θ) :
    |angularFactorFirst p δ θ| / angularFactor p δ θ ≤
      (p+q p)*3^(eta p)*δ^(-1-eta p)*(damping p δ θ)^(eta p) := by
  let f := angularFactor p δ θ
  let e := eta p
  have hf : 0 < f := angularFactor_pos hδ hθ
  have hdf : δ ≤ f := angularFactor_ge_delta hδ.le hθ.le
  have hf3 : f ≤ 3 := angularFactor_le_three hp hδ.le hδ1 hθ.le
  have he : 0 < e := eta_pos
  have hD : 0 < damping p δ θ :=
    mul_pos (div_pos hδ hf) (Real.rpow_pos_of_pos hθ _)
  have hidentity : Real.sin θ ^ (q p-1) = (f/δ)^e * (damping p δ θ)^e := by
    rw [← Real.mul_rpow (div_pos hf hδ).le hD.le]
    have hcancel : f/δ*damping p δ θ = Real.sin θ ^ (q p-2) := by
      dsimp [damping, sinePower, f]
      field_simp [hδ.ne', (angularFactor_pos hδ hθ).ne']
    rw [hcancel, ← Real.rpow_mul hθ.le]
    congr 1
    exact ((mul_comm _ _).trans (eta_identity p)).symm
  have hpq : 0 ≤ p+q p := add_nonneg hp.le (q_pos hp).le
  calc
    _ ≤ ((p+q p)*Real.sin θ ^ (q p-1))/f :=
      div_le_div_of_nonneg_right (angularFactorFirst_bound hp hδ.le hδ1 hθ) hf.le
    _ ≤ ((p+q p)*Real.sin θ ^ (q p-1))/δ :=
      div_le_div_of_nonneg_left (mul_nonneg hpq (Real.rpow_nonneg hθ.le _)) hδ hdf
    _ = (p+q p)/δ * (f/δ)^e * (damping p δ θ)^e := by rw [hidentity]; ring
    _ ≤ (p+q p)/δ * (3/δ)^e * (damping p δ θ)^e := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hD.le _)
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hpq hδ.le)
      exact Real.rpow_le_rpow (div_pos hf hδ).le
        (div_le_div_of_nonneg_right hf3 hδ.le) he.le
    _ = _ := by
      rw [Real.div_rpow (by norm_num : (0:ℝ) ≤ 3) hδ.le,
        Real.rpow_sub hδ, Real.rpow_neg_one]
      ring

def driftThreshold (p : ℝ) : ℝ :=
  (negativeDrift p / (2*driftAllowance p)) ^ (1/(2-q p))

lemma driftThreshold_pos {p : ℝ} (hp : 0 < p) : 0 < driftThreshold p := by
  exact Real.rpow_pos_of_pos (div_pos (negativeDrift_pos hp)
    (mul_pos (by norm_num) (driftAllowance_pos hp))) _

lemma driftThreshold_lt_one {p : ℝ} (hp : 0 < p) : driftThreshold p < 1 := by
  have hq := q_pos hp
  have hq1 := q_lt_one (p := p)
  have hqp := q_lt_p hp
  have hk := negativeDrift_pos hp
  have hA := driftAllowance_pos hp
  have hden : 0 < 2-q p := by linarith
  have hsmall : negativeDrift p < 2*driftAllowance p := by
    unfold negativeDrift driftAllowance
    nlinarith [mul_nonneg (sub_nonneg.mpr hq1.le) (sub_nonneg.mpr hqp.le)]
  exact Real.rpow_lt_one (div_pos hk (by positivity)).le
    ((div_lt_one (by positivity)).mpr hsmall) (by positivity : 0 < 1/(2-q p))

lemma driftThreshold_identity {p : ℝ} (hp : 0 < p) :
    negativeDrift p * driftThreshold p ^ (q p-2) = 2*driftAllowance p := by
  have hk := negativeDrift_pos hp
  have hA := driftAllowance_pos hp
  have hq2 : 2-q p ≠ 0 := ne_of_gt (by linarith [q_lt_one (p := p)])
  unfold driftThreshold
  rw [← Real.rpow_mul (div_pos hk (by positivity)).le]
  have he : (1/(2-q p))*(q p-2) = -1 := by field_simp; ring
  rw [he, Real.rpow_neg_one]
  field_simp

/-- The negative singular part absorbs the bounded drift at small angles;
away from the endpoints the denominator supplies a fixed lower bound. -/
lemma regularized_drift_bound {p δ σ θ : ℝ} (hp : 0 < p)
    (hδ : 0 < δ) (hσ : σ ≤ 1) (hθ : 0 < Real.sin θ) :
    δ / angularFactor p δ θ *
      (p/2 + (p-q p)*(1+q p)/2*sinePower (q p) θ -
        negativeDrift p*sinePower (q p-2) θ + σ*(1+sinePower (q p) θ)) ≤
    (driftAllowance p * driftThreshold p ^ (-p))*δ -
      (negativeDrift p/2)*damping p δ θ := by
  let f := angularFactor p δ θ
  let S := sinePower (q p-2) θ
  let A := driftAllowance p
  let k := negativeDrift p
  let h := driftThreshold p
  have hf : 0 < f := angularFactor_pos hδ hθ
  have hA : 0 < A := driftAllowance_pos hp
  have hk : 0 < k := negativeDrift_pos hp
  have hh : 0 < h := driftThreshold_pos hp
  have hbr := regularized_bracket_le hp hσ hθ.le (Real.sin_le_one θ)
  have hstart := mul_le_mul_of_nonneg_left hbr (div_pos hδ hf).le
  change δ/f * _ ≤ A*h^(-p)*δ - (k/2)*(δ/f*S)
  apply hstart.trans
  change δ/f * (A-k*S) ≤ A*h^(-p)*δ - (k/2)*(δ/f*S)
  by_cases hsmall : Real.sin θ ≤ h
  · have hS : h^(q p-2) ≤ S :=
      Real.rpow_le_rpow_of_nonpos hθ hsmall (by linarith [q_lt_one (p := p)])
    have hcancel : A ≤ k/2*S := by
      have he := driftThreshold_identity hp
      change k*h^(q p-2) = 2*A at he
      nlinarith [mul_le_mul_of_nonneg_left hS hk.le]
    have hnonneg : 0 ≤ A*h^(-p)*δ := by positivity
    have hneg := mul_nonpos_of_nonneg_of_nonpos (div_pos hδ hf).le
      (sub_nonpos.mpr hcancel)
    nlinarith
  · have hsp : h^p ≤ Real.sin θ ^ p :=
      Real.rpow_le_rpow hh.le (le_of_not_ge hsmall) hp.le
    have hsf : Real.sin θ ^ p ≤ f := by
      dsimp [f, angularFactor, sinePower]
      exact le_add_of_nonneg_right (by positivity)
    have hhpow : 0 < h^p := Real.rpow_pos_of_pos hh _
    have hquot : δ/f ≤ δ/(h^p) := div_le_div_of_nonneg_left hδ.le hhpow (hsp.trans hsf)
    have hmain := mul_le_mul_of_nonneg_left hquot hA.le
    have hS0 : 0 ≤ S := Real.rpow_nonneg hθ.le _
    have hnonneg : 0 ≤ (k/2)*(δ/f*S) := mul_nonneg (by positivity)
      (mul_nonneg (div_pos hδ hf).le hS0)
    rw [Real.rpow_neg hh.le]
    change A*(δ/f) ≤ A*(δ*(h^p)⁻¹) at hmain
    nlinarith

end SLEExactGauge.Multipoint

end

end OAI
