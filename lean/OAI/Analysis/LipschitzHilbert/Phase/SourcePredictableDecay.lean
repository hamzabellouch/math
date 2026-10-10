import OAI.Analysis.LipschitzHilbert.Trees.SourceMotionBudget
import OAI.Analysis.LipschitzHilbert.Trees.SourceAveraging

namespace OAI

/-! Explicit polynomial bounds for the source predictable-motion
coefficient, before its dyadic gain is absorbed. -/

noncomputable section
namespace LipschitzHilbert

theorem source_blockCount_le_square {L : ℝ} (hL : 5 ≤ L) :
    (SourceParameters.blockCount L : ℝ) ≤ L^2 := by
  have hL0 : 0 ≤ L := by linarith
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hlog : Real.log L ≤ 2*Real.sqrt L := by
    have hb := Real.log_le_rpow_div hL0 (by norm_num : (0:ℝ)<1/2)
    rw [← Real.sqrt_eq_rpow] at hb
    linarith
  have hsq : Real.log L^2 ≤ 4*L := by
    have ht := pow_le_pow_left₀ hlog0 hlog 2
    have hr := Real.sq_sqrt hL0
    nlinarith
  have hceil : (SourceParameters.blockCount L : ℝ) ≤ Real.log L^2+1 :=
    (Nat.ceil_lt_add_one (sq_nonneg (Real.log L))).le
  exact hceil.trans (by nlinarith)

theorem source_amplitude_log_factor {L S a Z C : ℝ} {K : ℕ}
    (hL : 1 ≤ L) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hZ0 : 0 ≤ Z) (hZ : Z ≤ 2*L^2)
    (hK : (K:ℝ) ≤ L^2) (hS : Real.log (max 1 S) ≤ 3*L) :
    C^4*(1+(a+Z*K)*(Real.log (max 1 S)+1))^2 ≤ (169*C^4)*L^10 := by
  have hL0 : 0 ≤ L := by linarith
  have hL4 : 1 ≤ L^4 := one_le_pow₀ hL
  have hL5 : 1 ≤ L^5 := one_le_pow₀ hL
  have hlog0 : 0 ≤ Real.log (max 1 S) := Real.log_nonneg (le_max_left _ _)
  have hzk : Z*(K:ℝ) ≤ (2*L^2)*L^2 := mul_le_mul hZ hK (Nat.cast_nonneg _) (by positivity)
  have haq : a+Z*K ≤ 3*L^4 := by nlinarith
  have hlog : Real.log (max 1 S)+1 ≤ 4*L := by linarith
  have hproduct := mul_le_mul haq hlog (by positivity : 0 ≤ Real.log (max 1 S)+1)
    (by positivity : 0 ≤ 3*L^4)
  have hfactor : 1+(a+Z*K)*(Real.log (max 1 S)+1) ≤ 13*L^5 := by
    nlinarith
  have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ 1+(a+Z*K)*(Real.log (max 1 S)+1))
    hfactor 2
  calc
    _ ≤ C^4*(13*L^5)^2 := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = _ := by ring

theorem source_packet_polynomial {L A p q maskExponent Cfreq D : ℝ}
    (hL : 1 ≤ L) (hA0 : 0 ≤ A) (hA : A ≤ L^q) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hmask : 0 ≤ maskExponent) (hCfreq : 0 ≤ Cfreq) :
    L^(2*p+4)*Real.exp (16*D)+A+(4*(⌈L⌉₊:ℝ)/L^maskExponent)*A+Cfreq*A ≤
      (Real.exp (16*D)+9+Cfreq)*L^(2*p+q+6) := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hr (r s : ℝ) (hrs : r ≤ s) : L^r ≤ L^s :=
    Real.rpow_le_rpow_of_exponent_le hL hrs
  have hlarge : 0 ≤ L^(2*p+q+6) := Real.rpow_nonneg hL0.le _
  have hfirst := mul_le_mul_of_nonneg_right
    (hr (2*p+4) (2*p+q+6) (by linarith)) (Real.exp_pos (16*D)).le
  have hplain : A ≤ L^(2*p+q+6) := hA.trans (hr q _ (by linarith))
  have hden : 1 ≤ L^maskExponent := Real.one_le_rpow hL hmask
  have hceil : (⌈L⌉₊:ℝ) ≤ 2*L := by
    have := (Nat.ceil_lt_add_one hL0.le).le
    linarith
  have hmaskfactor : 4*(⌈L⌉₊:ℝ)/L^maskExponent ≤ 8*L := by
    calc
      _ ≤ 4*(⌈L⌉₊:ℝ) := div_le_self (by positivity) hden
      _ ≤ _ := by linarith
  have hmasked : (4*(⌈L⌉₊:ℝ)/L^maskExponent)*A ≤ 8*L^(2*p+q+6) := by
    calc
      _ ≤ (8*L)*L^q := mul_le_mul hmaskfactor hA hA0 (by positivity)
      _ = 8*L^(q+1) := by rw [Real.rpow_add hL0, Real.rpow_one]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hr (q+1) _ (by linarith)) (by norm_num)
  have hlast := mul_le_mul_of_nonneg_left hplain hCfreq
  nlinarith

theorem source_predictable_polynomial_bound {L A p q maskExponent Cfreq D Kw G S a Z C : ℝ}
    {K : ℕ} (hL : 1 ≤ L) (hA0 : 0 ≤ A) (hA : A ≤ L^q)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hmask : 0 ≤ maskExponent) (hCfreq : 0 ≤ Cfreq)
    (hD : 0 ≤ D) (hKw : 1 ≤ Kw) (hG : 1 ≤ G) (hsmall : (5*D/Kw)/Real.sqrt G ≤ 1/2)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hZ0 : 0 ≤ Z) (hZ : Z ≤ 2*L^2)
    (hK : (K:ℝ) ≤ L^2) (hS : Real.log (max 1 S) ≤ 3*L) (hC : 1 ≤ C) :
    let J := L^(2*p+4)*Real.exp (16*D)+A+(4*(⌈L⌉₊:ℝ)/L^maskExponent)*A+Cfreq*A
    let δ := (5*D/Kw)/Real.sqrt G
    let d := Real.exp (a*δ)*(δ+(Real.exp (2*δ)-1))
    let V := C^4*(1+(a+Z*K)*(Real.log (max 1 S)+1))^2
    let W := 5*D*(Real.exp 1*(1+2*Real.exp 1))
    V*((1+d)*(J/Real.sqrt G)+d*A)*C^3 ≤
      ((169*C^7)*((1+W)*(Real.exp (16*D)+9+Cfreq)+W))*L^(2*p+q+16)/Real.sqrt G := by
  dsimp only
  let J := L^(2*p+4)*Real.exp (16*D)+A+(4*(⌈L⌉₊:ℝ)/L^maskExponent)*A+Cfreq*A
  let δ := (5*D/Kw)/Real.sqrt G
  let d := Real.exp (a*δ)*(δ+(Real.exp (2*δ)-1))
  let V := C^4*(1+(a+Z*K)*(Real.log (max 1 S)+1))^2
  let W := 5*D*(Real.exp 1*(1+2*Real.exp 1))
  let CJ := Real.exp (16*D)+9+Cfreq
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hKw0 : 0 < Kw := zero_lt_one.trans_le hKw
  have hG0 : 0 < G := zero_lt_one.trans_le hG
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hd : d ≤ W/Real.sqrt G := by
    calc
      _ ≤ (Real.exp 1*(1+2*Real.exp 1))*δ := source_moving_weight_factor_le ha1 hδ hsmall
      _ ≤ (Real.exp 1*(1+2*Real.exp 1))*((5*D)/Real.sqrt G) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (div_le_self (by positivity) hKw) (Real.sqrt_nonneg _))
          (by positivity)
      _ = _ := by dsimp [W]; ring
  have hVbound : V ≤ (169*C^4)*L^10 := source_amplitude_log_factor hL ha0 ha1 hZ0 hZ hK hS
  have hJbound : J ≤ CJ*L^(2*p+q+6) := source_packet_polynomial hL hA0 hA hp hq hmask hCfreq
  have hAbound : A ≤ L^(2*p+q+6) := hA.trans
    (Real.rpow_le_rpow_of_exponent_le hL (by linarith))
  have hinner : (1+W)*J+W*A ≤ ((1+W)*CJ+W)*L^(2*p+q+6) := by
    calc
      _ ≤ (1+W)*(CJ*L^(2*p+q+6))+W*L^(2*p+q+6) :=
        add_le_add (mul_le_mul_of_nonneg_left hJbound (by positivity))
          (mul_le_mul_of_nonneg_left hAbound hW)
      _ = _ := by ring
  have hmotion := source_predictable_coefficient_le hV hA0
    (show 0 ≤ J/Real.sqrt G by positivity) hW hG hd (le_refl (J/Real.sqrt G))
  calc
    _ ≤ ((V*((1+W)*J+W*A))/Real.sqrt G)*C^3 :=
      mul_le_mul_of_nonneg_right hmotion (by positivity)
    _ ≤ ((((169*C^4)*L^10)*(((1+W)*CJ+W)*L^(2*p+q+6)))/Real.sqrt G)*C^3 :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right
          (mul_le_mul hVbound hinner (by positivity) (by positivity))
          (Real.sqrt_nonneg _)) (by positivity)
    _ = (((169*C^7)*((1+W)*CJ+W))*(L^10*L^(2*p+q+6)))/Real.sqrt G := by ring
    _ = _ := by
      rw [← Real.rpow_natCast L 10, ← Real.rpow_add hL0]
      congr 2
      congr 1
      norm_num
      ring

/-- At the actual source step, the full predictable-motion coefficient
is at most `G^(-1/4)`, uniformly in the allowed phase and mass parameters. -/
theorem eventually_source_predictable_coefficient (p q D C Cfreq : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hD : 0 ≤ D) (hC : 1 ≤ C) (hCfreq : 0 ≤ Cfreq) :
    ∀ᶠ L : ℝ in Filter.atTop,
      ∀ (A maskExponent Kw S a Z : ℝ) (K : ℕ),
      0 ≤ A → A ≤ L^q → 0 ≤ maskExponent → 1 ≤ Kw →
      0 ≤ a → a ≤ 1 → 0 ≤ Z → Z ≤ 2*L^2 → (K:ℝ) ≤ L^2 →
      Real.log (max 1 S) ≤ 3*L →
      let G := SourceParameters.step L
      let J := L^(2*p+4)*Real.exp (16*D)+A+(4*(⌈L⌉₊:ℝ)/L^maskExponent)*A+Cfreq*A
      let δ := (5*D/Kw)/Real.sqrt G
      let d := Real.exp (a*δ)*(δ+(Real.exp (2*δ)-1))
      let V := C^4*(1+(a+Z*K)*(Real.log (max 1 S)+1))^2
      V*((1+d)*(J/Real.sqrt G)+d*A)*C^3 ≤ G^(-(1/4:ℝ)) := by
  let W := 5*D*(Real.exp 1*(1+2*Real.exp 1))
  let CP := (169*C^7)*((1+W)*(Real.exp (16*D)+9+Cfreq)+W)
  have hpoly := eventually_source_polynomial_motion CP (2*p+q+16)
  have hsqrt := (Real.tendsto_sqrt_atTop.comp source_step_tendsto_atTop).eventually_ge_atTop (10*D)
  filter_upwards [hpoly,hsqrt,Filter.eventually_ge_atTop (1:ℝ)] with L hpoly hsqrt hL
  change 10*D ≤ Real.sqrt (SourceParameters.step L) at hsqrt
  intro A maskExponent Kw S a Z K hA0 hA hmask hKw ha0 ha1 hZ0 hZ hK hS
  dsimp only
  have hG : 1 ≤ SourceParameters.step L := one_le_pow₀ (by norm_num : (1:ℝ)≤2)
  have hroot : 0 < Real.sqrt (SourceParameters.step L) :=
    Real.sqrt_pos.mpr (SourceParameters.step_pos L)
  have hsmall : (5*D/Kw)/Real.sqrt (SourceParameters.step L) ≤ 1/2 := by
    apply (div_le_iff₀ hroot).mpr
    have hb := div_le_self (show 0 ≤ 5*D by positivity) hKw
    linarith
  exact (source_predictable_polynomial_bound hL hA0 hA hp hq hmask hCfreq hD hKw
    hG hsmall ha0 ha1 hZ0 hZ hK hS hC).trans hpoly

end LipschitzHilbert

end

end OAI
