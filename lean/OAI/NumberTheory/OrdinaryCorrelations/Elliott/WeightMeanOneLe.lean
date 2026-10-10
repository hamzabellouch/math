import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.DivisorFamily
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.CardTreeVerticesLe
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Epsilon
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourceSystem
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourceCoreEquiv
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.SourceFullTraceRaw
import OAI.NumberTheory.OrdinaryCorrelations.Elliott.DeletedOut

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology
open MeasureTheory intervalIntegral
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff
open Filter Finset
open scoped BigOperators Matrix.Norms.L2Operator

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem.Sliding
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.FiniteIntegration
open OrdinaryCorrelations.Localization

lemma weightMean_one_le (S : PrimeSystem) : 1 ≤ S.weightMean := by
  unfold weightMean
  apply Finset.one_le_prod₀
  intro p hp
  exact le_add_of_nonneg_right (div_nonneg (amplitude_nonneg p) (Nat.cast_nonneg _))

lemma source_harmonic_upper : ∀ᶠ B : ℝ in atTop,
    (sourceSystem B).harmonicCore ≤ Real.log B ∧ (sourceSystem B).harmonicCenter ≤ Real.log B := by
  have hc := SourcePrimeBands.source_prime_bands.1.eventually (eventually_lt_nhds
    (by norm_num [SourcePrimeBands.eta,SourcePrimeBands.epsilon] : SourcePrimeBands.eta < 1))
  have hz := SourcePrimeBands.source_prime_bands.2.eventually (eventually_lt_nhds
    (by norm_num [SourcePrimeBands.eta,SourcePrimeBands.epsilon] : SourcePrimeBands.epsilon-SourcePrimeBands.eta < 1))
  filter_upwards [hc,hz,eventually_gt_atTop (1:ℝ)] with B hc hz hB
  have hlog := Real.log_pos hB
  rw [source_harmonicCore,source_harmonicCenter]
  exact ⟨(div_lt_one hlog).mp hc |>.le,(div_lt_one hlog).mp hz |>.le⟩

def sourceWindow (h : ℕ) (τ C₀ B : ℝ) : ℕ := ⌈2*(h:ℝ)*τ*Real.exp (C₀*B)⌉₊

lemma sourceWindow_positive (h : ℕ) (τ C₀ B : ℝ) (hh : 0 < h) (hτ : 0 < τ) :
    0 < sourceWindow h τ C₀ B := by
  apply Nat.ceil_pos.mpr
  positivity

lemma sourceWindow_span (h : ℕ) {τ C₀ B : ℝ} (hτ : 0 ≤ τ)
    (D : (sourceSystem B).DivisorFamily B τ C₀) :
    ∀ d∈D.members,2*(h*d) ≤ sourceWindow h τ C₀ B := by
  intro d hd
  have hbound : (d:ℝ) ≤ τ*Real.exp (C₀*B) :=
    (D.upper d hd).trans (mul_le_mul_of_nonneg_left D.H_upper hτ)
  have hc := Nat.le_ceil (2*(h:ℝ)*τ*Real.exp (C₀*B))
  change _ ≤ (sourceWindow h τ C₀ B:ℝ) at hc
  have hp : ((2*(h*d):ℕ):ℝ) ≤ (sourceWindow h τ C₀ B:ℝ) := by
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hbound (show 0 ≤ 2*(h:ℝ) by positivity)]
  exact_mod_cast hp

lemma exp_linear_le_floor_power (C : ℝ) : ∀ᶠ B : ℝ in atTop,
    Real.exp (C*B)  ≤  B^(eta*(⌊B⌋₊:ℝ)) := by
  have heta : 0 < eta := by norm_num [eta,epsilon]
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (2*max C 0/eta),
    eventually_ge_atTop (2:ℝ)] with B hlog hB
  have hB0 : 0 < B := by linarith
  have hf : B ≤ 2*(⌊B⌋₊:ℝ) := by linarith [Nat.lt_floor_add_one B]
  have hl : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
  have hc := (div_le_iff₀ heta).mp hlog
  rw [Real.rpow_def_of_pos hB0]
  apply Real.exp_le_exp.mpr
  have hcB := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg ⌊B⌋₊)
  have hff := mul_le_mul_of_nonneg_left hf (le_max_right C 0)
  nlinarith [mul_le_mul_of_nonneg_right (le_max_left C 0) hB0.le]

lemma source_window_growth (h : ℕ) (τ C₀ : ℝ) (hτ : 0 ≤ τ) (hC : 0 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop,
      (sourceWindow h τ C₀ B:ℝ)*Real.exp ((A^2+2*A)*(sourceSystem B).harmonicCore+
        3*(sourceSystem B).harmonicCenter)  ≤  B^(eta*(⌊B⌋₊:ℝ)) := by
  let K : ℝ := A^2+2*A+3
  let C : ℝ := 2*(h:ℝ)*τ+1+C₀+K
  have hK : 0 ≤ K := by dsimp [K]; unfold A; positivity
  have hp : 0 ≤ 2*(h:ℝ)*τ+1 := by positivity
  filter_upwards [source_harmonic_upper,exp_linear_le_floor_power C,
    eventually_ge_atTop (1:ℝ)] with B hmass hex hB
  have hlog := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hB)
  have hmass' : (A^2+2*A)*(sourceSystem B).harmonicCore+3*(sourceSystem B).harmonicCenter ≤ K*B := by
    have hc := mul_le_mul_of_nonneg_left hmass.1 (show 0 ≤ A^2+2*A by unfold A; positivity)
    have hz := mul_le_mul_of_nonneg_left hmass.2 (by norm_num : (0:ℝ) ≤ 3)
    dsimp [K] at *
    nlinarith
  have hw : (sourceWindow h τ C₀ B:ℝ) ≤ (2*(h:ℝ)*τ+1)*Real.exp (C₀*B) := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ 2*(h:ℝ)*τ*Real.exp (C₀*B) by positivity)
    have he : 1 ≤ Real.exp (C₀*B) := Real.one_le_exp (mul_nonneg hC (zero_le_one.trans hB))
    change (sourceWindow h τ C₀ B:ℝ) < _ at hc
    nlinarith
  have heC : 2*(h:ℝ)*τ+1 ≤ Real.exp ((2*(h:ℝ)*τ+1)*B) := by
    have := Real.add_one_le_exp ((2*(h:ℝ)*τ+1)*B)
    have := mul_le_mul_of_nonneg_left hB hp
    linarith
  calc
    _  ≤  ((2*(h:ℝ)*τ+1)*Real.exp (C₀*B))*Real.exp (K*B) :=
      mul_le_mul hw (Real.exp_le_exp.mpr hmass') (Real.exp_pos _).le (by positivity)
    _  ≤  (Real.exp ((2*(h:ℝ)*τ+1)*B)*Real.exp (C₀*B))*Real.exp (K*B) := by
      gcongr
    _ = Real.exp (C*B) := by rw [←Real.exp_add,←Real.exp_add]; congr 1; dsimp [C]; ring
    _  ≤  _ := hex

lemma source_deletion_small (h : ℕ) (τ C₀ : ℝ) (hC : 0 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop, ∀ D : (sourceSystem B).DivisorFamily B τ C₀,
      2*Real.exp (theta*(sourceSystem B).harmonicCenter)*deletedWeightMean D h (pathLength B)  ≤  B^(-2:ℝ) := by
  let K : ℝ := 2*theta+(A^2+2*A)+3+4
  have hK : 0 < K := by dsimp [K]; norm_num [theta_value]; unfold A; positivity
  have hc : (0:ℝ) < 1-epsilon := by norm_num [epsilon]
  have hlim := (isLittleO_log_rpow_atTop hc).tendsto_div_nhds_zero
  have hsmall := (hlim.const_mul K).eventually (eventually_le_nhds (by norm_num : K*0 < (1/4:ℝ)))
  have hpow := (tendsto_rpow_atTop hc).eventually_ge_atTop (4*Real.log 4)
  filter_upwards [source_deleted_weight h τ C₀ (1/2) hC (by norm_num),
    source_harmonic_upper,hsmall,hpow,eventually_ge_atTop (1:ℝ)] with B hD hmass hsmall hpow hB
  intro D
  have hB0 := zero_lt_one.trans_le hB
  have hpr := Real.rpow_pos_of_pos hB0 (1-epsilon)
  have hs : K*Real.log B ≤ (1/4)*B^(1-epsilon) := by
    apply (div_le_iff₀ hpr).mp
    simpa only [mul_zero,mul_div_assoc] using hsmall
  have hlog : Real.log 4+(2*theta*(sourceSystem B).harmonicCenter+
      ((A^2+2*A)*(sourceSystem B).harmonicCore+3*(sourceSystem B).harmonicCenter))-
      (1/2)*B^(1-epsilon)  ≤  (-4)*Real.log B := by
    have hz := mul_le_mul_of_nonneg_left hmass.2 (show 0 ≤ 2*theta+3 by norm_num [theta_value])
    have hc := mul_le_mul_of_nonneg_left hmass.1 (show 0 ≤ A^2+2*A by unfold A; positivity)
    dsimp [K] at hs
    nlinarith
  have hb : (2*Real.exp (theta*(sourceSystem B).harmonicCenter)*
        (Real.sqrt (Real.exp ((A^2+2*A)*(sourceSystem B).harmonicCore+3*(sourceSystem B).harmonicCenter))*
          Real.sqrt ((sourceMinPrime B)^(-1+(1/2:ℝ)))))^2  ≤  (B^(-2:ℝ))^2 := by
    have he : (2:ℝ)^2 = Real.exp (Real.log 4) := by rw [Real.exp_log (by norm_num)]; norm_num
    have hr : (B^(-2:ℝ))^2 = Real.exp ((-4)*Real.log B) := by
      rw [Real.rpow_def_of_pos hB0,←Real.exp_nat_mul]
      congr 1
      norm_num
      ring
    simp only [mul_pow,sourceMinPrime,←Real.exp_mul,
      Real.sq_sqrt (Real.exp_pos _).le,←Real.exp_nat_mul]
    rw [he,←Real.exp_add,←Real.exp_add,←Real.exp_add,hr]
    apply Real.exp_le_exp.mpr
    convert hlog using 1; norm_num; ring
  have hb' : 2*Real.exp (theta*(sourceSystem B).harmonicCenter)*
        (Real.sqrt (Real.exp ((A^2+2*A)*(sourceSystem B).harmonicCore+3*(sourceSystem B).harmonicCenter))*
          Real.sqrt ((sourceMinPrime B)^(-1+(1/2:ℝ))))  ≤  B^(-2:ℝ) := by
    exact (sq_le_sq₀ (by positivity) (Real.rpow_nonneg hB0.le _)).mp hb
  exact (mul_le_mul_of_nonneg_left (hD D) (by positivity)).trans hb'

lemma moment_reserve {B E Q : ℝ} {D₀ m : ℕ}
    (hB : 0 < B) (hE : 0 ≤ E) (hD : 0 < D₀)
    (hQ : Q ≤ B^(-(1+eta)*(2*(m:ℝ))))
    (hgrowth : (D₀:ℝ)*E ≤ B^(eta*(m:ℝ))) :
    Real.sqrt ((D₀:ℝ)^3*Q*E) ≤
      (D₀:ℝ)*(B^(-1-eta/2:ℝ))^m := by
  have hp : (0:ℝ) ≤ B^(-(1+eta)*(2*(m:ℝ))) := (Real.rpow_pos_of_pos hB _).le
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ = (D₀:ℝ)^2*(Q*((D₀:ℝ)*E)) := by ring
    _ ≤ (D₀:ℝ)^2*(B^(-(1+eta)*(2*(m:ℝ)))*B^(eta*(m:ℝ))) := by
      gcongr
    _ = _ := by
      rw [←Real.rpow_add hB,mul_pow,←pow_mul,←Real.rpow_mul_natCast hB.le]
      congr 1
      congr 1
      push_cast
      ring

theorem source_divisorForm_bound (h : ℕ) (hh : 0 < h) (τ T C₀ : ℝ)
    (hτ : 1 ≤ τ) (hτ2 : τ < 2) (hC : 0 ≤ C₀) :
    ∀ᶠ B : ℝ in atTop, ∀ (D : (sourceSystem B).DivisorFamily B τ C₀)
      (cut : (sourceSystem B).Cutoffs T) (a : ℕ→ℂ),
      (∀ d∈D.members, ‖a d‖ ≤ 1) → ∀ F G : ℤ→ℂ,
      (∀ n, ‖F n‖ ≤ 1) → (∀ n, ‖G n‖ ≤ 1) → ∀ δ : ℝ, 0 < δ →
    ∀ᶠ X : ℝ in atTop,
      ‖divisorForm D h cut a F G X‖/X ≤
        5*B^(-1-eta/2:ℝ)*(sourceSystem B).weightMean+δ := by
  filter_upwards [NumericalLine.source_high_trace h hh τ T C₀ hτ hτ2 hC,
    source_window_growth h τ C₀ (by linarith) hC,
    source_deletion_small h τ C₀ hC,eventually_ge_atTop (2:ℝ)] with B htrace hgrowth hdel hB
  intro D cut a ha F G hF hG δ hδ
  let D₀ := sourceWindow h τ C₀ B
  let m := ⌊B⌋₊
  let t : ℝ := B^(-1-eta/2:ℝ)
  have hB0 : 0 < B := by linarith
  have hD : 0 < D₀ := sourceWindow_positive h τ C₀ B hh (by linarith)
  have hm : 0 < m := Nat.floor_pos.mpr (by linarith)
  have ht : 0 < t := Real.rpow_pos_of_pos hB0 _
  have htr : NumericalLine.fullTraceSum D h (2*m) (pathLength B) cut ≤
      B^(-(1+eta)*(2*(m:ℝ))) := by
    simpa only [sourceLength,Nat.cast_mul,Nat.cast_ofNat] using htrace D cut
  have hr := moment_reserve hB0 (Real.exp_pos _).le hD htr hgrowth
  have hroot : 2*Real.sqrt ((D₀:ℝ)^3*NumericalLine.fullTraceSum D h (2*m) (pathLength B) cut*
        Real.exp ((A^2+2*A)*(sourceSystem B).harmonicCore+3*(sourceSystem B).harmonicCenter))/
      ((D₀:ℝ)*t^(m-1)) ≤ 2*t := by
    apply (div_le_iff₀ (mul_pos (Nat.cast_pos.mpr hD) (pow_pos ht _))).mpr
    calc
      _ ≤ 2*((D₀:ℝ)*t^m) := mul_le_mul_of_nonneg_left hr (by norm_num)
      _ = _ := by
        rw [show t^m=t^(m-1)*t by
          conv_lhs => rw [show m=(m-1)+1 by omega,pow_succ]]
        ring
  have hd : 2*Real.exp (theta*(sourceSystem B).harmonicCenter)*deletedWeightMean D h (pathLength B) ≤ t := by
    apply (hdel D).trans
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    norm_num [eta,epsilon]
  have hwt := weightMean_one_le (sourceSystem B)
  filter_upwards [divisorForm_eventual D hh (pathLength B) D₀ m hD hm
    (sourceWindow_span h (by linarith) D) cut a ha F G hF hG t ht δ hδ] with X hX
  dsimp [t] at hX hroot hd
  nlinarith [mul_le_mul_of_nonneg_left hwt ht.le]

end OrdinaryCorrelations.GraphKernel.PrimeSystem.Sliding

end

end OAI
