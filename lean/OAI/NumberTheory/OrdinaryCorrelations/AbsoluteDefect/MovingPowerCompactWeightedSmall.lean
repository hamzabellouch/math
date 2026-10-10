import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrincipalDivergence

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter

namespace OrdinaryCorrelations.UniformFamilyHalasz
open MeasureTheory Set Completion OrdinaryHorizontalHalasz OrdinaryDirichletMeanSquare
open PretentiousEuler Filter

theorem moving_power_compact_weighted_small {ι : Type*} {F : ι → ℕ → ℂ} (hf : ∀i, OneBounded (F i))
    (hD : PrincipalDivergence F) (k : ℕ) (hk : 1 ≤ k) (T ζ : ℝ) (hζ : 0<ζ) :
    ∀ᶠ N : ℕ in atTop, ∀i, ∀τ : ℝ, |τ|≤(N:ℝ)^k/2 →
      (Real.log (N:ℝ))⁻¹*(∫t in Icc (-T) T, gaussian t*
        ‖deriv (LSeries (OrdinaryArchimedeanTwist.twist (complete (F i)) τ))
          (line ((Real.log (N:ℝ))⁻¹) t)‖)≤ζ := by
  let C := energyConstant
  have hC : 0≤C := PretentiousEuler.energyConstant_nonneg
  let ε := ζ/(30*(C+1))
  have hε : 0<ε := by dsimp [ε]; positivity
  have he : 10*C*ε≤ζ/3 := by
    have hid := div_mul_cancel₀ ζ (ne_of_gt (show 0<30*(C+1) by positivity))
    change ε*(30*(C+1))=ζ at hid
    nlinarith [hε.le]
  have hlimA : Tendsto (fun A : ℝ => 60*C*A^(-(1/4:ℝ))) atTop (nhds 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)).const_mul (60*C)
  obtain ⟨A,hAs,hAge⟩ := ((hlimA.eventually (eventually_lt_nhds (show 0<ζ/3 by positivity))).and
    (eventually_ge_atTop (1:ℝ))).exists
  have hA : 0<A := lt_of_lt_of_le zero_lt_one hAge
  let K := 2*Real.sqrt (∫t : ℝ, gaussian t)*Real.sqrt (5*C)
  have hlimδ : Tendsto (fun N : ℕ => K*Real.sqrt ((Real.log (N:ℝ))⁻¹)) atTop (nhds 0) := by
    simpa using logarithmic_delta_tendsto.sqrt.const_mul K
  obtain ⟨M₀,hband₀⟩ := eventually_atTop.1
    (eventual_band_saving hf hD (show 0≤(k:ℝ)*A by positivity) hε)
  filter_upwards [eventually_ge_atTop M₀,
    hlimδ.eventually (eventually_lt_nhds (show 0<ζ/3 by positivity)),
    logarithmic_delta_tendsto.eventually (eventually_lt_nhds zero_lt_one),
    eventually_ge_atTop (2:ℕ),eventually_ge_atTop ⌈2*T⌉₊] with N hNM hsmall hd1 hN2 hNT
  intro i τ hτ
  let δ := (Real.log (N:ℝ))⁻¹
  have hl : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hδ : 0<δ := inv_pos.mpr hl
  have hδ1 : δ≤1 := hd1.le
  have hN1r : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hNN : N≤N^k := Nat.le_self_pow (by omega) N
  have hT : 2*T≤(N:ℝ) := le_trans (Nat.le_ceil (2*T)) (by exact_mod_cast hNT)
  have hTN : 2*T≤(N:ℝ)^k := hT.trans (by exact_mod_cast hNN)
  have hband := hband₀ (N^k) (hNM.trans hNN)
  have hkr : (k:ℝ)≠0 := by exact_mod_cast (show k≠0 by omega)
  have hlog : Real.log ((N^k:ℕ):ℝ)=(k:ℝ)*Real.log N := by
    rw [Nat.cast_pow, Real.log_pow]
  let g := OrdinaryArchimedeanTwist.twist (complete (F i)) τ
  have hg (n : ℕ) : ‖g n‖≤1 := by
    simpa only [g,OrdinaryArchimedeanTwist.norm_twist] using complete_oneBounded (hf i) n
  have hgm : OrdinaryLogDerivative.Complete g := fun m n hm hn =>
    OrdinaryArchimedeanTwist.twist_mul (complete (F i)) τ (complete_isComplete (F i)) hm hn
  have hb (u : ℝ) (hδu : δ≤u) (hu1 : u≤δ+1) (huA : u≤A*δ)
      (t : ℝ) (ht : t∈Icc (-T) T) : ‖LSeries g (line u t)‖≤ε/u := by
    have hu : 0<u := hδ.trans_le hδu
    have htN : |-(t+τ)|≤((N^k:ℕ):ℝ) := by
      push_cast
      rw [abs_neg]
      have hh := abs_add_le t τ
      have htT := abs_le.mpr ht
      linarith
    have huN : u≤((k:ℝ)*A)/Real.log ((N^k:ℕ):ℝ) := by
      rw [hlog]
      have hratio : ((k:ℝ)*A)/((k:ℝ)*Real.log N)=A*δ := by dsimp [δ]; field_simp
      rw [hratio]
      exact huA
    have harg : line u t-(τ:ℂ)*Complex.I = ((1+u:ℝ):ℂ)+((-(t+τ):ℝ):ℂ)*Complex.I := by
      simp only [line, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_neg]
      ring
    rw [show g = OrdinaryArchimedeanTwist.twist (complete (F i)) τ from rfl,
      OrdinaryArchimedeanTwist.lseries_twist, harg]
    exact hband i u hu (by linarith) huN (-(t+τ)) htN
  have hh := band_derivative_bound hg hgm hA hδ hδ1 hε.le (-T) T hb
  change δ*(∫t in Icc (-T) T, gaussian t*‖deriv (LSeries g) (line δ t)‖)≤ζ
  change δ*(∫t in Icc (-T) T, gaussian t*‖deriv (LSeries g) (line δ t)‖)≤
    10*C*ε+60*C*A^(-(1/4:ℝ))+K*Real.sqrt δ at hh
  exact hh.trans (by linarith)

open MeasureTheory Set Completion OrdinaryHorizontalHalasz OrdinaryDirichletMeanSquare

lemma moving_power_compact_unweighted_small {ι : Type*} {F : ι → ℕ → ℂ} (hf : ∀i, OneBounded (F i))
    (hD : PrincipalDivergence F) (k : ℕ) (hk : 1 ≤ k) (T ζ : ℝ) (hζ : 0<ζ) :
    ∀ᶠ N : ℕ in atTop, ∀i, ∀τ : ℝ, |τ|≤(N:ℝ)^k/2 →
      (∫t in Icc (-T) T, (Real.log (N:ℝ))⁻¹*
        ‖deriv (LSeries (OrdinaryArchimedeanTwist.twist (complete (F i)) τ))
          (line ((Real.log (N:ℝ))⁻¹) t)‖)≤ζ := by
  filter_upwards [moving_power_compact_weighted_small hf hD k hk T (ζ/Real.exp (T^2))
    (by positivity), eventually_ge_atTop (2:ℕ)] with N hsmall hN
  intro i τ hτ
  let δ := (Real.log (N:ℝ))⁻¹
  let g := OrdinaryArchimedeanTwist.twist (complete (F i)) τ
  have hδ : 0<δ := inv_pos.mpr (Real.log_pos (by exact_mod_cast (show 1<N by omega)))
  have hg (n : ℕ) : ‖g n‖≤1 := by
    simpa only [g,OrdinaryArchimedeanTwist.norm_twist] using complete_oneBounded (hf i) n
  have hc := continuous_derivative_vertical hg hδ
  have hi : IntegrableOn (fun t : ℝ => δ*‖deriv (LSeries g) (line δ t)‖) (Icc (-T) T) :=
    (hc.norm.const_mul δ).continuousOn.integrableOn_Icc
  have hwi : IntegrableOn (fun t : ℝ => gaussian t*‖deriv (LSeries g) (line δ t)‖) (Icc (-T) T) :=
    (derivative_gaussian_integrable hg hδ).integrableOn
  have hb (t : ℝ) (ht : t∈Icc (-T) T) : 1≤Real.exp (T^2)*gaussian t := by
    have ht2 : t^2≤T^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (show 0≤T+t by linarith [ht.1])]
    calc
      1 = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (T^2+-t^2) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := Real.exp_add _ _
  have hh : (∫t in Icc (-T) T, δ*‖deriv (LSeries g) (line δ t)‖) ≤
      Real.exp (T^2)*(δ*(∫t in Icc (-T) T, gaussian t*‖deriv (LSeries g) (line δ t)‖)) := by
    rw [←MeasureTheory.integral_const_mul,←MeasureTheory.integral_const_mul]
    apply integral_mono_ae hi ((hwi.const_mul δ).const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    nlinarith [mul_le_mul_of_nonneg_right (hb t ht) (mul_nonneg hδ.le (norm_nonneg (deriv (LSeries g) (line δ t))))]
  exact hh.trans (by
    have he := mul_le_mul_of_nonneg_left (hsmall i τ hτ) (Real.exp_pos (T^2)).le
    simpa only [mul_div_cancel₀ ζ (Real.exp_ne_zero (T^2))] using he)

theorem moving_power_global_derivative_small {ι : Type*} {F : ι → ℕ → ℂ} (hf : ∀i, OneBounded (F i))
    (hD : PrincipalDivergence F) (k : ℕ) (hk : 1 ≤ k) (ζ : ℝ) (hζ : 0<ζ) :
    ∀ᶠ N : ℕ in atTop, ∀i, ∀τ : ℝ, |τ|≤(N:ℝ)^k/2 →
      (Real.log (N:ℝ))⁻¹*(∫t : ℝ, (1+t^2)⁻¹*
        ‖deriv (LSeries (OrdinaryArchimedeanTwist.twist (complete (F i)) τ))
          (line ((Real.log (N:ℝ))⁻¹) t)‖)≤ζ := by
  let K := Real.exp 1*derivativeConstant
  have hK0 : 0≤K := mul_nonneg (Real.exp_pos 1).le derivativeConstant_nonneg
  have heps : 0<ζ/(3*(K+1)) := by positivity
  have he := OrdinaryCauchyTail.tendsto_tail_integral.eventually (eventually_lt_nhds heps)
  obtain ⟨R,hR,hRi⟩ := (he.and (eventually_ge_atTop (1:ℝ))).exists
  filter_upwards [moving_power_compact_unweighted_small hf hD k hk (R+1) (ζ/2) (by positivity),
    logarithmic_delta_tendsto.eventually (eventually_lt_nhds zero_lt_one),
    eventually_ge_atTop (2:ℕ)] with N hsmall hd1 hN
  intro i τ hτ
  let δ := (Real.log (N:ℝ))⁻¹
  let b := OrdinaryArchimedeanTwist.twist (complete (F i)) τ
  let g := fun t : ℝ => δ*‖deriv (LSeries b) (line δ t)‖
  have hδ : 0<δ := inv_pos.mpr (Real.log_pos (by exact_mod_cast (show 1<N by omega)))
  have hδ1 : δ≤1 := hd1.le
  have hb (n : ℕ) : ‖b n‖≤1 := by
    simpa only [b,OrdinaryArchimedeanTwist.norm_twist] using complete_oneBounded (hf i) n
  have hbm : OrdinaryLogDerivative.Complete b := fun m n hm hn =>
    OrdinaryArchimedeanTwist.twist_mul (complete (F i)) τ (complete_isComplete (F i)) hm hn
  have hg : Continuous g := (continuous_derivative_vertical hb hδ).norm.const_mul δ
  have hg0 (t : ℝ) : 0≤g t := mul_nonneg hδ.le (norm_nonneg _)
  obtain ⟨B,hBB⟩ := derivative_vertical_bounded hb hδ
  have hB (t : ℝ) : ‖g t‖≤δ*B := by
    rw [Real.norm_of_nonneg (hg0 t)]
    exact mul_le_mul_of_nonneg_left (hBB t) hδ.le
  have hlocal (u : ℝ) : (∫t in Icc (-1:ℝ) 1, g (t+u))≤K := by
    simp only [g,MeasureTheory.integral_const_mul]
    exact shifted_derivative_bound hb hbm hδ hδ1 u
  have htail := OrdinaryCauchyTail.tail_bound hg hg0 hB hlocal R
  have htail0 : 0≤∫u : ℝ, OrdinaryCauchyTail.tailWeight R u :=
    integral_nonneg (OrdinaryCauchyTail.tail_nonneg R)
  have htail' : (∫t : ℝ, OrdinaryCauchyTail.tailWeight (R+1) t*g t)≤ζ/2 := by
    have hh := (lt_div_iff₀ (by positivity : (0:ℝ)<3*(K+1))).mp hR
    nlinarith
  have hi : IntegrableOn g (Icc (-(R+1)) (R+1)) := hg.continuousOn.integrableOn_Icc
  have hci := (OrdinaryCauchyTail.cauchy_integrable.mul_bdd hg.aestronglyMeasurable
    (Eventually.of_forall hB)).integrableOn (s:=Icc (-(R+1)) (R+1))
  have hc : (∫t in Icc (-(R+1)) (R+1), OrdinaryCauchyTail.cauchy t*g t)≤ζ/2 := by
    apply (integral_mono_ae hci hi _).trans (hsmall i τ hτ)
    exact Eventually.of_forall (fun t => by
      nlinarith [mul_le_mul_of_nonneg_right (OrdinaryCauchyTail.cauchy_le_one t) (hg0 t)])
  have hh : (∫t : ℝ, OrdinaryCauchyTail.cauchy t*g t)≤ζ := by
    rw [OrdinaryCauchyTail.tail_decomposition hg hB (R+1)]
    linarith
  simpa only [OrdinaryCauchyTail.cauchy,g,mul_left_comm _ δ,MeasureTheory.integral_const_mul] using hh

open MeasureTheory Set Completion OrdinaryRieszPerron OrdinaryHorizontalHalasz

theorem moving_power_logcutoff_small {ι : Type*} {F : ι → ℕ → ℂ} (hf : ∀i, OneBounded (F i))
    (hD : PrincipalDivergence F) (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀i, ∀τ : ℝ, |τ|≤(N:ℝ)^k/2 →
      ‖cutoffSeries (LSeries.logMul (OrdinaryArchimedeanTwist.twist (complete (F i)) τ)) (N:ℝ)‖
        ≤ε*(N:ℝ)*Real.log N := by
  let c : ℝ := 1/(2*Real.pi)*Real.exp 1
  have hc : 0<c := by dsimp [c]; positivity
  filter_upwards [moving_power_global_derivative_small hf hD k hk (ε/c) (div_pos hε hc),
    eventually_ge_atTop (2:ℕ)] with N hsmall hN
  intro i τ hτ
  let g := OrdinaryArchimedeanTwist.twist (complete (F i)) τ
  have hg (n : ℕ) : ‖g n‖≤1 := by
    simpa only [g,OrdinaryArchimedeanTwist.norm_twist] using complete_oneBounded (hf i) n
  have hX : 1<(N:ℝ) := by exact_mod_cast (show 1<N by omega)
  have hx : 0<(N:ℝ) := lt_trans zero_lt_one hX
  have hl : 0<Real.log N := Real.log_pos hX
  let δ : ℝ := (Real.log (N:ℝ))⁻¹
  have hδ : 0<δ := inv_pos.mpr hl
  have hab : LSeries.abscissaOfAbsConv (LSeries.logMul g)<((1+δ:ℝ):EReal) := by
    rw [LSeries.abscissaOfAbsConv_logMul]
    exact lt_of_le_of_lt (LSeries.abscissaOfAbsConv_le_of_le_const ⟨1,fun n _ => hg n⟩)
      (by exact_mod_cast (show (1:ℝ)<1+δ by linarith))
  have hh := cutoffSeries_norm_le (LSeries.logMul g) hx (show 1≤1+δ by linarith) hab
  rw [square_bounded_logSeries_cauchy_derivative hg hδ, rpow_one_add_inv_log hX] at hh
  have hs := hsmall i τ hτ
  have hsi : (∫t : ℝ, (1+t^2)⁻¹*‖deriv (LSeries g) (line δ t)‖) ≤ (ε/c)*Real.log N := by
    have hh' := mul_le_mul_of_nonneg_right hs hl.le
    have hid : δ*Real.log N=1 := inv_mul_cancel₀ hl.ne'
    change δ*(∫t : ℝ, (1+t^2)⁻¹*‖deriv (LSeries g) (line δ t)‖)*Real.log N≤_ at hh'
    rw [mul_right_comm δ, hid, one_mul] at hh'
    exact hh'
  calc
    ‖cutoffSeries (LSeries.logMul g) (N:ℝ)‖ ≤
        (1/(2*Real.pi))*((N:ℝ)*Real.exp 1)*(∫t : ℝ, (1+t^2)⁻¹*‖deriv (LSeries g) (line δ t)‖) := hh
    _ ≤ (1/(2*Real.pi))*((N:ℝ)*Real.exp 1)*((ε/c)*Real.log N) :=
      mul_le_mul_of_nonneg_left hsi (by positivity)
    _ = ε*(N:ℝ)*Real.log N := by
      dsimp [c]
      field_simp

theorem moving_power_cutoff_small {ι : Type*} {F : ι → ℕ → ℂ} (hf : ∀i, OneBounded (F i))
    (hD : PrincipalDivergence F) (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀i, ∀τ : ℝ, |τ|≤(N:ℝ)^k/2 →
      ‖cutoffSeries (OrdinaryArchimedeanTwist.twist (complete (F i)) τ) (N:ℝ)‖≤ε*(N:ℝ) := by
  let R : ℝ := 1+3/ε
  have hR : 1≤R := by dsimp [R]; linarith [div_pos (by norm_num : (0:ℝ)<3) hε]
  have hR0 : 0<R := lt_of_lt_of_le zero_lt_one hR
  have hdiv : 1/R≤ε/3 := by
    apply (div_le_iff₀ hR0).2
    dsimp [R]
    have hh : ε/3*(3/ε)=1 := by field_simp
    nlinarith
  have hloglim : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [moving_power_logcutoff_small hf hD k hk (ε/3) (by positivity),
    hloglim.eventually (eventually_ge_atTop (3*Real.log R/ε)),
    eventually_ge_atTop (2:ℕ)] with N hsmall hlog hN
  intro i τ hτ
  let g := OrdinaryArchimedeanTwist.twist (complete (F i)) τ
  have hg (n : ℕ) : ‖g n‖≤1 := by
    simpa only [g,OrdinaryArchimedeanTwist.norm_twist] using complete_oneBounded (hf i) n
  have hX : 1<(N:ℝ) := by exact_mod_cast (show 1<N by omega)
  have hx : 0<(N:ℝ) := lt_trans zero_lt_one hX
  have hl : 0<Real.log N := Real.log_pos hX
  have hlogR : Real.log R≤(ε/3)*Real.log N := by
    have hh := (div_le_iff₀ hε).1 hlog
    nlinarith
  have hdivX : (N:ℝ)/R≤(ε/3)*(N:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hdiv hx.le
    simpa only [one_div,div_eq_mul_inv,one_mul,mul_comm (R⁻¹) (N:ℝ)] using hh
  have hh := cutoff_norm_le_logcutoff_add g hX.le hR hg
  have hs := hsmall i τ hτ
  have herr1 := mul_le_mul_of_nonneg_right hdivX hl.le
  have herror2 := mul_le_mul_of_nonneg_left hlogR hx.le
  have htotal : Real.log N*‖cutoffSeries g (N:ℝ)‖≤Real.log N*(ε*(N:ℝ)) := by
    nlinarith
  exact (mul_le_mul_iff_right₀ hl).1 htotal

open OrdinaryRieszPerron OrdinaryTriangular Completion Filter

theorem moving_power_complete_partial_small {ι : Type*} {F : ι → ℕ → ℂ} (hf : ∀i, OneBounded (F i))
    (hD : PrincipalDivergence F) (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, ∀i, ∀τ : ℝ, |τ|≤(N:ℝ)^k/2 →
      ‖∑n∈Finset.Icc 1 N, OrdinaryArchimedeanTwist.twist (complete (F i)) τ n‖≤ε*(N:ℝ) := by
  let ρ : ℝ := min (ε/4) (1/2)
  have hρ : 0<ρ := lt_min (by positivity) (by norm_num)
  have hρε : ρ≤ε/4 := min_le_left _ _
  have hρ1 : ρ≤1/2 := min_le_right _ _
  let e : ℝ := ε*ρ/10
  have he : 0<e := by dsimp [e]; positivity
  have hte : ∀ᶠ N : ℕ in atTop, ∀i, ∀τ : ℝ, |τ|≤(N:ℝ)^k/2 →
      ‖triangle (OrdinaryArchimedeanTwist.twist (complete (F i)) τ) N‖≤e*(N:ℝ)^2 := by
    filter_upwards [moving_power_cutoff_small hf hD k hk e he, eventually_ge_atTop (1:ℕ)] with N hs hN
    intro i τ hτ
    rw [triangle_eq_cutoff _ (by omega),norm_mul,Complex.norm_natCast]
    have hh := mul_le_mul_of_nonneg_left (hs i τ hτ) (Nat.cast_nonneg N)
    nlinarith
  obtain ⟨N₀,htri⟩ := eventually_atTop.1 hte
  filter_upwards [eventually_ge_atTop N₀,eventually_ge_atTop (1:ℕ),
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (1/ρ))] with N hNM hN1 hNρ
  intro i τ hτ
  let a := OrdinaryArchimedeanTwist.twist (complete (F i)) τ
  have ha (n : ℕ) : ‖a n‖≤1 := by
    simpa only [a,OrdinaryArchimedeanTwist.norm_twist] using complete_oneBounded (hf i) n
  have hN : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hρN : 1≤ρ*(N:ℝ) := by have hh := (div_le_iff₀ hρ).1 hNρ; nlinarith
  let H : ℕ := ⌈ρ*(N:ℝ)⌉₊
  have hHlow : ρ*(N:ℝ)≤(H:ℝ) := Nat.le_ceil _
  have hHupper : (H:ℝ)≤2*ρ*(N:ℝ) := by
    have hh := Nat.ceil_lt_add_one (show 0≤ρ*(N:ℝ) by positivity)
    dsimp [H]
    linarith
  have hHpos : 0<(H:ℝ) := lt_of_lt_of_le (by positivity : 0<ρ*(N:ℝ)) hHlow
  have hHN : (H:ℝ)≤(N:ℝ) := by nlinarith [mul_le_mul_of_nonneg_right hρ1 hN.le]
  have hNadd : (N+H:ℕ)≥N := Nat.le_add_right _ _
  have hu := unsmoothing a ha N H
  have hNMadd : N₀≤N+H := hNM.trans hNadd
  have hsN := htri N hNM i τ hτ
  have hτNH : |τ|≤((N+H:ℕ):ℝ)^k/2 := by
    apply hτ.trans
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact pow_le_pow_left₀ (Nat.cast_nonneg N) (by exact_mod_cast hNadd) k
  have hsNH := htri (N+H) hNMadd i τ hτNH
  have hsq : (((N+H:ℕ):ℝ))^2≤4*(N:ℝ)^2 := by
    push_cast
    nlinarith [sq_nonneg ((N:ℝ)-(H:ℝ)),sq_nonneg (H:ℝ)]
  have hmain : ‖triangle a (N+H)‖+‖triangle a N‖≤5*e*(N:ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_left hsq he.le
    nlinarith
  have hmain' : 5*e*(N:ℝ)^2≤(ε/2)*(H:ℝ)*(N:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hHlow (show 0≤ε/2 by positivity)) hN.le
    calc
      _ = (ε/2)*(ρ*(N:ℝ))*(N:ℝ) := by dsimp only [e]; ring
      _ ≤ _ := hh
  have hHε : (H:ℝ)≤(ε/2)*(N:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hρε hN.le
    nlinarith
  have htail : (H:ℝ)^2≤(ε/2)*(H:ℝ)*(N:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hHε hHpos.le
    nlinarith
  have htotal : (H:ℝ)*‖ordinarySum a N‖≤(H:ℝ)*(ε*(N:ℝ)) := by nlinarith
  exact (mul_le_mul_iff_right₀ hHpos).1 htotal

end OrdinaryCorrelations.UniformFamilyHalasz

end

end OAI
