import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.CompleteIsComplete
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.DerivativeConstant
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Twist
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.BandPowerLower
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.InverseBandBound
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.LogarithmicDeltaTendsto

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

namespace OrdinaryCorrelations.PretentiousEuler
open MeasureTheory Set Completion OrdinaryHorizontalHalasz OrdinaryDirichletMeanSquare

theorem moving_square_compact_weighted_small {f : ℕ → ℂ} (hf : OneBounded f)
    (hNP : UniformlyNonpretentious f) (T ζ : ℝ) (hζ : 0<ζ) :
    ∀ᶠ N : ℕ in atTop, ∀τ : ℝ, |τ|≤(N:ℝ)^2/2 →
      (Real.log (N:ℝ))⁻¹*(∫t in Icc (-T) T, gaussian t*
        ‖deriv (LSeries (OrdinaryArchimedeanTwist.twist (complete f) τ))
          (line ((Real.log (N:ℝ))⁻¹) t)‖)≤ζ := by
  let C := energyConstant
  have hC : 0≤C := energyConstant_nonneg
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
    (eventual_band_saving hf hNP (show 0≤2*A by positivity) hε)
  filter_upwards [eventually_ge_atTop M₀,
    hlimδ.eventually (eventually_lt_nhds (show 0<ζ/3 by positivity)),
    logarithmic_delta_tendsto.eventually (eventually_lt_nhds zero_lt_one),
    eventually_ge_atTop (2:ℕ),eventually_ge_atTop ⌈2*T⌉₊] with N hNM hsmall hd1 hN2 hNT
  intro τ hτ
  let δ := (Real.log (N:ℝ))⁻¹
  have hl : 0<Real.log N := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hδ : 0<δ := inv_pos.mpr hl
  have hδ1 : δ≤1 := hd1.le
  have hN1r : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hNN : N≤N*N := by nlinarith
  have hT : 2*T≤(N:ℝ) := le_trans (Nat.le_ceil (2*T)) (by exact_mod_cast hNT)
  have hTN : 2*T≤(N:ℝ)^2 := by nlinarith
  have hband := hband₀ (N*N) (hNM.trans hNN)
  have hlog : Real.log ((N*N:ℕ):ℝ)=2*Real.log N := by
    rw [Nat.cast_mul,Real.log_mul (by positivity : (N:ℝ)≠0) (by positivity : (N:ℝ)≠0)]
    ring
  let g := OrdinaryArchimedeanTwist.twist (complete f) τ
  have hg (n : ℕ) : ‖g n‖≤1 := by
    simpa only [g,OrdinaryArchimedeanTwist.norm_twist] using complete_oneBounded hf n
  have hgm : OrdinaryLogDerivative.Complete g := fun m n hm hn =>
    OrdinaryArchimedeanTwist.twist_mul (complete f) τ (complete_isComplete f) hm hn
  have hb (u : ℝ) (hδu : δ≤u) (hu1 : u≤δ+1) (huA : u≤A*δ)
      (t : ℝ) (ht : t∈Icc (-T) T) : ‖LSeries g (line u t)‖≤ε/u := by
    have hu : 0<u := hδ.trans_le hδu
    have htN : |-(t+τ)|≤((N*N:ℕ):ℝ) := by
      push_cast
      rw [abs_neg]
      have hh := abs_add_le t τ
      have htT := abs_le.mpr ht
      linarith
    have huN : u≤(2*A)/Real.log ((N*N:ℕ):ℝ) := by
      rw [hlog]
      have hratio : (2*A)/(2*Real.log N)=A*δ := by dsimp [δ]; field_simp
      rw [hratio]
      exact huA
    have harg : line u t-(τ:ℂ)*Complex.I = ((1+u:ℝ):ℂ)+((-(t+τ):ℝ):ℂ)*Complex.I := by
      simp only [line, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_neg]
      ring
    rw [show g = OrdinaryArchimedeanTwist.twist (complete f) τ from rfl,
      OrdinaryArchimedeanTwist.lseries_twist, harg]
    exact hband u hu (by linarith) huN (-(t+τ)) htN
  have hh := band_derivative_bound hg hgm hA hδ hδ1 hε.le (-T) T hb
  change δ*(∫t in Icc (-T) T, gaussian t*‖deriv (LSeries g) (line δ t)‖)≤ζ
  change δ*(∫t in Icc (-T) T, gaussian t*‖deriv (LSeries g) (line δ t)‖)≤
    10*C*ε+60*C*A^(-(1/4:ℝ))+K*Real.sqrt δ at hh
  exact hh.trans (by linarith)

end OrdinaryCorrelations.PretentiousEuler

end

end OAI
