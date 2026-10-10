import Mathlib
import OAI.Probability.LogConcave.Numerics.VelocityWorkCoefficient

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter Quadrature MeanTree
open scoped Topology

lemma logMeshCount_rate {T : ℕ → ℝ} {b : ℝ} (hb : 0≤b)
    (hT0 : ∀ᶠ d : ℕ in atTop,0<T d) (hT1 : ∀ᶠ d : ℕ in atTop,T d<1)
    (hL : LogPowerRate (fun d => logMeshLength (T d)) 0) :
    LogPowerRate (fun d => (logMeshCount (T d) ((d:ℝ)^(-b)):ℝ)) (-b) := by
  have hr := hL.mul (LogPowerRate.inv_power b)
  simp only [zero_add] at hr
  apply LogPowerRate.of_le (hr.add ((LogPowerRate.const 1).mono (by linarith)))
  · exact Eventually.of_forall (fun _ => Nat.cast_nonneg _)
  · filter_upwards [hT0,hT1,eventually_ge_atTop (1:ℕ)] with d hd0 hd1 hd
    have hp : (0:ℝ)<d := by exact_mod_cast hd
    simpa only [div_eq_mul_inv] using (logMeshCount_bound hd0 hd1 (Real.rpow_pos_of_pos hp (-b))).le

lemma probabilityNode_card_rate {T : ℕ → ℝ} {b : ℝ} (hb : 0≤b) (n : ℕ)
    (hT0 : ∀ᶠ d : ℕ in atTop,0<T d) (hT1 : ∀ᶠ d : ℕ in atTop,T d<1)
    (hL : LogPowerRate (fun d => logMeshLength (T d)) 0) :
    LogPowerRate (fun d => (Fintype.card (ProbabilityNode (T d) ((d:ℝ)^(-b)) n):ℝ)) (-b) := by
  simpa only [probabilityNode_card,Nat.cast_mul,Nat.cast_add,Nat.cast_one] using
    (logMeshCount_rate hb hT0 hT1 hL).mul_const ((n:ℝ)+1)

theorem meanWork_rate {p : ℕ → ℕ} {b : ℝ} (hb : 0≤b)
    (hp : LogPowerRate (fun d => (p d:ℝ)) (-b)) (q m N nc Nc : ℕ) :
    LogPowerRate (fun d => (meanWork (p d) q m N nc Nc 0 0 0:ℝ)) (-((Nc*(2*N+2):ℕ):ℝ)*b) := by
  have hr := (hp.add ((LogPowerRate.const 1).mono (by linarith))).pow (Nc*(2*N+2))
  have he := hr.const_mul (((nc+1)*((nc+1)*velocityWorkCoefficient q m N)^Nc:ℕ):ℝ)
  simp only [mul_neg,neg_mul] at he ⊢
  apply LogPowerRate.of_le he
  · exact Eventually.of_forall (fun _ => Nat.cast_nonneg _)
  · apply Eventually.of_forall
    intro d
    exact_mod_cast meanWork_polynomial (p d) q m N nc Nc

lemma sampleWork_rate {p : ℕ → ℕ} {b : ℝ} (hb : 0≤b)
    (hp : LogPowerRate (fun d => (p d:ℝ)) (-b)) (N : ℕ) :
    LogPowerRate (fun d => (flowWork (p d) N 0 0:ℝ)) (-(N:ℝ)*b) := by
  have he := (hp.add ((LogPowerRate.const 1).mono (by linarith))).pow N
  simp only [mul_neg,neg_mul] at he ⊢
  apply LogPowerRate.of_le he
  · exact Eventually.of_forall (fun _ => Nat.cast_nonneg _)
  · apply Eventually.of_forall
    intro d
    have hh := flowWork_bound (p d) N 0
    simp only [zero_add,one_mul] at hh
    have : flowWork (p d) N 0 0≤(p d+1)^N := by omega
    exact_mod_cast this

lemma routineBudget_rate {c : ℕ → ℕ} {a : ℝ} (ha : 0≤a)
    (hc : LogPowerRate (fun d => (c d:ℝ)) (-a)) (rank : ℕ) :
    LogPowerRate (fun d => ((2*(40*c d+40)^rank:ℕ):ℝ)) (-(rank:ℝ)*a) := by
  have he := (((hc.const_mul 40).add ((LogPowerRate.const 40).mono (by linarith))).pow rank).const_mul 2
  simp only [mul_neg,neg_mul] at he ⊢
  simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_ofNat] using he
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Filter Quadrature
open scoped Topology

lemma sampleCorrelation_antitone {a b : ℝ} (ha : 0≤a) (hab : a≤b) :
    sampleCorrelation b≤ sampleCorrelation a := by
  unfold sampleCorrelation
  apply (inv_le_inv₀ (Real.sqrt_pos.mpr (by positivity))
    (Real.sqrt_pos.mpr (by positivity))).mpr
  exact Real.sqrt_le_sqrt (by nlinarith)

lemma logMeshCount_mono {T U h : ℝ} (hT : T≤U) (hU : U<1) (hh : 0<h) :
    logMeshCount T h≤logMeshCount U h := by
  apply Nat.ceil_mono
  apply div_le_div_of_nonneg_right _ hh.le
  unfold logMeshLength
  have he := Real.log_le_log (by linarith : 0<1-U) (by linarith : 1-U≤1-T)
  linarith

lemma sampleCorrelation_radius_lower {η : ℝ} (hη : 0<η) (hη1 : η≤1) :
    η/4≤Real.sqrt (1-(sampleCorrelation η)^2) := by
  have hp := sampleCorrelation_properties hη hη1
  have ht : 0<sampleCorrelation η := by linarith
  have he : Real.sqrt (1-(sampleCorrelation η)^2)=sampleCorrelation η*(η/2) := by
    have h := congrArg (fun z : ℝ => sampleCorrelation η*z) hp.2.2
    simpa only [←mul_assoc,mul_inv_cancel₀ ht.ne',one_mul] using h
  rw [he]
  nlinarith

lemma logMeshLength_sample_rate {η : ℕ → ℝ} {a : ℝ}
    (hη : ∀ᶠ d : ℕ in atTop,(d:ℝ)^(-a)≤η d ∧ η d≤1) :
    LogPowerRate (fun d => logMeshLength (sampleCorrelation (η d))) 0 := by
  have hr := ((LogPowerRate.const (Real.log 2)).add
    (((LogPowerRate.log_power a).add (LogPowerRate.const (-Real.log 4))).const_mul (-2)))
  apply LogPowerRate.of_le hr
  · filter_upwards [hη,eventually_ge_atTop (1:ℕ)] with d hd hd1
    have hp : (0:ℝ)<d := by exact_mod_cast hd1
    have hpη := sampleCorrelation_properties (lt_of_lt_of_le (Real.rpow_pos_of_pos hp _) hd.1) hd.2
    exact (logMeshLength_pos (by linarith [hpη.1]) hpη.2.1).le
  · filter_upwards [hη,eventually_ge_atTop (1:ℕ)] with d hd hd1
    have hp : (0:ℝ)<d := by exact_mod_cast hd1
    have hR : 0<(d:ℝ)^(-a) := Real.rpow_pos_of_pos hp _
    have hηpos := lt_of_lt_of_le hR hd.1
    have hpη := sampleCorrelation_properties hηpos hd.2
    have hh := sampleCorrelation_radius_lower hηpos hd.2
    have hu : (d:ℝ)^(-a)/4≤Real.sqrt (1-(sampleCorrelation (η d))^2) := by linarith
    have hs : 0≤1-(sampleCorrelation (η d))^2 := by nlinarith [hpη.1,hpη.2.1]
    have hdR : ((d:ℝ)^(-a)/4)^2≤1-(sampleCorrelation (η d))^2 := by
      have he := pow_le_pow_left₀ (by positivity : 0≤(d:ℝ)^(-a)/4) hu 2
      rwa [Real.sq_sqrt hs] at he
    have he := logMeshLength_le_scale (by linarith [hpη.1]) hpη.2.1
      (by positivity : 0<(d:ℝ)^(-a)/4) hdR
    rw [Real.log_div hR.ne' (by norm_num)] at he
    linarith
end LogConcaveSampling

end

end

end OAI
