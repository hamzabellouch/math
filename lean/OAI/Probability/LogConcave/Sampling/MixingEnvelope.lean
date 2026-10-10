import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.PrimitiveProducer
import OAI.Probability.LogConcave.OraclePrograms.TopProgram
import OAI.Probability.LogConcave.Sampling.TopScale

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter
open scoped Topology

lemma LogPowerRate.dimension : LogPowerRate (fun d : ℕ => (d:ℝ)) (-1) := by
  simpa only [neg_neg,Real.rpow_one] using LogPowerRate.power (-1)

def mixingEnvelope (κ : ℝ) (d : ℕ) : ℝ :=
  (2*(d:ℝ))*(d:ℝ)^(-(20*(1+κ)))*(topScale κ d)⁻¹

lemma mixingEnvelope_rate (κ : ℝ) : LogPowerRate (mixingEnvelope κ) (19+19*κ) := by
  have hh := (((LogPowerRate.dimension.const_mul 2).mul (LogPowerRate.power (20*(1+κ)))).mul
    (topScale_inv_rate κ))
  convert! hh using 1
  ring

lemma mixing_error_le {κ : ℝ} (hκ : 0≤κ) {d : ℕ} (hd : 1≤d) :
    ((1+Real.sqrt (topScale κ d))*Real.sqrt d)/
      ((1+topScale κ d)^(proximalRounds κ d)*Real.sqrt (topScale κ d)) ≤ mixingEnvelope κ d := by
  let h := topScale κ d
  have hp : 0<h := topScale_pos (by omega)
  have h1 : h≤1 := (topScale_le_one hκ hd).trans (by norm_num)
  have hs1 : Real.sqrt h≤1 := by simpa using Real.sqrt_le_sqrt h1
  have hs : h≤Real.sqrt h := by nlinarith [Real.sq_sqrt hp.le,Real.sqrt_nonneg h]
  have hd1 : (1:ℝ)≤d := by exact_mod_cast hd
  have hd0 : (0:ℝ)<d := by linarith
  have hsd : Real.sqrt d≤d := by nlinarith [Real.sq_sqrt (Nat.cast_nonneg d),Real.sqrt_nonneg (d:ℝ)]
  have hnum : (1+Real.sqrt h)*Real.sqrt d≤2*d := by
    nlinarith [Real.sqrt_nonneg (d:ℝ)]
  have hden : (d:ℝ)^(20*(1+κ))*h≤(1+h)^(proximalRounds κ d)*Real.sqrt h :=
    mul_le_mul (proximalRounds_power hκ hd) hs hp.le (by positivity)
  calc
    _ ≤ (2*(d:ℝ))/((1+h)^(proximalRounds κ d)*Real.sqrt h) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (2*(d:ℝ))/((d:ℝ)^(20*(1+κ))*h) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = _ := by
      dsimp [mixingEnvelope,h]
      rw [Real.rpow_neg (Nat.cast_nonneg d)]
      ring

lemma descent_error_le {κ : ℝ} (hκ : 0≤κ) {d : ℕ} (hd : 1≤d) :
    2*(2*Real.sqrt (descentScale (topScale κ d) (descentRounds d))+
      descentScale (topScale κ d) (descentRounds d))*d≤6*(d:ℝ)^(-9:ℝ) := by
  let h := descentScale (topScale κ d) (descentRounds d)
  have hp : 0<topScale κ d := topScale_pos (by omega)
  have hpos : 0<h := descentScale_pos hp _
  have h1 : h≤1 := (descentScale_le hp.le _).trans ((topScale_le_one hκ hd).trans (by norm_num))
  have hd0 : (0:ℝ)<d := by exact_mod_cast (by omega : 0<d)
  have hh : h≤1/(d:ℝ)^20 := by
    calc
      _ ≤ 1/(2:ℝ)^(descentRounds d) := div_le_div_of_nonneg_right
        ((topScale_le_one hκ hd).trans (by norm_num : (1:ℝ)/4≤1)) (by positivity)
      _ ≤ _ := one_div_le_one_div_of_le (by positivity) (descentRounds_power d hd)
  have hh' : h≤(1/(d:ℝ)^10)^2 := by
    simpa only [div_pow,one_pow,←pow_mul] using hh
  have hs : Real.sqrt h≤1/(d:ℝ)^10 := by
    calc
      _ ≤ Real.sqrt ((1/(d:ℝ)^10)^2) := Real.sqrt_le_sqrt hh'
      _ = _ := Real.sqrt_sq (by positivity)
  have hs1 : Real.sqrt h≤1 := by simpa using Real.sqrt_le_sqrt h1
  have hhs : h≤Real.sqrt h := by nlinarith [Real.sq_sqrt hpos.le,Real.sqrt_nonneg h]
  calc
    _ ≤ 6*(1/(d:ℝ)^10)*d := by
      have he : 2*(2*Real.sqrt h+h)≤6*(1/(d:ℝ)^10) := by linarith
      exact mul_le_mul_of_nonneg_right he (Nat.cast_nonneg d)
    _ = _ := by
      rw [Real.rpow_neg (Nat.cast_nonneg d)]
      norm_num
      field_simp

lemma top_asymptotic_errors {κ P : ℝ} (hκ : 0<κ) (hP : κ+3<κ*P)
    {e : ℕ → ℝ} (her : LogPowerRate e (κ*P)) (hep : ∀ᶠ d : ℕ in atTop,0≤e d) :
    ∀ᶠ d : ℕ in atTop,
      (((proximalRounds κ d:ℝ)*18+(descentRounds d:ℝ)*10)*e d*Real.sqrt d+
      ((1+Real.sqrt (topScale κ d))*Real.sqrt d)/
        ((1+topScale κ d)^(proximalRounds κ d)*Real.sqrt (topScale κ d))+
      2*(2*Real.sqrt (descentScale (topScale κ d) (descentRounds d))+
        descentScale (topScale κ d) (descentRounds d))*d)≤1/10 := by
  have hr1 := (((proximalRounds_rate hκ.le).mul_const 18).add
    ((descentRounds_rate.mul_const 10).mono (by linarith))).mul her
  have hr := hr1.mul LogPowerRate.dimension
  have ha := hr.eventually_small (b:=1) (by linarith)
  have hb := (mixingEnvelope_rate κ).eventually_small (b:=1) (by linarith)
  have hc := ((LogPowerRate.power 9).const_mul 6).eventually_small (b:=1) (by norm_num)
  filter_upwards [ha,hb,hc,hep,eventually_ge_atTop (100:ℕ)] with d ha hb hc hep hd
  have hd0 : (0:ℝ)<d := by exact_mod_cast (by omega : 0<d)
  have hd1 : (1:ℝ)≤d := by exact_mod_cast (by omega : 1≤d)
  have hd100 : (100:ℝ)≤d := by exact_mod_cast hd
  have hinv : (d:ℝ)^(-1:ℝ)≤1/100 := by
    rw [Real.rpow_neg_one]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) hd100
  have hsd : Real.sqrt d≤d := by nlinarith [Real.sq_sqrt (Nat.cast_nonneg d),Real.sqrt_nonneg (d:ℝ)]
  have hefirst : (((proximalRounds κ d:ℝ)*18+(descentRounds d:ℝ)*10)*e d*Real.sqrt d)≤(d:ℝ)^(-1:ℝ) :=
    (mul_le_mul_of_nonneg_left hsd (by positivity)).trans ((le_abs_self _).trans ha)
  have hemix := (mixing_error_le hκ.le (by omega : 1≤d)).trans ((le_abs_self _).trans hb)
  have hedesc := (descent_error_le hκ.le (by omega : 1≤d)).trans ((le_abs_self _).trans hc)
  linarith

end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Filter MeasureTheory ProbabilityTheory OracleCompiler
open scoped Classical Topology NNReal

theorem eventually_subpolynomial_sampler {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ d : ℕ in atTop,∃q : ℕ,CanSample d q ∧ (q:ℝ)≤(d:ℝ)^ε := by
  let κ := ε/4
  let P := 10*(1+κ)/κ
  have hκ : 0<κ := by dsimp [κ]; positivity
  have hPeq : κ*P=10*(1+κ) := by dsimp [P]; field_simp
  have hP : 1≤P := by
    apply (le_div_iff₀ hκ).2
    linarith
  have hPerr : κ+3<κ*P := by rw [hPeq]; linarith
  obtain ⟨t,ht,hts,_,K,_,e,her,hep,hproducer⟩ := exists_primitive_producer hκ hP
  have herr := top_asymptotic_errors hκ hPerr her (hep.mono (fun _ h => h.le))
  have hcostRate := (LogPowerRate.power (-(κ*t))).mul
    ((proximalRounds_rate hκ.le).add (descentRounds_rate.mono (by linarith)))
  have hcost := hcostRate.eventually_small (b:= -ε) (by dsimp [κ] at *; nlinarith)
  simp only [neg_neg] at hcost
  filter_upwards [hproducer,herr,hcost,hep,eventually_ge_atTop (2:ℕ)] with d hprod herr hcost hep hd
  obtain ⟨S,B,hB,hbud,hcorr⟩ := hprod
  have hd0 : (0:ℝ)<d := by exact_mod_cast (by omega : 0<d)
  have hd1 : (1:ℝ)≤d := by exact_mod_cast (by omega : 1≤d)
  have hd2 : (1:ℝ)<d := by exact_mod_cast (by omega : 1<d)
  have hqpos : 0<(d:ℝ)^(-κ) := Real.rpow_pos_of_pos hd0 _
  have hq1 : (d:ℝ)^(-κ)<1 := Real.rpow_lt_one_of_one_lt_of_neg hd2 (by linarith)
  have hh : 0<topScale κ d := topScale_pos (by omega)
  have hη : (d:ℝ)^(-(κ*t))≤1 := Real.rpow_le_one_of_one_le_of_nonpos hd1 (by nlinarith)
  let T := S 1 1
  let N := proximalRounds κ d
  let J := descentRounds d
  let q := T.full.calls*N+T.full.calls*J
  refine ⟨q,?_,?_⟩
  · refine ⟨_,inferInstance,topSeedLaw T N J,inferInstance,(topProgram T (topScale κ d) N J).algorithm,?_⟩
    intro V hV
    refine ⟨(topProgram T (topScale κ d) N J).algorithm.measurable_run hV,?_⟩
    rw [show (topProgram T (topScale κ d) N J).algorithm.run V =
      (topProgram T (topScale κ d) N J).run V from funext (Program.algorithm_run _ V)]
    have ha := topProgram_accuracy S hh (show 2*topScale κ d≤(d:ℝ)^(-κ) by unfold topScale; linarith)
      hq1 hep.le hη (hbud 1).reserve hcorr
      ⌈40*(1+κ)*dimensionLog d/topScale κ d⌉₊ J hV
    exact ha.mono (by simpa only [proximalRounds,Nat.cast_add,Nat.cast_one] using herr)
  · have hc : (T.calls:ℝ)≤(d:ℝ)^(κ*t) := (by exact_mod_cast (hbud 1).calls : (T.calls:ℝ)≤B).trans hB
    calc
      (q:ℝ) = (T.calls:ℝ)*((N:ℝ)+J) := by change ((T.calls*N+T.calls*J:ℕ):ℝ)=_; push_cast; ring
      _ ≤ (d:ℝ)^(κ*t)*((N:ℝ)+J) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ ≤ |(d:ℝ)^(κ*t)*((N:ℝ)+J)| := le_abs_self _
      _ ≤ _ := hcost

end LogConcaveSampling

end

end

end OAI
