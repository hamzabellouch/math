import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.StandaloneCorrect

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter MeasureTheory ProbabilityTheory
open scoped Classical NNReal Topology

lemma LogPowerRate.envelope {q : ℕ → ℝ} {a : ℝ} (hq : LogPowerRate q a) :
    ∃S : ℝ,0≤S ∧ ∃k : ℕ,∀ᶠ d : ℕ in atTop,|q d|≤S*dimensionLog d^k*(d:ℝ)^(-a) := by
  obtain ⟨k,hk⟩ := hq
  obtain ⟨C,hC⟩ := hk.bound
  refine ⟨|C|,abs_nonneg _,k,?_⟩
  filter_upwards [hC] with d hd
  have hn : 0≤dimensionLog d^k*(d:ℝ)^(-a) := by positivity [dimensionLog_nonneg d]
  rw [Real.norm_eq_abs,Real.norm_of_nonneg hn] at hd
  exact (hd.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hn)).trans_eq (by ring)

lemma source_error_square (κ J : ℝ) {d : ℕ} (_ : 0<d) :
    ((d:ℝ)^(-(κ*J)))^2=(d:ℝ)^(-(2*κ*J)) := by
  have hd0 : (0:ℝ)≤d := Nat.cast_nonneg d
  rw [←Real.rpow_natCast,←Real.rpow_mul hd0]
  congr 1
  push_cast
  ring

namespace OracleCompiler

theorem exists_source_numerical_ready {κ J t w : ℝ}
    (hκ : 0<κ) (hJ : 1≤J) (ht : 0<t) (hts : t<1/100)
    (hw : 0<w) (hwt : w<t) : ∃n : ℕ,
    J+10<w*((n:ℝ)-3) ∧ J+10<t*((n:ℝ)-3) ∧ 4*(J+10)<(n:ℝ) ∧
    ∀q : ℕ → ℝ,LogPowerRate q (κ*(1/2)) →
      ∀ᶠ d : ℕ in atTop,∀C : CircuitParameters,
      SourceShape κ t w n (numericalLayerCount J) d C →
      ∀{F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,0<lam → (lam:ℝ)≤1 →
      ∀hql : q d≤1/4,
      C.MeanNumericalReady hF (q d) ((d:ℝ)^(-(κ*J))) hql ∧
      C.SampleNumericalReady hF (q d) ((d:ℝ)^(-(κ*J))) := by
  obtain ⟨n,hnw,hnt,hnn,hmean⟩ := exists_calibrated_mean_circuit hκ hJ
    (b:=1/2) le_rfl ht hts hw hwt
  have hnw' : J+10<w*((n+1:ℕ)-3) := by push_cast; linarith
  refine ⟨n,hnw,hnt,hnn,?_⟩
  intro q hq
  obtain ⟨S,hS,k,henv⟩ := (hq.const_mul 2).envelope
  have hm := hmean hS k
  have hs := calibrated_sample_circuit_order hκ hJ (b:=1/2) le_rfl hw (n+1)
    (Nat.succ_pos n) hnw' hS k
  filter_upwards [hm,hs,henv,eventually_ge_atTop (1:ℕ)] with d hmd hsd hqd hd
  intro C hC F lam hF hlam hlam1 hql
  have hd0 : 0<d := hd
  have hsquare := source_error_square κ J hd0
  have heψ : -(κ*(4*t))=-(4*(κ*t)) := by ring
  obtain ⟨hT0,hT1,hh,hmc⟩ := hmd
  obtain ⟨hh',hsc⟩ := hsd
  have hbound {r σ : ℝ} (hz : MeanSize lam (q d) r σ) :
      (lam:ℝ)*r^2≤S*dimensionLog d^k*(d:ℝ)^(-(κ*(1/2))) ∧
      (lam:ℝ)*r/(σ/2)≤S*dimensionLog d^k*(d:ℝ)^(-(κ*(1/2))) := by
    have hq0 := hz.nonneg lam.coe_nonneg
    have he : 2*q d≤S*dimensionLog d^k*(d:ℝ)^(-(κ*(1/2))) := (le_abs_self _).trans hqd
    constructor
    · linarith [hz.2.2.2.1]
    · apply le_trans _ he
      apply (div_le_iff₀ (by positivity [hz.2.2.1] : 0<σ/2)).mpr
      nlinarith [hz.2.2.2.2]
  constructor
  · intro x r σ hz
    have hL : (lam:ℝ)*r≤1 := (mul_le_of_le_one_left hz.1.le hlam1).trans hz.2.1
    obtain ⟨hl,hp⟩ := hmc hF x hz.1 hz.2.1 hlam hL
      (show 0<σ/2 by positivity [hz.2.2.1]) (hbound hz).1 (hbound hz).2
    simpa only [CircuitParameters.MeanNumericalReady,hC.n_eq,hC.N_eq,hC.T_eq,hC.h_eq,
      hC.ψ_eq,heψ,hsquare] using hp
  · intro x r η hz hl
    have hL : (lam:ℝ)*r≤1 := (mul_le_of_le_one_left hz.1.le hlam1).trans hz.2.1
    have hq0 := hz.nonneg lam.coe_nonneg
    have hb : (lam:ℝ)*r^2≤S*dimensionLog d^k*(d:ℝ)^(-(κ*(1/2))) := by
      have he := hz.2.2.2.2.trans (mul_le_of_le_one_right hq0 hz.2.2.2.1)
      have hhq : 2*q d≤S*dimensionLog d^k*(d:ℝ)^(-(κ*(1/2))) := (le_abs_self _).trans hqd
      linarith
    obtain ⟨hl',hp⟩ := hsc hF x hz.1 hz.2.1 hlam hL hb
    have hη := sampleCorrelation_properties hz.2.2.1 hz.2.2.2.1
    change ∀{T : ℝ},1/2≤T → T<1 → ∀e : ProbabilityNode T ((d:ℝ)^(-(κ*w))) (n+1),
      Integrable (fun z => ‖sampleMeanCircuit F x r T ((d:ℝ)^(-(κ*w))) (n+1) (numericalLayerCount J) e z-
        T⁻¹ • fullProbabilityFlow hF x hz.1.le hl' (probabilityNodeTime T ((d:ℝ)^(-(κ*w))) (n+1) e) z‖^2)
        (stdGaussian (Point d)) ∧
      (∫z,‖sampleMeanCircuit F x r T ((d:ℝ)^(-(κ*w))) (n+1) (numericalLayerCount J) e z-
        T⁻¹ • fullProbabilityFlow hF x hz.1.le hl' (probabilityNodeTime T ((d:ℝ)^(-(κ*w))) (n+1) e) z‖^2
        ∂stdGaussian (Point d))≤circuitD F x^2*(d:ℝ)^(-(2*κ*J)) at hp
    rw [←hC.h_eq,←hC.n_eq,←hC.N_eq] at hp
    have he := hp hη.1 hη.2.1 (C.sampleEndpoint η hz.2.2.1 hz.2.2.2.1)
    simpa only [CircuitParameters.sampleEndpoint,
      probabilityEndpoint_time _ _ _ _ (Nat.succ_pos C.n),hsquare] using he
end OracleCompiler
end LogConcaveSampling

end

end

end OAI
