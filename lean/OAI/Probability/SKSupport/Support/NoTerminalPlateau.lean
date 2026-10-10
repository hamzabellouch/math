import Mathlib
import OAI.Probability.SKSupport.Regularity.ClosedTime
import OAI.Probability.SKSupport.Support.ContactPotential

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK
open Heat
variable {Ω : Type*} [MeasurableSpace Ω]

lemma terminal_plateau_q_lt_near_one (W : BrownianSystem Ω) (γ : OrderParameter)
    {a c : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (hc0 : 0 ≤ c)
    (hc : ∀ r ∈ Ioo a 1, extend γ.val r=c) :
    ∃ b : ℝ, 0 ≤ b ∧ b < 1 ∧ ∀ t ∈ Ioo b 1, squareMoment W γ (diffusion W γ) t < t := by
  let s₀ : ℝ := (a+1)/2
  have hs0 : 0 < s₀ := by dsimp [s₀];linarith
  have hs1 : s₀ < 1 := by dsimp [s₀];linarith
  have has : a < s₀ := by dsimp [s₀];linarith
  let s : Time := ⟨s₀,⟨hs0.le,hs1⟩⟩
  obtain ⟨C,hC,hbound⟩ := terminal_plateau_second_moment_defect W γ ha1 hc0 hc s hs0 has
  have hl : Tendsto (fun t : ℝ => Real.sqrt (1-t)) (𝓝 1) (𝓝 0) := by
    have hcroot : Continuous (fun t : ℝ => Real.sqrt (1-t)) := by fun_prop
    simpa only [sub_self,Real.sqrt_zero] using hcroot.tendsto (1:ℝ)
  have hm : Tendsto (fun t : ℝ => 8*kernelConstant*c*Real.sqrt (1-t)) (𝓝 1) (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hl (a := 8*kernelConstant*c)
  have hev : ∀ᶠ t in 𝓝 (1:ℝ), ((s:ℝ)+1)/2 ≤ t ∧
      8*kernelConstant*c*Real.sqrt (1-t) ≤ 1/2 ∧ Real.sqrt (1-t) < C := by
    filter_upwards [lt_mem_nhds (show ((s:ℝ)+1)/2 < 1 by change (s₀+1)/2 < 1;linarith),
      hm.eventually_lt_const (show (0:ℝ) < 1/2 by norm_num),hl.eventually_lt_const hC] with t ht ht' ht''
    exact ⟨ht.le,ht'.le,ht''⟩
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hev
  let b : ℝ := max 0 (1-ε/2)
  have hb0 : 0 ≤ b := le_max_left _ _
  have hb1 : b < 1 := max_lt (by norm_num) (by linarith)
  refine ⟨b,hb0,hb1,fun t ht => ?_⟩
  have hεt : t ∈ Metric.ball (1:ℝ) ε := by
    rw [Metric.mem_ball,Real.dist_eq,abs_of_neg (sub_neg.mpr ht.2)]
    dsimp [b] at ht
    linarith [ht.1,le_max_right (0:ℝ) (1-ε/2)]
  obtain ⟨hm0,hm1,hm2⟩ := hball hεt
  have ht0 := hb0.trans ht.1.le
  have hbq := hbound ⟨t,⟨ht0,ht.2⟩⟩ hm0 hm1
  have hroot := Real.sqrt_pos.mpr (sub_pos.mpr ht.2)
  have hsqr := Real.sq_sqrt (sub_nonneg.mpr ht.2.le)
  have hmul := mul_lt_mul_of_pos_right hm2 hroot
  change C*Real.sqrt (1-t) ≤ 1-squareMoment W γ (diffusion W γ) t at hbq
  nlinarith

theorem minimizer_no_terminal_plateau (W : BrownianSystem Ω) (γ : OrderParameter) (hmin : IsMinimizer W γ) :
    ¬ ∃ a c : ℝ, 0 ≤ a ∧ a < 1 ∧ 0 ≤ c ∧ ∀ t ∈ Ioo a 1, extend γ.val t=c := by
  rintro ⟨a,c,ha0,ha1,hc0,hc⟩
  obtain ⟨b,hb0,hb1,hneg⟩ := terminal_plateau_q_lt_near_one W γ ha0 ha1 hc0 hc
  have hi := (contactIntegrand_tail_integrable W γ ⟨hb0,hb1.le⟩).neg
  have hip : IntegrableOn (fun t => t-squareMoment W γ (diffusion W γ) t) (Ioo b 1) := by
    have hh := (intervalIntegrable_iff_integrableOn_Ioo_of_le hb1.le).mp hi
    change IntegrableOn (fun t => -(squareMoment W γ (diffusion W γ) t-t)) (Ioo b 1) at hh
    simpa only [neg_sub] using hh
  have hn : 0 ≤ᵐ[volume.restrict (Ioo b 1)] (fun t => t-squareMoment W γ (diffusion W γ) t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact sub_nonneg.mpr (hneg t ht).le
  have hsupp : Ioo b 1 ⊆ Function.support (fun t => t-squareMoment W γ (diffusion W γ) t) := by
    intro t ht
    exact ne_of_gt (sub_pos.mpr (hneg t ht))
  have hμpos : 0 < (volume.restrict (Ioo b 1)) (Ioo b 1) := by
    rw [Measure.restrict_apply measurableSet_Ioo,inter_self,Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hb1)
  have hp := (integral_pos_iff_support_of_nonneg_ae hn hip).mpr (hμpos.trans_le (measure_mono hsupp))
  have he : (∫ t in Ioo b 1, t-squareMoment W γ (diffusion W γ) t)=-contactPotential W γ b := by
    unfold contactPotential
    rw [← intervalIntegral.integral_neg]
    simp only [neg_sub]
    rw [intervalIntegral.integral_of_le hb1.le,integral_Ioc_eq_integral_Ioo]
  rw [he] at hp
  linarith [contactPotential_nonneg W γ hmin ⟨b,⟨hb0,hb1⟩⟩]

end ZeroTemperatureSK

end
end
section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section

namespace ZeroTemperatureSK

def spinHamiltonian (n : ℕ) (J : (Fin n × Fin n) → ℝ) (σ : Fin n → Bool) : ℝ :=
  (∑ i : Fin n, ∑ j : Fin n, if i < j then
    J (i,j) * (if σ i then 1 else -1) * (if σ j then 1 else -1) else 0) / Real.sqrt n

def spinDisorder (n : ℕ) : Measure ((Fin n × Fin n) → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

def expectedSKMaximum (n : ℕ) : ℝ :=
  (∫ J, sSup (Set.range (spinHamiltonian n J)) ∂spinDisorder n) / n

def groundStateValue : ℝ := limUnder atTop expectedSKMaximum

variable {Ω : Type*} [MeasurableSpace Ω]

def TerminalValueConclusion (W : BrownianSystem Ω) (γ : OrderParameter)
    (X : ℝ≥0 → Ω → ℝ) : Prop :=
  Tendsto expectedSKMaximum atTop (𝓝 groundStateValue) ∧
  ∃ U₁ : Ω → ℝ,
    Martingale (terminalGradient W γ X U₁) (closedFiltration W) W.law ∧
    (∀ᵐ ω ∂W.law, |U₁ ω| ≤ 1 ∧ (U₁ ω)^2 = 1) ∧
    MemLp U₁ 2 W.law ∧
    (∀ᵐ ω ∂W.law,
      Tendsto (fun t : ℝ => gradient W γ t (X (Real.toNNReal t) ω))
        (𝓝[<] (1 : ℝ)) (𝓝 (U₁ ω))) ∧
    Tendsto (fun t : ℝ => eLpNorm
      (fun ω => gradient W γ t (X (Real.toNNReal t) ω) - U₁ ω) 2 W.law)
      (𝓝[<] (1 : ℝ)) (𝓝 0) ∧
    Integrable (fun ω => |X 1 ω|) W.law ∧
    Integrable (fun ω => U₁ ω * W.B 1 ω) W.law ∧
    IntervalIntegrable (fun t : ℝ => t * extend γ.val t) volume 0 1 ∧
    IntervalIntegrable (fun t : ℝ => ∫ ω, curvature W γ t
      (X (Real.toNNReal t) ω) ∂W.law) volume 0 1 ∧
    groundStateValue = parisi W γ ∧
    groundStateValue = (∫ ω, |X 1 ω| ∂W.law) -
      ∫ t in (0 : ℝ)..1, t * extend γ.val t ∧
    groundStateValue = (∫ ω, U₁ ω * W.B 1 ω ∂W.law) ∧
    groundStateValue = (∫ t in (0 : ℝ)..1,
      ∫ ω, curvature W γ t (X (Real.toNNReal t) ω) ∂W.law)

def GaussianConclusion (W : BrownianSystem Ω) (γ : OrderParameter)
    (X : ℝ≥0 → Ω → ℝ) (T : ℝ) : Prop :=
  (∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N → ∀ j ∈ Finset.Icc 1 N,
    Integrable (fun z => (curvature W γ (meshTime T N (j-1))
      (eulerState W γ T N (j-1) z))^2) (gaussianLaw N) ∧
    0 < eulerCurvatureMoment W γ T N j ∧ 0 < eulerNormalizer W γ T N j) ∧
  Tendsto (gaussianValueSum W γ T) atTop
    (𝓝 (∫ t in (0 : ℝ)..T,
      ∫ ω, curvature W γ t (X (Real.toNNReal t) ω) ∂W.law)) ∧
  Tendsto (fun T : ℝ => ∫ t in (0 : ℝ)..T,
      ∫ ω, curvature W γ t (X (Real.toNNReal t) ω) ∂W.law)
    (𝓝[<] (1 : ℝ)) (𝓝 groundStateValue)

end ZeroTemperatureSK

end
end

end OAI
