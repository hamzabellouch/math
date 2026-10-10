import OAI.NumberTheory.Jacobsthal.Harmonic.BudgetPolynomialBound
import OAI.NumberTheory.Jacobsthal.Partitions.HorizonMeshSmallness
import OAI.NumberTheory.Jacobsthal.Primes.PrimeMarginalInduction

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.UniformBudgetRate

open _root_.Set _root_.Filter
open scoped Topology
open UniformFailureBudget ExponentialMesh BudgetPolynomialBound HorizonMeshSmallness PrimeKilledChain

theorem uniform_budget_rate {c₁ c₂ C₁ C₂ C₃ D κ A : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hD : 0 ≤ D) (hA : 0 ≤ A)
    (hκ : 0 < κ) (hc₁ : 4*κ ≤ c₁) (hc₂ : 2*κ ≤ c₂) (hκr : κ ≤ normalizationRate) :
    ∀ᶠ w : ℝ in atTop, ∀ S : ℝ, 0 ≤ S → S ≤ (Real.log w)^3 → ∀ N : ℕ,
      (N:ℝ) ≤ A*(Real.log w)^3 →
      2*mesh κ w ≤ 1 ∧ upperDisplacement S (mesh κ w) N+mesh κ w ≤ 1 ∧
      (N:ℝ)*stepBudget c₁ c₂ C₁ C₂ C₃ D w S (mesh κ w) N ≤
        Real.exp (-(κ/2)*Real.sqrt (Real.log w)) := by
  filter_upwards [horizon_mesh_smallness hA hD hκ,
    log_power_exp_absorption (A*coefficient A C₁ C₂ C₃ D) 21 hκ,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with w hsmall hpoly hlog
  intro S hS hSP N hNP
  have hsm := hsmall S hS hSP N hNP
  refine ⟨hsm.1,hsm.2.2.2,?_⟩
  have h := budget_polynomial_bound (P:=(Real.log w)^3) N hC₁ hC₂ hC₃ hD hA hκ.le hc₁ hc₂ hκr
    (by linarith) (one_le_pow₀ hlog) hS hSP hNP hsm.2.1 hsm.2.2.1
  have hp : ((Real.log w)^3)^7 = (Real.log w)^21 := by ring
  rw [hp] at h
  exact h.trans hpoly

theorem source_scale_bound {d w B : ℝ} (hW : d^2 ≤ Real.log w)
    (hB : 2 ≤ Real.log B) (hcomp : Real.log B ≤ d*Real.log w) :
    (Real.log B)^2 ≤ (Real.log w)^3 ∧
      (LowStateHorizon.sourceHorizon ((Real.log B)^2) B:ℝ) ≤ 5*d^3*(Real.log w)^3 := by
  have hlog : 0 ≤ Real.log w := (sq_nonneg d).trans hW
  have hpow₂ := pow_le_pow_left₀ (show 0 ≤ Real.log B by linarith) hcomp 2
  have hpow₃ := pow_le_pow_left₀ (show 0 ≤ Real.log B by linarith) hcomp 3
  have hmul := mul_le_mul_of_nonneg_right hW (sq_nonneg (Real.log w))
  have hN := LowStateHorizon.source_horizon_log_cube hB
  constructor <;> nlinarith

end NumberTheoryLean.UniformBudgetRate

end

section

namespace NumberTheoryLean.SourceMarginalRate

open _root_.Set _root_.Filter _root_.MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
open FinitePathGeometry PrimeHistories PrimeKilledChain PrimeSideSupport PrimeGridGeometry PrimeGridKernel
open PrimeMarginalInduction MarginalProfiles SourceParentBin ExponentialMesh UniformBudgetRate
open DerivativeWeights LowStateHorizon

theorem mesh_eventually_small {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) :
    ∀ᶠ w : ℝ in atTop, mesh κ w ≤ ε := by
  have ht := log_power_exp_tendsto 1 0 hκ
  filter_upwards [ht.eventually (eventually_lt_nhds hε)] with w hw
  have he : Real.exp (-κ*Real.sqrt (Real.log w)) < ε := by simpa only [pow_zero,one_mul] using hw
  exact (mesh_upper κ w).trans he.le

theorem source_discrete_marginals : ∃ κ₀ C : ℝ, 0 < κ₀ ∧ 0 < C ∧
    ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∀ d : ℝ, 0 < d → ∃ w₀ : ℝ, 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell B : ℝ, ∀ start : Node,
      1 ≤ ell → 0 < B → 2 ≤ Real.log B → Real.log B ≤ d*Real.log w →
      0 < start.gap → start.side = .even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
      let S := (Real.log B)^2
      let N := sourceHorizon S B
      let m := ⌈Real.exp (κ*Real.sqrt (Real.log w))⌉₊
      (∀ n,IsProbabilityMeasure (pathLaw w ell S start n)) ∧
      (∀ j,Valid .odd (point m j) → mass w ell S start m 1 j ≤
        ENNReal.ofReal (C*width m*W (point m j)*weight .odd (point m j))) ∧
      (∀ n,2 ≤ n → n ≤ N → ∀ j,lowerIndex m (sideAfter .even n) ≤ j → mass w ell S start m n j ≤
        ENNReal.ofReal (C*width m*weight (sideAfter .even n) (point m j)*profile m (sideAfter .even n) (point m j))) := by
  obtain ⟨κ₀,L,hκ₀,hL,hprofiles⟩ := finite_marginal_profiles
  have hCpos := initialConstant_pos
  refine ⟨κ₀,48*initialConstant,hκ₀,by positivity,?_⟩
  intro κ hκ hκle d hd
  obtain ⟨wP,hwP,hprofiles⟩ := hprofiles κ hκ hκle
  let A := 5*d^3
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hevent := (MarginalGrowth.factor_power_bounded hA hL.le hκ).and
    ((mesh_eventually_small hκ (by norm_num : (0:ℝ) < 1/100)).and
      (Real.tendsto_log_atTop.eventually (eventually_ge_atTop (d^2))))
  obtain ⟨W₀,hW₀⟩ := eventually_atTop.mp hevent
  refine ⟨max wP W₀,hwP.trans_le (le_max_left _ _),?_⟩
  intro w hw ell B start hell _hB hlogB hcomp hr hi h199 h23
  dsimp only
  let S := (Real.log B)^2
  let N := sourceHorizon S B
  let m := ⌈Real.exp (κ*Real.sqrt (Real.log w))⌉₊
  have hwe := hW₀ w ((le_max_right _ _).trans hw)
  have hscale := source_scale_bound hwe.2.2 hlogB hcomp
  have hS0 : 0 ≤ S := sq_nonneg _
  have hS3 : 3 ≤ S := by dsimp [S]; nlinarith
  have hS : S ≤ (Real.log w)^3 := hscale.1
  have hN : (N:ℝ) ≤ A*(Real.log w)^3 := hscale.2
  have hm : 1 ≤ m := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hmesh : width m = mesh κ w := rfl
  have hsmall : width m ≤ 1/100 := by rw [hmesh]; exact hwe.2.1
  have hp := hprofiles w ((le_max_left _ _).trans hw) ell S hS3 hS start hell hr hi h199 h23 m hm hmesh hsmall
  have hC0 := initialConstant_pos.le
  have hwidth := width_nonneg m
  have hNpos : 1 ≤ N := by dsimp [N,sourceHorizon]; omega
  have hOne : (1:ℝ) ≤ A*(Real.log w)^3 := by
    have h : ((1:ℕ):ℝ) ≤ (N:ℝ) := by exact_mod_cast hNpos
    simpa only [Nat.cast_one] using h.trans hN
  have hG : MarginalGrowth.factor L κ w S ≤ 2 := by
    simpa only [pow_one] using hwe.1 S hS0 hS 1 (by simpa only [Nat.cast_one] using hOne)
  refine ⟨hp.1,?_,?_⟩
  · intro j hjV
    have hb := hp.2.1 j hjV
    have hWt := (WeightFutureIntegrals.W_pos (valid_pos hjV)).le
    have hφ := (weight_pos hjV).le
    have hC : initialConstant*MarginalGrowth.factor L κ w S ≤ 48*initialConstant := by nlinarith
    exact hb.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hwidth) hWt) hφ))
  · intro n hn2 hnN j hj
    have hb := hp.2.2 n hn2 j hj
    have hn : (n:ℝ) ≤ A*(Real.log w)^3 := (show (n:ℝ) ≤ (N:ℝ) by exact_mod_cast hnN).trans hN
    have hGn := hwe.1 S hS0 hS n hn
    have hφ := (weight_pos (index_valid hm (sideAfter .even n) hj)).le
    have hProf := profile_nonneg m (index_regular hm (sideAfter .even n) hj)
    have hC : (24*initialConstant)*(MarginalGrowth.factor L κ w S)^n ≤ 48*initialConstant := by nlinarith
    exact hb.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hwidth) hφ) hProf))

end NumberTheoryLean.SourceMarginalRate

end

end Erdos970

end OAI
