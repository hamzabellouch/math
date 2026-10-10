import Mathlib
import OAI.NumberTheory.PrimePackets.SubquadraticGrowth

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
namespace PrimeDegreePackets.AnalyticGrowth

lemma outside_nearOneBox_scaled_gap {L : ℝ} (hL : 0 < L) {ρ : ℂ}
    (hβ : ρ.re ≤ 1) (hbox : ¬ InNearOneBox L ρ) :
    (1/4:ℝ)^2 ≤ (L*(1-ρ.re))^2+(L*ρ.im)^2 := by
  have hX : 0 ≤ L*(1-ρ.re) := mul_nonneg hL.le (by linarith)
  by_contra h
  have hsq : (L*(1-ρ.re))^2+(L*ρ.im)^2 < (1/4:ℝ)^2 := lt_of_not_ge h
  have hXq : L*(1-ρ.re) ≤ 1/4 := by nlinarith [sq_nonneg (L*ρ.im)]
  have hYq : |L*ρ.im| ≤ 1/4 := by
    have H := sq_abs (L*ρ.im)
    nlinarith [sq_nonneg (L*(1-ρ.re)), abs_nonneg (L*ρ.im)]
  apply hbox
  constructor
  · have H := (le_div_iff₀ hL).mpr (show (1-ρ.re)*L ≤ 1/4 by nlinarith only [hXq])
    have HE : (1/4:ℝ)/L = 1/(4*L) := by ring
    rw [HE] at H
    linarith
  · rw [abs_mul, abs_of_pos hL] at hYq
    have H := (le_div_iff₀ hL).mpr (show |ρ.im| * L ≤ 1/4 by nlinarith only [hYq])
    simpa only [div_div] using H

lemma realZeroPole_le_base_of_outside_box {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0)
    (hstrip : ∀ ρ, f ρ = 0 → ρ.re ≤ 1)
    {L h : ℝ} (hL : 0 < L) (hh : 0 < h) (hh4 : h ≤ 4/L) (ρ : ℂ)
    (hbox : ¬ InNearOneBox L ρ) :
    realZeroPole f (1+h) ρ ≤ 676*realZeroPole f (1+1/L) ρ := by
  by_cases hm : zeroMultiplicity f ρ = 0
  · simp [realZeroPole,hm]
  have hβ := hstrip ρ ((zeroMultiplicity_ne_zero_iff hf h0 ρ).mp hm)
  have hX : 0 ≤ L*(1-ρ.re) := mul_nonneg hL.le (by linarith)
  have hU : 0 < L*h := mul_pos hL hh
  have hU4 : L*h ≤ 4 := by have H := (le_div_iff₀ hL).mp hh4; nlinarith only [H]
  have H := realPoleKernel_comparison (by norm_num : (0:ℝ)<1/4) hX hU hU4
    (outside_nearOneBox_scaled_gap hL hβ hbox)
  norm_num only at H
  have HL := mul_le_mul_of_nonneg_left H hL.le
  have HN := mul_le_mul_of_nonneg_left HL
    (show (0:ℝ) ≤ zeroMultiplicity f ρ by exact_mod_cast zeroMultiplicity_nonneg hf ρ)
  simp only [realZeroPole, real_inverse_pole_scaled hL.ne', mul_one_div_cancel hL.ne']
  unfold realPoleKernel at HN
  nlinarith only [HN]

 

def nearOneZeroPole (f : ℂ → ℂ) (L s : ℝ) (ρ : ℂ) : ℝ :=
  if InNearOneBox L ρ then realZeroPole f s ρ else 0

def separatedZeroPole (f : ℂ → ℂ) (L s : ℝ) (ρ : ℂ) : ℝ :=
  if InNearOneBox L ρ then 0 else realZeroPole f s ρ

lemma zeroPole_split (f : ℂ → ℂ) (L s : ℝ) (ρ : ℂ) :
    nearOneZeroPole f L s ρ + separatedZeroPole f L s ρ = realZeroPole f s ρ := by
  unfold nearOneZeroPole separatedZeroPole
  split <;> simp

lemma nearOneZeroPole_summable {f : ℂ → ℂ} {L s : ℝ}
    (H : Summable (realZeroPole f s)) : Summable (nearOneZeroPole f L s) := by
  exact H.indicator {ρ | InNearOneBox L ρ}

lemma separatedZeroPole_summable {f : ℂ → ℂ} {L s : ℝ}
    (H : Summable (realZeroPole f s)) : Summable (separatedZeroPole f L s) := by
  have HE : separatedZeroPole f L s =
      fun ρ => realZeroPole f s ρ - nearOneZeroPole f L s ρ := by
    funext ρ
    have H := zeroPole_split f L s ρ
    linarith
  rw [HE]
  exact H.sub (nearOneZeroPole_summable H)

end PrimeDegreePackets.AnalyticGrowth


namespace PrimeDegreePackets.HeckeMellin
open AnalyticGrowth

lemma dedekind_separated_zero_sum_bound {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hodd : Odd (finrank ℚ K)) {B L h : ℝ}
    (hL : L = Real.log |(NumberField.discr K : ℝ)|) (hL1 : 1 ≤ L) (hB : 0 < B)
    (harch : ∀ s ∈ Icc (1:ℝ) 2, |archimedeanZetaTerm (d+1) s| ≤ B)
    (hh : h ∈ Ioc (0:ℝ) (4/L)) :
    0 ≤ ∑' ρ, separatedZeroPole (completedThetaXi σ hn) L (1+h) ρ ∧
      (∑' ρ, separatedZeroPole (completedThetaXi σ hn) L (1+h) ρ) ≤
        676*(B+3)*L := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have Hs := dedekindXi_hasSum_realZeroPole σ hn hodd (by linarith [hh.1] : 1 < 1+h)
  have H0 := hasSum_realZeroPole (completedThetaXi_entire σ hn)
    (dedekindXiZeros_ne_zero σ hn hodd) (completedThetaXi_hasSubquadraticGrowth σ hn)
    (fun z => (completedThetaXi_functionalEquation σ hn hodd z).symm)
    (fun z hz => (dedekindXiZeros_re_mem_Icc σ hn hodd hz).2)
    (by have H := one_div_pos.mpr hLp; linarith : 1 < 1+1/L)
  have Hn (ρ : ℂ) : 0 ≤ separatedZeroPole (completedThetaXi σ hn) L (1+h) ρ := by
    unfold separatedZeroPole
    split
    · exact le_rfl
    · exact dedekindXi_realZeroPole_nonneg σ hn hodd (by linarith [hh.1]) ρ
  refine ⟨tsum_nonneg Hn, ?_⟩
  have Hpoint (ρ : ℂ) : separatedZeroPole (completedThetaXi σ hn) L (1+h) ρ ≤
      676*realZeroPole (completedThetaXi σ hn) (1+1/L) ρ := by
    unfold separatedZeroPole
    split
    · exact mul_nonneg (by norm_num) (dedekindXi_realZeroPole_nonneg σ hn hodd
        (by have H := one_div_pos.mpr hLp; linarith) ρ)
    · apply realZeroPole_le_base_of_outside_box (completedThetaXi_entire σ hn)
        (dedekindXiZeros_ne_zero σ hn hodd)
        (fun z hz => (dedekindXiZeros_re_mem_Icc σ hn hodd hz).2) hLp hh.1 hh.2 ρ
      assumption
  have HT := (separatedZeroPole_summable Hs.summable).tsum_le_tsum Hpoint
    (H0.summable.mul_left 676)
  rw [tsum_mul_left, H0.tsum_eq] at HT
  have HB := completedThetaXi_logDeriv_base_le σ hn hodd hL hL1 harch
  have HBL : B+1 ≤ (B+1)*L := by nlinarith
  nlinarith

 

theorem dedekind_regularized_deriv_remove_exceptional {d : ℕ} {K : Type*}
    [Field K] [NumberField K] [NumberField.IsTotallyReal K]
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (hodd : Odd (finrank ℚ K)) {B L : ℝ}
    (hL : L = Real.log |(NumberField.discr K : ℝ)|) (hL4 : 4 ≤ L) (hB : 0 < B)
    (harch : ∀ s ∈ Icc (1:ℝ) 2, |archimedeanZetaTerm (d+1) s| ≤ B) :
    ∀ h ∈ Ioc (0:ℝ) (4/L),
      |deriv (logRegularizedDedekindZeta K) h -
        ∑' ρ, nearOneZeroPole (completedThetaXi σ hn) L (1+h) ρ| ≤
          (677*B+2030)*L := by
  intro h hh
  have hLp : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have Hsum := dedekindXi_hasSum_realZeroPole σ hn hodd (by linarith [hh.1] : 1 < 1+h)
  have HS := dedekind_separated_zero_sum_bound σ hn hodd hL hL1 hB harch hh
  have Hsplit := (nearOneZeroPole_summable (L := L) Hsum.summable).tsum_add
    (separatedZeroPole_summable (L := L) Hsum.summable)
  simp only [zeroPole_split] at Hsplit
  rw [Hsum.tsum_eq, hn, ← hL] at Hsplit
  have HE : 1+h-1 = h := by ring
  rw [HE] at Hsplit
  have Hder := logRegularizedDedekindZeta_deriv K hh.1
  have hh1 : h ≤ 1 := hh.2.trans ((div_le_one hLp).mpr hL4)
  have HG := abs_le.mp (harch (1+h) ⟨by linarith [hh.1], by linarith⟩)
  have Hr : 0 ≤ 1/(1+h) ∧ 1/(1+h) ≤ 1 := by
    constructor
    · exact one_div_nonneg.mpr (by linarith [hh.1])
    · exact (div_le_one (by linarith [hh.1])).mpr (by linarith [hh.1])
  have HBL : B ≤ B*L := by nlinarith
  apply abs_le.mpr
  constructor <;> nlinarith only [Hsplit, Hder, HS.1, HS.2, HG.1, HG.2,
    Hr.1, Hr.2, HBL, hL4]

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets.AnalyticGrowth

lemma nearOneZeroPole_sum_of_no_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) {L s : ℝ}
    (H : ∀ ρ, f ρ = 0 → ¬ InNearOneBox L ρ) :
    (∑' ρ, nearOneZeroPole f L s ρ) = 0 := by
  have Hz (ρ : ℂ) : nearOneZeroPole f L s ρ = 0 := by
    unfold nearOneZeroPole
    split
    next hbox =>
      have hm : zeroMultiplicity f ρ = 0 :=
        (zeroMultiplicity_eq_zero_iff hf h0 ρ).mpr (fun hρ => H ρ hρ hbox)
      simp [realZeroPole,hm]
    · rfl
  simp [Hz]

lemma nearOneZeroPole_sum_of_unique {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) {L s : ℝ} {ρ : ℂ}
    (hbox : InNearOneBox L ρ) (hm : zeroMultiplicity f ρ = 1) (hreal : ρ.im = 0)
    (H : ∀ τ, f τ = 0 → InNearOneBox L τ → τ = ρ) :
    (∑' τ, nearOneZeroPole f L s τ) = 1/(s-ρ.re) := by
  have Hz (τ : ℂ) (hne : τ ≠ ρ) : nearOneZeroPole f L s τ = 0 := by
    unfold nearOneZeroPole
    split
    next hτ =>
      have hmult : zeroMultiplicity f τ = 0 :=
        (zeroMultiplicity_eq_zero_iff hf h0 τ).mpr (fun hz => hne (H τ hz hτ))
      simp [realZeroPole,hmult]
    · rfl
  rw [tsum_eq_single ρ Hz, nearOneZeroPole, ite_eq_left hbox, realZeroPole, hm]
  have HE : ρ = (ρ.re : ℂ) := by apply Complex.ext <;> simp [hreal]
  rw [HE]
  norm_cast
  simp

end PrimeDegreePackets.AnalyticGrowth


namespace PrimeDegreePackets.HeckeMellin
open AnalyticGrowth

 

theorem dedekind_regularized_deriv_dichotomy (d : ℕ) :
    ∃ C M : ℝ, 0 < C ∧ 0 < M ∧
      ∀ {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K],
      ∀ (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
        (_ : Odd (finrank ℚ K)),
      C < Real.log |(NumberField.discr K : ℝ)| →
      (∀ h ∈ Ioc (0:ℝ) (4 / Real.log |(NumberField.discr K : ℝ)|),
        |deriv (logRegularizedDedekindZeta K) h| ≤
          M * Real.log |(NumberField.discr K : ℝ)|) ∨
      (∃ β : ℝ, 1-1/(4*Real.log |(NumberField.discr K : ℝ)|) ≤ β ∧ β < 1 ∧
        completedThetaXi σ hn β = 0 ∧ zeroMultiplicity (completedThetaXi σ hn) β = 1 ∧
        ∀ h ∈ Ioc (0:ℝ) (4 / Real.log |(NumberField.discr K : ℝ)|),
          |deriv (logRegularizedDedekindZeta K) h - 1/(1+h-β)| ≤
            M * Real.log |(NumberField.discr K : ℝ)|) := by
  obtain ⟨B,hB,harch⟩ := archimedeanZetaTerm_bounded (d+1)
  obtain ⟨C,hC,Hunique⟩ := dedekind_near_one_zero_real_simple_unique d
  refine ⟨max C 4, 677*B+2030, lt_of_lt_of_le hC (le_max_left _ _), by positivity, ?_⟩
  intro K _ _ _ σ hn hodd hL
  have hLC : C < Real.log |(NumberField.discr K : ℝ)| :=
    lt_of_le_of_lt (le_max_left _ _) hL
  have hL4 : (4:ℝ) ≤ Real.log |(NumberField.discr K : ℝ)| :=
    (lt_of_le_of_lt (le_max_right _ _) hL).le
  have HE := dedekind_regularized_deriv_remove_exceptional σ hn hodd rfl hL4 hB harch
  by_cases H : ∃ ρ, completedThetaXi σ hn ρ = 0 ∧
      InNearOneBox (Real.log |(NumberField.discr K : ℝ)|) ρ
  · obtain ⟨ρ,hρ,hbox⟩ := H
    obtain ⟨hm,hr,Huniq⟩ := Hunique σ hn hodd hLC ρ hρ hbox
    have HEρ : ρ = (ρ.re : ℂ) := by apply Complex.ext <;> simp [hr]
    have hβle := (dedekindXiZeros_re_mem_Icc σ hn hodd hρ).2
    have hβne : ρ.re ≠ 1 := by
      intro he
      have Hρ : ρ = 1 := by rw [HEρ,he]; rfl
      subst ρ
      exact dedekindXiZeros_ne_one σ hn hodd hρ
    refine Or.inr ⟨ρ.re,hbox.1,lt_of_le_of_ne hβle hβne,by simpa [← HEρ] using hρ,
      by simpa [← HEρ] using hm,?_⟩
    intro h hh
    have HH := HE h hh
    rwa [nearOneZeroPole_sum_of_unique (completedThetaXi_entire σ hn)
      (dedekindXiZeros_ne_zero σ hn hodd) hbox hm hr Huniq] at HH
  · left
    intro h hh
    have HH := HE h hh
    have Hnone : ∀ ρ, completedThetaXi σ hn ρ = 0 →
        ¬ InNearOneBox (Real.log |(NumberField.discr K : ℝ)|) ρ := by
      intro ρ hρ hb
      exact H ⟨ρ,hρ,hb⟩
    rwa [nearOneZeroPole_sum_of_no_zero (completedThetaXi_entire σ hn)
      (dedekindXiZeros_ne_zero σ hn hodd) Hnone,sub_zero] at HH

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets

 

theorem residue_log_comparison_remove_pole (K : Type*) [Field K] [NumberField K]
    {B C a : ℝ} (hB : 0 < B) (ha : 0 < a)
    (H : ∀ h ∈ Ioc (0:ℝ) B,
      |deriv (logRegularizedDedekindZeta K) h - 1/(h+a)| ≤ C)
    {h : ℝ} (hh : 0 < h) (hhB : h ≤ B) :
    |logRegularizedDedekindZeta K h - Real.log (NumberField.dedekindZeta_residue K) -
        Real.log ((h+a)/a)| ≤ C*h := by
  let f : ℝ → ℝ := fun u => logRegularizedDedekindZeta K u - Real.log (u+a)
  have HD (u : ℝ) (hu : 0 < u) :
      HasDerivAt f (deriv (logRegularizedDedekindZeta K) u - 1/(u+a)) u := by
    have HA : u+a ≠ 0 := (add_pos hu ha).ne'
    have HL := ((hasDerivAt_id u).add_const a).log HA
    exact (logRegularizedDedekindZeta_differentiableAt K hu).hasDerivAt.sub HL
  have HF : Tendsto f (𝓝[>] 0)
      (𝓝 (Real.log (NumberField.dedekindZeta_residue K) - Real.log a)) := by
    have HA : Tendsto (fun u : ℝ => u+a) (𝓝[>] 0) (𝓝 a) := by
      simpa using (tendsto_id.mono_left inf_le_left : Tendsto (fun u : ℝ => u)
        (𝓝[>] 0) (𝓝 0)).add_const a
    exact (tendsto_logRegularizedDedekindZeta K).sub (HA.log ha.ne')
  have HI : ∀ᶠ u : ℝ in 𝓝[>] 0, |f h-f u| ≤ C*|h-u| := by
    filter_upwards [self_mem_nhdsWithin,
      (show Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) from tendsto_id.mono_left inf_le_left).eventually_lt_const hB]
      with u hu huB
    have HM := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun u (hu : u ∈ Ioc (0:ℝ) B) => (HD u hu.1).differentiableAt)
      (fun u hu => by simpa only [(HD u hu.1).deriv, Real.norm_eq_abs] using H u hu)
      (convex_Ioc (0:ℝ) B) ⟨hu,huB.le⟩ ⟨hh,hhB⟩
    simpa only [Real.norm_eq_abs] using HM
  have Hleft := ((tendsto_const_nhds (x := f h)).sub HF).abs
  have Hright : Tendsto (fun u : ℝ => C*|h-u|) (𝓝[>] 0) (𝓝 (C*h)) := by
    have HA := ((tendsto_const_nhds (x := h)).sub
      (tendsto_id.mono_left inf_le_left : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0))).abs
    simpa only [sub_zero,abs_of_pos hh,id_eq] using HA.const_mul C
  have Hlim := le_of_tendsto_of_tendsto Hleft Hright HI
  dsimp only [f] at Hlim
  rw [Real.log_div (add_pos hh ha).ne' ha.ne']
  convert Hlim using 1
  congr 1
  ring

 

theorem residue_comparison_remove_pole (K : Type*) [Field K] [NumberField K]
    {B C a : ℝ} (hB : 0 < B) (ha : 0 < a)
    (H : ∀ h ∈ Ioc (0:ℝ) B,
      |deriv (logRegularizedDedekindZeta K) h - 1/(h+a)| ≤ C)
    {h : ℝ} (hh : 0 < h) (hhB : h ≤ B) :
    Real.exp (-C*h)*NumberField.dedekindZeta_residue K*((h+a)/a) ≤
        regularizedDedekindZeta K h ∧
      regularizedDedekindZeta K h ≤
        Real.exp (C*h)*NumberField.dedekindZeta_residue K*((h+a)/a) := by
  have HL := residue_log_comparison_remove_pole K hB ha H hh hhB
  have Htwo := abs_le.mp HL
  have hreg := regularizedDedekindZeta_pos K hh
  have hk := NumberField.dedekindZeta_residue_pos K
  have hfactor : 0 < (h+a)/a := div_pos (add_pos hh ha) ha
  constructor
  · have E := Real.exp_le_exp.mpr (show -C*h+Real.log (NumberField.dedekindZeta_residue K)+
        Real.log ((h+a)/a) ≤ Real.log (regularizedDedekindZeta K h) by
      have hhlo := Htwo.1
      change -(C*h) ≤ Real.log (regularizedDedekindZeta K h)-_-_ at hhlo
      linarith)
    simpa only [Real.exp_add,Real.exp_log hk,Real.exp_log hreg,Real.exp_log hfactor] using E
  · have E := Real.exp_le_exp.mpr (show Real.log (regularizedDedekindZeta K h) ≤
        C*h+Real.log (NumberField.dedekindZeta_residue K)+Real.log ((h+a)/a) by
      have hhhi := Htwo.2
      change Real.log (regularizedDedekindZeta K h)-_-_ ≤ C*h at hhhi
      linarith)
    simpa only [Real.exp_add,Real.exp_log hk,Real.exp_log hreg,Real.exp_log hfactor] using E

end PrimeDegreePackets

open Filter Set Topology Module
namespace PrimeDegreePackets.HeckeMellin
open AnalyticGrowth

 

theorem dedekind_residue_dichotomy (d : ℕ) :
    ∃ C A : ℝ, 0 < C ∧ 1 ≤ A ∧
      ∀ {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyReal K],
      ∀ (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
        (_hodd : Odd (finrank ℚ K)),
      C < Real.log |(NumberField.discr K : ℝ)| →
      (∀ h ∈ Ioc (0:ℝ) (4 / Real.log |(NumberField.discr K : ℝ)|),
        A⁻¹ * NumberField.dedekindZeta_residue K ≤ regularizedDedekindZeta K h ∧
        regularizedDedekindZeta K h ≤ A * NumberField.dedekindZeta_residue K) ∨
      (∃ β : ℝ, 1-1/(4*Real.log |(NumberField.discr K : ℝ)|) ≤ β ∧ β < 1 ∧
        completedThetaXi σ hn β = 0 ∧ zeroMultiplicity (completedThetaXi σ hn) β = 1 ∧
        ∀ h ∈ Ioc (0:ℝ) (4 / Real.log |(NumberField.discr K : ℝ)|),
          A⁻¹ * NumberField.dedekindZeta_residue K * ((1+h-β)/(1-β)) ≤
              regularizedDedekindZeta K h ∧
          regularizedDedekindZeta K h ≤
            A * NumberField.dedekindZeta_residue K * ((1+h-β)/(1-β))) := by
  obtain ⟨C,M,hC,hM,H⟩ := dedekind_regularized_deriv_dichotomy d
  refine ⟨C,Real.exp (4*M),hC,Real.one_le_exp (by positivity),?_⟩
  intro K _ _ _ σ hn hodd hL
  have hLp : 0 < Real.log |(NumberField.discr K : ℝ)| := hC.trans hL
  have hbound (h : ℝ) (hh : h ∈ Ioc (0:ℝ) (4/Real.log |(NumberField.discr K : ℝ)|)) :
      M*Real.log |(NumberField.discr K : ℝ)| *h ≤ 4*M := by
    have HH := (le_div_iff₀ hLp).mp hh.2
    nlinarith only [mul_le_mul_of_nonneg_left HH hM.le]
  have hlow (h : ℝ) (hh : h ∈ Ioc (0:ℝ) (4/Real.log |(NumberField.discr K : ℝ)|)) :
      (Real.exp (4*M))⁻¹ ≤ Real.exp (-(M*Real.log |(NumberField.discr K : ℝ)|)*h) := by
    rw [← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith only [hbound h hh]
  have hupp (h : ℝ) (hh : h ∈ Ioc (0:ℝ) (4/Real.log |(NumberField.discr K : ℝ)|)) :
      Real.exp ((M*Real.log |(NumberField.discr K : ℝ)|)*h) ≤ Real.exp (4*M) :=
    Real.exp_le_exp.mpr (hbound h hh)
  have hk := (NumberField.dedekindZeta_residue_pos K).le
  rcases H σ hn hodd hL with Hordinary | ⟨β,hβbox,hβ,hzero,hsimple,Hex⟩
  · left
    intro h hh
    have HR := residue_comparison_of_deriv_bound K (by positivity) Hordinary hh.1 hh.2
    exact ⟨(mul_le_mul_of_nonneg_right (hlow h hh) hk).trans HR.1,
      HR.2.trans (mul_le_mul_of_nonneg_right (hupp h hh) hk)⟩
  · right
    refine ⟨β,hβbox,hβ,hzero,hsimple,?_⟩
    intro h hh
    have HE : 1+h-β = h+(1-β) := by ring
    have Hder : ∀ u ∈ Ioc (0:ℝ) (4/Real.log |(NumberField.discr K : ℝ)|),
        |deriv (logRegularizedDedekindZeta K) u - 1/(u+(1-β))| ≤
          M*Real.log |(NumberField.discr K : ℝ)| := by
      intro u hu
      convert Hex u hu using 1
      congr 2
      ring
    have HR := residue_comparison_remove_pole K (by positivity) (by linarith : 0 < 1-β)
      Hder hh.1 hh.2
    rw [← HE] at HR
    have hp : 0 ≤ (1+h-β)/(1-β) := div_nonneg (by linarith [hh.1]) (by linarith)
    exact ⟨(mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hlow h hh) hk) hp).trans HR.1,
      HR.2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hupp h hh) hk) hp)⟩

end PrimeDegreePackets.HeckeMellin


namespace PrimeDegreePackets
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

 

def anchorNormalize (ν : Measure β) (J : Set β) : Measure β := (ν J)⁻¹ • ν

lemma anchorNormalize_anchor (ν : Measure β) [IsFiniteMeasure ν]
    (J : Set β) (hJ : ν J ≠ 0) : anchorNormalize ν J J = 1 := by
  exact ENNReal.inv_mul_cancel hJ (measure_ne_top ν J)

lemma anchorNormalize_finite (ν : Measure β) [IsFiniteMeasure ν]
    (J : Set β) (hJ : ν J ≠ 0) : IsFiniteMeasure (anchorNormalize ν J) := by
  constructor
  change (ν J)⁻¹ * ν univ < ∞
  exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hJ))
    (measure_lt_top ν univ)

 

theorem anchorNormalize_restrict (p q : Measure β) [IsFiniteMeasure p] [IsFiniteMeasure q]
    {V J : Set β} (hJ : MeasurableSet J) (hJV : J ⊆ V)
    (hrel : q V • p = q.restrict V) (hqJ : q J ≠ 0) :
    p J ≠ 0 ∧ anchorNormalize p J = (anchorNormalize q J).restrict V := by
  have hm : q V * p J = q J := by
    have H := congrArg (fun ν : Measure β => ν J) hrel
    simpa only [Measure.smul_apply,smul_eq_mul,Measure.restrict_apply hJ,
      inter_eq_left.mpr hJV] using H
  have hpJ : p J ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hm
    exact hqJ hm.symm
  have he : (q J)⁻¹ * q V = (p J)⁻¹ := by
    rw [←hm,ENNReal.mul_inv (Or.inr (measure_ne_top p J))
      (Or.inl (measure_ne_top q V))]
    rw [mul_right_comm,ENNReal.inv_mul_cancel
      (ne_zero_of_lt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hqJ) (measure_mono hJV)))
      (measure_ne_top q V),one_mul]
  refine ⟨hpJ,?_⟩
  unfold anchorNormalize
  rw [Measure.restrict_smul,←hrel,smul_smul,he]

 

theorem restricted_conditional_anchor [StandardBorelSpace β] [Nonempty β]
    (ρ : Measure (α × β)) [IsFiniteMeasure ρ]
    {U : Set α} {V J : Set β} (hU : MeasurableSet U)
    (hV : MeasurableSet V) (hJ : MeasurableSet J) (hJV : J ⊆ V) :
    ∀ᵐ a ∂ρ.fst.restrict U, ρ.condKernel a J ≠ 0 →
      (ρ.restrict (U ×ˢ V)).condKernel a J ≠ 0 ∧
      anchorNormalize ((ρ.restrict (U ×ˢ V)).condKernel a) J =
        (anchorNormalize (ρ.condKernel a) J).restrict V := by
  filter_upwards [restricted_conditional_kernel ρ hU hV] with a ha
  exact anchorNormalize_restrict _ _ hJ hJV ha

end PrimeDegreePackets
end
end

end OAI
