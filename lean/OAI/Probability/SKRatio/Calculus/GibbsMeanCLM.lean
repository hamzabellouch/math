import Mathlib
import OAI.Probability.SKRatio.FiniteChain.MeanMulVec
import OAI.Probability.SKRatio.Calculus.SignedVector

namespace OAI

section
noncomputable section
open scoped BigOperators Topology Matrix
open ContinuousLinearMap
namespace SKRatio.Calculus
open Real Set

def gibbsMeanCLM {n : ℕ} (g : Disorder n) : Observables n →L[ℝ] ℝ :=
  (∑ x : Spin n, mass g 0 x • ContinuousLinearMap.proj x)

@[simp] lemma gibbsMeanCLM_apply {n : ℕ} (g : Disorder n) (f : Observables n) :
    gibbsMeanCLM g f = FiniteLaw.mean (mass g 0) f := by
  simp [gibbsMeanCLM, FiniteLaw.mean]

lemma gibbsMean_generator {n : ℕ} (g : Disorder n) (f : Observables n) :
    gibbsMeanCLM g (generator (coupling g) f) = 0 := by
  have heq : generator (coupling g) f = (n:ℝ) • (transition g *ᵥ f - f) := by
    funext x
    exact generator_eq_transition g f x
  rw [heq, map_smul, map_sub]
  simp only [gibbsMeanCLM_apply, FiniteLaw.mean_mulVec, transition_stationary, sub_self,
    smul_zero]

lemma functional_exp_invariant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (A : E →L[ℝ] E) (T : E →L[ℝ] ℝ)
    (h : ∀ f, T (A f) = 0) (f : E) : T (NormedSpace.exp A f) = T f := by
  have hp (k : ℕ) : T ((A^(k+1)) f) = 0 := by
    rw [pow_succ', mul_apply_eq_comp, h]
  have hs := T.hasSum (exp_apply_hasSum A f)
  have eqs : (fun k : ℕ => T ((k.factorial:ℝ)⁻¹ • ((A^k) f))) =
      fun k => if k = 0 then T f else 0 := by
    funext k
    cases k with
    | zero => simp
    | succ k => simp only [map_smul, hp, smul_zero, Nat.succ_ne_zero, ↓reduceIte]
  rw [eqs] at hs
  exact hs.unique (hasSum_ite_eq 0 (T f))

theorem gibbsMean_semigroup {n : ℕ} (g : Disorder n) (t : ℝ)
    (f : Observables n) :
    FiniteLaw.mean (mass g 0) (semigroup (coupling g) t f) =
      FiniteLaw.mean (mass g 0) f := by
  simpa only [gibbsMeanCLM_apply, semigroup] using
    functional_exp_invariant (t • generatorCLM (coupling g)) (gibbsMeanCLM g)
    (fun f => by
      rw [smul_apply, map_smul]
      change t • gibbsMeanCLM g (generator (coupling g) f) = 0
      rw [gibbsMean_generator, smul_zero]) f

theorem continuousKernel_stationary {n : ℕ} (g : Disorder n) (t : ℝ) :
    mass g 0 ᵥ* continuousKernel (coupling g) t = mass g 0 := by
  funext y
  have h := gibbsMean_semigroup g t (fun z => if z = y then (1:ℝ) else 0)
  simpa only [FiniteLaw.mean, Matrix.vecMul, continuousKernel, dotProduct,
    mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq'] using h

def continuousDistance {n : ℕ} (g : Disorder n) (t : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun x : Spin n => totalVariation (continuousKernel (coupling g) t x) (mass g 0))

lemma continuousKernel_stochastic {n : ℕ} (J : Interaction n) {t : ℝ} (ht : 0 ≤ t) :
    continuousKernel J t ∈ Matrix.rowStochastic ℝ (Spin n) := by
  exact Matrix.mem_rowStochastic_iff_sum.mpr
    ⟨continuousKernel_nonneg J t ht, continuousKernel_sum J t⟩

lemma tv_le_continuousDistance {n : ℕ} (g : Disorder n) (t : ℝ) (x : Spin n) :
    totalVariation (continuousKernel (coupling g) t x) (mass g 0) ≤
      continuousDistance g t := by
  unfold continuousDistance
  exact Finset.le_sup' (fun z : Spin n =>
    totalVariation (continuousKernel (coupling g) t z) (mass g 0)) (Finset.mem_univ x)

lemma continuousDistance_nonneg {n : ℕ} (g : Disorder n) (t : ℝ) :
    0 ≤ continuousDistance g t :=
  (totalVariation_nonneg _ _).trans (tv_le_continuousDistance g t (fun _ => true))

lemma continuousDistance_le_one {n : ℕ} (g : Disorder n) {t : ℝ} (ht : 0 ≤ t) :
    continuousDistance g t ≤ 1 := by
  apply Finset.sup'_le
  intro x _
  exact totalVariation_le_one _ _ (continuousKernel_nonneg _ t ht x) (mass_nonneg g 0)
    (continuousKernel_sum _ t x) (sum_mass g 0)

lemma continuousDistance_antitone {n : ℕ} (g : Disorder n) {s t : ℝ}
    (_hs : 0 ≤ s) (hst : s ≤ t) : continuousDistance g t ≤ continuousDistance g s := by
  apply Finset.sup'_le
  intro x _
  have htime : t = s + (t-s) := by ring
  have hsum : (∑ y, continuousKernel (coupling g) s x y) = ∑ y, mass g 0 y := by
    rw [continuousKernel_sum, sum_mass]
  calc
    _ = totalVariation (continuousKernel (coupling g) s x ᵥ*
        continuousKernel (coupling g) (t-s))
        (mass g 0 ᵥ* continuousKernel (coupling g) (t-s)) := by
      rw [continuousKernel_stationary]
      conv_lhs => rw [htime, continuousKernel_add, Matrix.mul_apply_eq_vecMul]
    _ ≤ totalVariation (continuousKernel (coupling g) s x) (mass g 0) :=
      totalVariation_contract _ (continuousKernel_stochastic _ (sub_nonneg.mpr hst)) _ _ hsum
    _ ≤ _ := tv_le_continuousDistance g s x

theorem continuousDistance_smoothing {n : ℕ} (g : Disorder n) {t s : ℝ}
    (ht : 0 ≤ t) {ε V W : ℝ} (hε : 0 < ε)
    (hoverlap : continuousDistance g t ≤ 1-ε)
    (htransient : ∀ (x : Spin n) (f : Observables n), (∀ y, |f y| ≤ 1) →
      FiniteLaw.variance (continuousKernel (coupling g) t x)
        (semigroup (coupling g) s f) ≤ V)
    (hequilibrium : ∀ f : Observables n, (∀ y, |f y| ≤ 1) →
      FiniteLaw.variance (mass g 0) (semigroup (coupling g) s f) ≤ W) :
    continuousDistance g (t+s) ≤ (Real.sqrt V+Real.sqrt W)/(2*Real.sqrt ε) := by
  apply Finset.sup'_le
  intro x _
  apply FiniteLaw.totalVariation_le_of_tests
  intro f hf
  have hc := FiniteLaw.common_mass_means (continuousKernel (coupling g) t x) (mass g 0)
    (semigroup (coupling g) s f) (continuousKernel_nonneg _ t ht x) (mass_nonneg g 0)
    (continuousKernel_sum _ t x) (sum_mass g 0) hε
    ((tv_le_continuousDistance g t x).trans hoverlap)
  rw [gibbsMean_semigroup, ← semigroup_eq_kernel, ← mul_apply_eq_comp,
    ← semigroup_add, semigroup_eq_kernel] at hc
  calc
    _ ≤ (Real.sqrt (FiniteLaw.variance (continuousKernel (coupling g) t x)
        (semigroup (coupling g) s f))+
        Real.sqrt (FiniteLaw.variance (mass g 0) (semigroup (coupling g) s f))) /
        Real.sqrt ε := hc
    _ ≤ (Real.sqrt V+Real.sqrt W) / Real.sqrt ε := by
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact add_le_add (Real.sqrt_le_sqrt (htransient x f hf))
        (Real.sqrt_le_sqrt (hequilibrium f hf))
    _ = _ := by ring

lemma gradientWeight_le_two {n : ℕ} (J : Interaction n) (x : Spin n) (i : Fin n) :
    gradientWeight J x i ≤ 2 := by
  have hl : -1 < mean J x i := Real.neg_one_lt_tanh _
  have hu : mean J x i < 1 := Real.tanh_lt_one _
  unfold gradientWeight spin
  cases x i <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith

lemma weightedGradient_nonneg {n : ℕ} (J : Interaction n) (f : Observables n) (x : Spin n) :
    0 ≤ weightedGradient J f x := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (gradientWeight_pos J x i).le (sq_nonneg _))

lemma weightedGradient_le {n : ℕ} (J : Interaction n) (f : Observables n) (x : Spin n) :
    weightedGradient J f x ≤ 2*unweightedGradient f x := by
  rw [unweightedGradient, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ =>
    mul_le_mul_of_nonneg_right (gradientWeight_le_two J x i) (sq_nonneg _))

lemma halfDiff_abs_le {n : ℕ} (f : Observables n) {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) (x : Spin n) (i : Fin n) : |halfDiff i f x| ≤ B := by
  unfold halfDiff
  rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have h := (abs_sub (f (replace x i true)) (f (replace x i false))).trans
    (add_le_add (hf _) (hf _))
  linarith only [h]

lemma unweightedGradient_le_dim {n : ℕ} (f : Observables n) (hf : ∀ x, |f x| ≤ 1)
    (x : Spin n) : unweightedGradient f x ≤ n := by
  calc
    _ ≤ ∑ _i : Fin n, (1:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact (sq_le_one_iff_abs_le_one _).mpr (halfDiff_abs_le f hf x i)
    _ = _ := by simp

lemma continuous_halfDiff {n : ℕ} (i : Fin n) (F : ℝ → Observables n)
    (hF : Continuous F) (x : Spin n) : Continuous (fun t => halfDiff i (F t) x) := by
  exact (((continuous_apply _).comp hF).sub ((continuous_apply _).comp hF)).div_const 2

lemma continuous_weightedGradient {n : ℕ} (J : Interaction n) (F : ℝ → Observables n)
    (hF : Continuous F) : Continuous (fun t => weightedGradient J (F t)) := by
  apply continuous_pi
  intro x
  exact continuous_finsetSum _ (fun i _ =>
    ((continuous_halfDiff i F hF x).pow 2).const_mul (gradientWeight J x i))

def backwardEnergy {n : ℕ} (J : Interaction n) (f : Observables n)
    (x : Spin n) (T u : ℝ) : ℝ :=
  semigroup J u (weightedGradient J (semigroup J (T-u) f)) x

lemma backwardEnergy_continuous {n : ℕ} (J : Interaction n) (f : Observables n)
    (x : Spin n) (T : ℝ) : Continuous (backwardEnergy J f x T) := by
  exact (continuous_apply x).comp ((semigroup_continuous J).clm_apply
    (continuous_weightedGradient J _ (((semigroup_continuous J).comp
      (continuous_const.sub continuous_id)).clm_apply continuous_const)))

lemma backwardEnergy_nonneg {n : ℕ} (J : Interaction n) (f : Observables n)
    (x : Spin n) (T u : ℝ) (hu : 0 ≤ u) : 0 ≤ backwardEnergy J f x T u := by
  exact semigroup_nonneg J u hu _ (weightedGradient_nonneg J _) x

lemma backward_second_moment_hasDerivAt {n : ℕ} (J : Interaction n) (f : Observables n)
    (x : Spin n) (T u : ℝ) :
    HasDerivAt (fun r : ℝ => semigroup J r (fun y => (semigroup J (T-r) f y)^2) x)
      (2*backwardEnergy J f x T u) u := by
  let F : ℝ → Observables n := fun r => semigroup J (T-r) f
  have hF : HasDerivAt F (-generator J (F u)) u := by
    simpa only [Function.comp_def, sub_zero, zero_sub, neg_smul, one_smul] using
      (semigroup_apply_hasDerivAt' J f (T-u)).scomp u
        ((hasDerivAt_const u T).sub (hasDerivAt_id u))
  have hsq : HasDerivAt (fun r : ℝ => (fun y => (F r y)^2))
      (fun y => -2*F u y*generator J (F u) y) u := by
    apply hasDerivAt_pi.mpr
    intro y
    convert (hasDerivAt_pi.mp hF y).fun_pow 2 using 1
    simp only [Pi.neg_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    ring
  have H := (semigroup_hasDerivAt J u).clm_apply hsq
  have heq : (semigroup J u*generatorCLM J) (fun y => F u y^2) +
      semigroup J u (fun y => -2*F u y*generator J (F u) y) =
      (2:ℝ) • semigroup J u (weightedGradient J (F u)) := by
    rw [mul_apply_eq_comp, ← map_add, ← map_smul]
    congr 1
    funext y
    change generator J (fun y => F u y^2) y + (-2*F u y*generator J (F u) y) =
      2*weightedGradient J (F u) y
    have h := variance_density J (F u) y
    linarith only [h]
  rw [heq] at H
  exact hasDerivAt_pi.mp H x

theorem backward_variance_budget {n : ℕ} (J : Interaction n) (f : Observables n)
    (x : Spin n) (T r : ℝ) :
    FiniteLaw.variance (continuousKernel J r x) (semigroup J (T-r) f) =
      2*∫ u in (0:ℝ)..r, backwardEnergy J f x T u := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => backward_second_moment_hasDerivAt J f x T u)
    ((backwardEnergy_continuous J f x T).const_mul 2 |>.intervalIntegrable 0 r)
  rw [intervalIntegral.integral_const_mul] at hi
  rw [FiniteLaw.variance_eq _ _ (continuousKernel_sum J r x),
    ← semigroup_eq_kernel, ← semigroup_eq_kernel,
    ← mul_apply_eq_comp, ← semigroup_add]
  have heq : r+(T-r) = T := by ring
  rw [heq]
  simpa only [semigroup_zero, one_apply_eq_self, sub_zero] using hi.symm

theorem backward_energy_budget {n : ℕ} (J : Interaction n) (f : Observables n)
    (hf : ∀ y, |f y| ≤ 1) (x : Spin n) {T : ℝ} (hT : 0 ≤ T) :
    (∫ u in (0:ℝ)..T, backwardEnergy J f x T u) ≤ 1/2 := by
  have hi := backward_variance_budget J f x T T
  simp only [sub_self, semigroup_zero, one_apply_eq_self] at hi
  rw [FiniteLaw.variance_eq _ _ (continuousKernel_sum J T x), ← semigroup_eq_kernel,
    ← semigroup_eq_kernel] at hi
  have hsquares : ∀ y, f y^2 ≤ (1:ℝ) := fun y => (sq_le_one_iff_abs_le_one _).mpr (hf y)
  have hm := semigroup_mono J hT (fun y => f y^2) (fun _ => 1) hsquares x
  rw [semigroup_const] at hm
  linarith [sq_nonneg (semigroup J T f x)]

end SKRatio.Calculus

end
end

end OAI
