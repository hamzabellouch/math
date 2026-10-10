import Mathlib
import OAI.Probability.ThreeStateClauses.CompactLimits

namespace OAI

/-! Information Loss. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment

variable {α β γ : Type}

def multisetKernel (K : α → PMF β) (s : Multiset α) : PMF (Multiset β) :=
  Multiset.recOn s (PMF.pure 0)
    (fun a _ p ↦ (K a).bind (fun b ↦ p.map (Multiset.cons b))) (by
      intro a a' s p
      apply heq_of_eq
      simp only [PMF.map_bind, PMF.map_comp]
      rw [PMF.bind_comm (K a) (K a')]
      congr 1
      funext b'
      congr 1
      funext b
      congr 1
      funext t
      exact Multiset.cons_swap _ _ _)

@[simp] lemma multisetKernel_zero (K : α → PMF β) : multisetKernel K 0 = PMF.pure 0 := by
  rw [multisetKernel, Multiset.recOn_0]

@[simp] lemma multisetKernel_cons (K : α → PMF β) (a : α) (s : Multiset α) :
    multisetKernel K (a ::ₘ s) = (K a).bind (fun b ↦ (multisetKernel K s).map (Multiset.cons b)) := by
  rw [multisetKernel, Multiset.recOn_cons]
  rfl

lemma multisetKernel_iid (p : PMF α) (K : α → PMF β) (n : ℕ) :
    ((iidList p n).map (fun xs : List α ↦ (xs : Multiset α))).bind (multisetKernel K) =
      (iidList (p.bind K) n).map (fun xs : List β ↦ (xs : Multiset β)) := by
  induction n with
  | zero => simp [iidList, PMF.pure_map]
  | succ n ih =>
    simp only [iidList, PMF.map_bind, PMF.map_comp, PMF.bind_bind, PMF.bind_map]
    congr 1
    funext a
    simp only [Function.comp_def, ← Multiset.cons_coe, multisetKernel_cons]
    rw [PMF.bind_comm (iidList p n) (K a)]
    congr 1
    funext b
    rw [← PMF.map_bind]
    have hi := ih
    rw [PMF.bind_map] at hi
    dsimp only [Function.comp_def] at hi
    rw [hi, PMF.map_comp]
    rfl

lemma observationLaw_succ (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (ℓ : ℕ) (i : Spin) :
    observationLaw lam hlam offspring (ℓ+1) i = offspring.bind (fun n ↦
      (iidList ((channel lam hlam i).bind (observationLaw lam hlam offspring ℓ)) n).map
        (fun xs : List (Observation ℓ) ↦ (xs : Multiset (Observation ℓ)))) := by
  rw [observationLaw]
  congr 1
  funext n
  exact PMF.map_id _

def observationExpansion (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ) :
    (ℓ : ℕ) → Observation ℓ → PMF (Observation (ℓ+1))
  | 0, i => observationLaw lam hlam offspring 1 i
  | ℓ+1, s => multisetKernel (observationExpansion lam hlam offspring ℓ) s

lemma observationLaw_degrades (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ)
    (ℓ : ℕ) (i : Spin) :
    (observationLaw lam hlam offspring ℓ i).bind (observationExpansion lam hlam offspring ℓ) =
      observationLaw lam hlam offspring (ℓ+1) i := by
  induction ℓ generalizing i with
  | zero => exact PMF.pure_bind _ _
  | succ ℓ ih =>
    rw [observationLaw_succ, observationLaw_succ]
    change ((offspring.bind (fun n ↦ (iidList ((channel lam hlam i).bind (observationLaw lam hlam offspring ℓ)) n).map
      (fun xs : List (Observation ℓ) ↦ (xs : Multiset (Observation ℓ))))).bind
      (multisetKernel (observationExpansion lam hlam offspring ℓ))) = _
    rw [PMF.bind_bind]
    congr 1
    funext n
    rw [multisetKernel_iid]
    congr 2
    rw [PMF.bind_bind]
    congr 1
    funext j
    exact ih j

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology
namespace ThreeState.TreeClauses.Experiment
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive

lemma coord_center_abs_le_two (m : Message) (i : Spin) : |m.1 i-1| ≤ 2 :=
  abs_le.mpr ⟨by linarith [coordinate_nonneg m i], by linarith [coordinate_le_three m i]⟩

variable {α β : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Countable β] [MeasurableSpace β] [MeasurableSingletonClass β]

lemma discrete_degradation_abs (p : Spin → PMF α) (K : α → PMF β) (i : Spin) :
    (∫ b, |(discreteMessage (fun j ↦ (p j).bind K) b).1 i-1|
      ∂(discreteMarginal (fun j ↦ (p j).bind K)).toMeasure) ≤
    ∫ a, |(discreteMessage p a).1 i-1| ∂(discreteMarginal p).toMeasure := by
  let q := fun j ↦ (p j).bind K
  let g : β → ℝ := fun b ↦ if 0 ≤ (discreteMessage q b).1 i-1 then 1 else -1
  have hg (b : β) : |g b| ≤ 1 := by dsimp [g]; split_ifs <;> norm_num
  have he (b : β) : ((discreteMessage q b).1 i-1)*g b = |(discreteMessage q b).1 i-1| := by
    dsimp [g]; split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (lt_of_not_ge h)]
  have hb (z : α × β) : |((discreteMessage p z.1).1 i-1)*g z.2| ≤ 2 := by
    rw [abs_mul]
    exact (mul_le_mul (coord_center_abs_le_two _ _) (hg _) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hi := discrete_degradation_centered p K i hg
  have hid (z : α × β) : ((discreteMessage p z.1).1 i-(discreteMessage q z.2).1 i)*g z.2 =
      ((discreteMessage p z.1).1 i-1)*g z.2-|(discreteMessage q z.2).1 i-1| := by
    rw [← he]; ring
  change (∫ z : α × β, ((discreteMessage p z.1).1 i-(discreteMessage q z.2).1 i)*g z.2 ∂_) = 0 at hi
  simp_rw [hid] at hi
  rw [integral_sub (pmf_bounded_integrable _ hb)
    (pmf_bounded_integrable _ (fun z : α × β ↦ by simpa using coord_center_abs_le_two (discreteMessage q z.2) i))] at hi
  have hle : (∫ z, ((discreteMessage p z.1).1 i-1)*g z.2 ∂(kernelJoint (discreteMarginal p) K).toMeasure) ≤
      ∫ z, |(discreteMessage p z.1).1 i-1| ∂(kernelJoint (discreteMarginal p) K).toMeasure :=
    integral_mono (μ := (kernelJoint (discreteMarginal p) K).toMeasure)
    (pmf_bounded_integrable _ hb)
    (pmf_bounded_integrable _ (fun z : α × β ↦ by simpa using coord_center_abs_le_two (discreteMessage p z.1) i))
    (fun z : α × β ↦ (le_abs_self _).trans (by
      rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hg _)))
  rw [integral_kernelJoint_fst (f := fun a ↦ |(discreteMessage p a).1 i-1|)] at hle
  rw [integral_kernelJoint_snd (f := fun b ↦ |(discreteMessage q b).1 i-1|), ← discreteMarginal_bind] at hi
  change _ - (∫ b, |(discreteMessage q b).1 i-1| ∂(discreteMarginal q).toMeasure) = 0 at hi
  linarith

lemma discrete_degradation_tv (p : Spin → PMF α) (K : α → PMF β) :
    (∫ m, tvMessage m ∂(discreteProbability (fun i ↦ (p i).bind K)).toMeasure) ≤
      ∫ m, tvMessage m ∂(discreteProbability p).toMeasure := by
  rw [integral_discreteProbability _ continuous_tvMessage.measurable,
    integral_discreteProbability _ continuous_tvMessage.measurable]
  unfold tvMessage
  rw [integral_div, integral_div, integral_avg_measure, integral_avg_measure]
  · exact div_le_div_of_nonneg_right (by
      dsimp [avg]
      linarith [discrete_degradation_abs p K 0, discrete_degradation_abs p K 1,
        discrete_degradation_abs p K 2]) (by norm_num)
  all_goals intro i; exact pmf_bounded_integrable _ (fun a ↦ by simpa using coord_center_abs_le_two _ i)

lemma advantage_antitone (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ) :
    Antitone (advantage lam hlam offspring) := by
  apply antitone_nat_of_succ_le
  intro ℓ
  simp only [advantage_eq_integral]
  have h := discrete_degradation_tv (observationLaw lam hlam offspring ℓ)
    (observationExpansion lam hlam offspring ℓ)
  simpa only [observationLaw_degrades] using h

lemma advantage_tendsto (lam : ℝ) (hlam : Admissible lam) (offspring : PMF ℕ) :
    Tendsto (advantage lam hlam offspring) atTop (𝓝 (⨅ ℓ, advantage lam hlam offspring ℓ)) :=
  tendsto_atTop_ciInf (advantage_antitone lam hlam offspring)
    ⟨0, by rintro _ ⟨ℓ,rfl⟩; exact advantage_nonneg lam hlam offspring ℓ⟩

end ThreeState.TreeClauses.Experiment

end 

noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace ThreeState.TreeClauses.Experiment
open ThreeState.TreeClauses.Radial ThreeState.TreeClauses.Positive

variable {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

lemma integral_discreteMarginal (p : Spin → PMF α) {f : α → ℝ} {B : ℝ} (hB : ∀ a, |f a| ≤ B) :
    (∫ a, f a ∂(discreteMarginal p).toMeasure) =
      ((∫ a, f a ∂(p 0).toMeasure)+(∫ a, f a ∂(p 1).toMeasure)+(∫ a, f a ∂(p 2).toMeasure))/3 := by
  rw [discreteMarginal, integral_pmf_bind _ _ hB, PMF.integral_eq_sum]
  simp only [Fin.sum_univ_three, uniformSpin_apply, ENNReal.toReal_div,
    ENNReal.toReal_one, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

lemma coord_sq_le_tv (m : Message) (i : Spin) : (m.1 i-1)^2 ≤ 12*tvMessage m := by
  have h := mul_le_mul_of_nonneg_left (coord_center_abs_le_two m i) (abs_nonneg (m.1 i-1))
  rw [← sq, sq_abs] at h
  have hs : |m.1 i-1| ≤ ∑ j : Spin, |m.1 j-1| :=
    Finset.single_le_sum (f := fun j : Spin ↦ |m.1 j-1|) (fun j _ ↦ abs_nonneg _) (Finset.mem_univ i)
  simp only [Fin.sum_univ_three] at hs
  dsimp [tvMessage, avg]
  linarith

omit [Countable α] [MeasurableSingletonClass α] in
lemma integral_scaled_square (μ : Measure α) {v f : α → ℝ} (r : ℝ)
    (hv : Integrable (fun a ↦ v a^2) μ) (hf : Integrable (fun a ↦ f a^2) μ)
    (hc : Integrable (fun a ↦ v a*f a) μ) :
    (∫ a, (v a-r*f a)^2 ∂μ) = (∫ a, v a^2 ∂μ)-2*r*(∫ a, v a*f a ∂μ)+r^2*(∫ a, f a^2 ∂μ) := by
  have he (a : α) : (v a-r*f a)^2 = (v a^2-(2*r)*(v a*f a))+r^2*f a^2 := by ring
  simp_rw [he]
  rw [integral_add (f := fun a ↦ v a^2-(2*r)*(v a*f a)) (g := fun a ↦ r^2*f a^2)
    (hv.sub (hc.const_mul (2*r))) (hf.const_mul (r^2))]
  rw [integral_sub hv (hc.const_mul (2*r))]
  rw [integral_const_mul, integral_const_mul]

lemma estimator_tv_lower (p : Spin → PMF α) {f : α → ℝ} {B C : ℝ}
    (hB : ∀ a, |f a| ≤ B) (hC : 0 < C)
    (hzero : (∫ a, f a ∂(discreteMarginal p).toMeasure) = 0)
    (hroot : (∫ a, f a ∂(p 0).toMeasure) = 2)
    (hsecond : (∫ a, f a^2 ∂(discreteMarginal p).toMeasure) ≤ C) :
    1/(3*C) ≤ ∫ m, tvMessage m ∂(discreteProbability p).toMeasure := by
  let v : α → ℝ := fun a ↦ (discreteMessage p a).1 0-1
  have hv (a : α) : |v a| ≤ 2 := coord_center_abs_le_two _ _
  have hf₂ := pmf_bounded_integrable (discreteMarginal p) (fun a ↦ show |f a^2| ≤ B^2 by
    rw [abs_of_nonneg (sq_nonneg _)]; nlinarith [hB a, abs_nonneg (f a), sq_abs (f a)])
  have hv₂ := pmf_bounded_integrable (discreteMarginal p) (fun a ↦ show |v a^2| ≤ (2:ℝ)^2 by
    rw [abs_of_nonneg (sq_nonneg _)]; nlinarith [hv a, abs_nonneg (v a), sq_abs (v a)])
  have hvf := pmf_bounded_integrable (discreteMarginal p) (fun a ↦ show |v a*f a| ≤ 2*B by
    rw [abs_mul]; exact mul_le_mul (hv a) (hB a) (abs_nonneg _) (by norm_num))
  have hcross : (∫ a, v a*f a ∂(discreteMarginal p).toMeasure) = 2 := by
    have he (a : α) : v a*f a = (discreteMessage p a).1 0*f a-f a := by dsimp [v]; ring
    simp_rw [he]
    rw [integral_sub (pmf_bounded_integrable _ (fun a ↦ show |(discreteMessage p a).1 0*f a| ≤ 3*B by
      rw [abs_mul, abs_of_nonneg (coordinate_nonneg _ _)]; exact mul_le_mul (coordinate_le_three _ _) (hB a) (abs_nonneg _) (by norm_num)))
      (pmf_bounded_integrable _ hB), discrete_bayes_integral p 0 hB, hroot, hzero, sub_zero]
  let r := 2/C
  have hr : r*C = 2 := div_mul_cancel₀ 2 hC.ne'
  have h := MeasureTheory.integral_nonneg (μ := (discreteMarginal p).toMeasure)
    (f := fun a ↦ (v a-r*f a)^2) (fun _ ↦ sq_nonneg _)
  rw [integral_scaled_square _ r hv₂ hf₂ hvf, hcross] at h
  have hb := mul_le_mul_of_nonneg_left hsecond (sq_nonneg r)
  have hr2 : r^2*C = 2*r := by
    have hh := congrArg (fun x : ℝ ↦ r*x) hr
    nlinarith only [hh]
  have hD : 4 ≤ C*(∫ a, v a^2 ∂(discreteMarginal p).toMeasure) := by
    have hs : 2*r ≤ ∫ a, v a^2 ∂(discreteMarginal p).toMeasure := by
      nlinarith only [h, hb, hr2]
    have hh := mul_le_mul_of_nonneg_left hs hC.le
    nlinarith only [hh, hr]
  have hT := integral_mono hv₂ (pmf_bounded_integrable (discreteMarginal p)
    (fun a ↦ show |12*tvMessage (discreteMessage p a)| ≤ 12 by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 12), abs_of_nonneg (tvMessage_nonneg _)];
      nlinarith [tvMessage_le_one (discreteMessage p a)]))
    (fun a ↦ coord_sq_le_tv (discreteMessage p a) 0)
  rw [integral_const_mul, ← integral_discreteProbability p continuous_tvMessage.measurable] at hT
  apply (div_le_iff₀ (by positivity : 0 < 3*C)).2
  have hh := mul_le_mul_of_nonneg_left hT hC.le
  nlinarith only [hD, hh]

end ThreeState.TreeClauses.Experiment

end

end OAI
