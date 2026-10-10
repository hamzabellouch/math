import Mathlib

namespace OAI

universe u_1 u_2 u_3

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

namespace Problem336AdditiveD139.BrownianSublinear

variable {Ω : Type u_1} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

theorem hasLaw_unit_increment (hB : IsPreBrownianReal B P) (n : ℕ) :
    HasLaw (fun ω => B (n + 1) ω - B n ω) (gaussianReal 0 1) P := by
  convert hB.hasLaw_sub (n + 1) n using 1
  simp [Real.nndist_eq]

theorem tendsto_nat_div_ae (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => B n ω / (n : ℝ)) atTop (𝓝 0) := by
  let X : ℕ → Ω → ℝ := fun n ω => B (n + 1) ω - B n ω
  have hXlaw : ∀ n, HasLaw (X n) (gaussianReal 0 1) P :=
    fun n => hasLaw_unit_increment hB n
  have hXint : Integrable (X 0) P :=
    by simpa [X, Pi.sub_def] using (hB.integrable_eval 1).sub (hB.integrable_eval 0)
  have hXindep : iIndepFun X P := by
    simpa [X] using hB.hasIndepIncrements.nat (t := fun n : ℕ => (n : ℝ≥0))
      (fun a b h => by simpa only using (Nat.cast_le.mpr h : (a : ℝ≥0) ≤ b))
  have hXident : ∀ n, IdentDistrib (X n) (X 0) P P :=
    fun n => (hXlaw n).identDistrib (hXlaw 0)
  have hmean : ∫ ω, X 0 ω ∂P = 0 := by
    rw [(hXlaw 0).integral_eq, integral_id_gaussianReal]
  have hSLLN := strong_law_ae_real X hXint
    (fun _ _ hij => hXindep.indepFun hij) hXident
  filter_upwards [hSLLN, hB.eval_zero_ae_eq_zero] with ω hω hzero
  have hsum : ∀ n, (∑ k ∈ Finset.range n, X k ω) = B n ω := by
    intro n
    simpa [X, hzero] using Finset.sum_range_sub (fun k : ℕ => B k ω) n
  simpa only [hsum, hmean] using hω

theorem tendsto_nat_div_all_ae {I : Type u_2} [Countable I]
    (B : I → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsPreBrownianReal (B i) P) :
    ∀ᵐ ω ∂P, ∀ i, Tendsto (fun n : ℕ => B i n ω / (n : ℝ)) atTop (𝓝 0) :=
  ae_all_iff.mpr fun i => tendsto_nat_div_ae (hB i)

theorem tendsto_nat_observation_slope_all_ae {I : Type u_3} [Countable I]
    (B : I → ℝ≥0 → Ω → ℝ) (X : I → Ω → ℝ)
    (hB : ∀ i, IsPreBrownianReal (B i) P) :
    ∀ᵐ ω ∂P, ∀ i, Tendsto
      (fun n : ℕ => ((n : ℝ) * X i ω + B i n ω) / (n : ℝ))
      atTop (𝓝 (X i ω)) := by
  filter_upwards [tendsto_nat_div_all_ae B hB] with ω hω
  intro i
  have hlim : Tendsto (fun n : ℕ => X i ω + B i n ω / (n : ℝ))
      atTop (𝓝 (X i ω)) := by
    simpa using tendsto_const_nhds.add (hω i)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp

end Problem336AdditiveD139.BrownianSublinear

end

end OAI
