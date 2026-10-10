import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

namespace Problem336

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

theorem brownian_integer_increment_hasLaw (hB : IsPreBrownianReal B P) (n : ℕ) :
    HasLaw (fun ω => B ((n + 1 : ℕ) : ℝ≥0) ω - B n ω) (gaussianReal 0 1) P := by
  have h := hB.hasLaw_sub ((n + 1 : ℕ) : ℝ≥0) (n : ℝ≥0)
  convert h using 1
  congr 1
  apply NNReal.coe_injective
  simp

theorem brownian_integer_sublinear (hB : IsPreBrownianReal B P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => B n ω / (n : ℝ)) atTop (𝓝 0) := by
  let X : ℕ → Ω → ℝ := fun n ω => B ((n + 1 : ℕ) : ℝ≥0) ω - B n ω
  have hXlaw (n : ℕ) : HasLaw (X n) (gaussianReal 0 1) P :=
    brownian_integer_increment_hasLaw hB n
  have hXint : Integrable (X 0) P := (hXlaw 0).hasGaussianLaw.integrable
  have hXind : iIndepFun X P :=
    hB.hasIndepIncrements.nat (t := fun n : ℕ => (n : ℝ≥0))
      (fun i j hij => Nat.cast_le.mpr hij)
  have hXident (n : ℕ) : IdentDistrib (X n) (X 0) P P :=
    (hXlaw n).identDistrib (hXlaw 0)
  have hmean : ∫ ω, X 0 ω ∂P = 0 := by
    rw [(hXlaw 0).integral_eq, integral_id_gaussianReal]
  have hslln := strong_law_ae_real X hXint (fun i j hij => hXind.indepFun hij) hXident
  rw [hmean] at hslln
  filter_upwards [hslln, hB.eval_zero_ae_eq_zero] with ω hω hzero
  have hsum (n : ℕ) : (∑ i ∈ Finset.range n, X i ω) = B n ω := by
    change (∑ i ∈ Finset.range n, (B ((i + 1 : ℕ) : ℝ≥0) ω - B i ω)) = _
    rw [Finset.sum_range_sub (fun i : ℕ => B i ω), Nat.cast_zero, hzero, sub_zero]
  simpa only [hsum] using hω

theorem brownian_integer_sublinear_all {ι : Type*} [Countable ι]
    {W : ι → ℝ≥0 → Ω → ℝ} (hW : ∀ i, IsPreBrownianReal (W i) P) :
    ∀ᵐ ω ∂P, ∀ i, Tendsto (fun n : ℕ => W i n ω / (n : ℝ)) atTop (𝓝 0) :=
  ae_all_iff.mpr (fun i => brownian_integer_sublinear (hW i))

end Problem336

end

end OAI
