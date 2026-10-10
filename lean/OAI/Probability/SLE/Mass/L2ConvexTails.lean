import OAI.Probability.SLE.Mass.SimultaneousConvexTails
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

namespace OAI

/-! A single deterministic sequence of finite convex tail combinations
for a countable family of uniformly L²-bounded random variables. Both
L² convergence and simultaneous almost-sure convergence are obtained. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace SLEExactGauge

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

lemma ae_tendsto_Lp_of_summable_errors {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : ℕ → Lp E p P) (x : Lp E p P)
    (h : Summable (fun n => ‖u n-x‖)) :
    ∀ᵐ ω ∂P, Tendsto (fun n => u n ω) atTop (𝓝 (x ω)) := by
  have hsum : ∑' n, eLpNorm (fun ω => (u n-x) ω) p P ≠ ⊤ := by
    simpa only [← Lp.enorm_def] using
      (tsum_enorm_ne_top_iff_summable_norm.mpr h)
  have hae := summable_norm_of_tsum_eLpNorm_ne_top (show 1 ≤ p from Fact.out) hsum
  have heq : ∀ᵐ ω ∂P, ∀ n, (u n-x) ω = u n ω-x ω :=
    ae_all_iff.mpr (fun n => Lp.coeFn_sub (u n) x)
  filter_upwards [hae,heq] with ω hω heω
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [heω] using hω.tendsto_atTop_zero

lemma ae_coeFn_weighted_sum (s : Finset ℕ) (w : ℕ → ℝ) (u : ℕ → Lp ℝ 2 P) :
    ∀ᵐ ω ∂P, (∑ i ∈ s, w i • u i) ω = ∑ i ∈ s, w i * u i ω := by
  have hs := (Lp.coeFn_finsetSum s (fun i => w i • u i)).trans
    (eventuallyEq_sum (fun i _ => Lp.coeFn_smul (w i) (u i)))
  filter_upwards [hs] with ω hω
  simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul] using hω

theorem exists_L2_convex_tail_limit (u : ℕ → ℕ → Lp ℝ 2 P)
    (hbound : ∀ j, ∃ B : ℝ, ∀ n, ‖u n j‖ ≤ B) :
    ∃ x : ℕ → Lp ℝ 2 P, ∃ s : ℕ → Finset ℕ, ∃ w : ℕ → ℕ → ℝ,
      (∀ n i, i ∈ s n → 0 ≤ w n i) ∧
      (∀ n, ∑ i ∈ s n, w n i = 1) ∧
      (∀ j, Tendsto (fun n => ∑ i ∈ s n, w n i • u (n+i) j) atTop (𝓝 (x j))) ∧
      (∀ᵐ ω ∂P, ∀ j,
        Tendsto (fun n => ∑ i ∈ s n, w n i * u (n+i) j ω) atTop (𝓝 (x j ω))) := by
  obtain ⟨x,s,w,hw,hs,hsum,hconv⟩ :=
    exists_simultaneous_convex_tail_combinations u hbound
  refine ⟨x,s,w,hw,hs,hconv,ae_all_iff.mpr (fun j => ?_)⟩
  have hae := ae_tendsto_Lp_of_summable_errors
    (fun n => ∑ i ∈ s n, w n i • u (n+i) j) (x j) (hsum j)
  have heq : ∀ᵐ ω ∂P, ∀ n,
      (∑ i ∈ s n, w n i • u (n+i) j) ω = ∑ i ∈ s n, w n i * u (n+i) j ω :=
    ae_all_iff.mpr (fun n => ae_coeFn_weighted_sum (s n) (w n) (fun i => u (n+i) j))
  filter_upwards [hae,heq] with ω hω heω
  simpa only [heω] using hω

/-- The same extraction stated for actual random variables, rather than
chosen representatives of their L² classes. -/
theorem exists_randomVariable_convex_tail_limit (f : ℕ → ℕ → Ω → ℝ)
    (hf : ∀ n j, MemLp (f n j) 2 P)
    (hbound : ∀ j, ∃ B : ℝ, ∀ n, ‖(hf n j).toLp (f n j)‖ ≤ B) :
    ∃ x : ℕ → Lp ℝ 2 P, ∃ s : ℕ → Finset ℕ, ∃ w : ℕ → ℕ → ℝ,
      (∀ n i, i ∈ s n → 0 ≤ w n i) ∧
      (∀ n, ∑ i ∈ s n, w n i = 1) ∧
      (∀ j, Tendsto (fun n => ∑ i ∈ s n, w n i • (hf (n+i) j).toLp (f (n+i) j))
        atTop (𝓝 (x j))) ∧
      (∀ᵐ ω ∂P, ∀ j,
        Tendsto (fun n => ∑ i ∈ s n, w n i * f (n+i) j ω) atTop (𝓝 (x j ω))) := by
  let u (n j : ℕ) : Lp ℝ 2 P := (hf n j).toLp (f n j)
  obtain ⟨x,s,w,hw,hs,hconv,hae⟩ := exists_L2_convex_tail_limit u hbound
  refine ⟨x,s,w,hw,hs,hconv,?_⟩
  have heq : ∀ᵐ ω ∂P, ∀ n j, u n j ω = f n j ω :=
    ae_all_iff.mpr (fun n => ae_all_iff.mpr (fun j => (hf n j).coeFn_toLp))
  filter_upwards [hae,heq] with ω hω heω
  simpa only [heω] using hω

end SLEExactGauge

end

end OAI
