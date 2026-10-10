import OAI.NumberTheory.JointDickman.Amplification.BinMarginalInput

namespace OAI

/-! # Extracting finite-state probabilities from generating values -/
namespace JointDickman
open Finset Filter
open scoped Topology

theorem exists_bounded_real_count_interpolation {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (v : Fin m → ℝ) (hv : Function.Injective v) (F : (ι → Fin m) → ℝ) :
    ∃ c : (ι → Fin m) → ℝ, ∀ t : ι → Fin m,
      F t = ∑ a : ι → Fin m, c a * ∏ i, v (a i)^(t i).val := by
  obtain ⟨c,hc⟩ := exists_bounded_count_interpolation v hv (fun t => (F t : ℂ))
  refine ⟨fun a => (c a).re, fun t => ?_⟩
  have h := congrArg Complex.re (hc t)
  simpa only [Complex.ofReal_re, Complex.re_sum, ← Complex.ofReal_pow,
    ← Complex.ofReal_prod, Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero] using h

noncomputable def binStateGeneratingAverage (J : ℕ) (z : Fin (J-1) → ℝ) (A x : ℝ) : ℝ :=
  (∑ n ∈ Ioc 0 ⌊A*x⌋₊, ∏ i, z i^(canonicalBinVector J x n i).val)/(A*x)

theorem binStateDensity_interpolation {J : ℕ} (r : BinCountState J)
    (c : BinCountState J → ℝ)
    (hc : ∀ t : BinCountState J, (if t = r then (1 : ℝ) else 0) =
      ∑ a : BinCountState J, c a * ∏ i, interpolationNode (a i)^(t i).val)
    (A x : ℝ) :
    binStateDensity J A x r = ∑ a : BinCountState J,
      c a * binStateGeneratingAverage J (fun i => interpolationNode (a i)) A x := by
  classical
  have he : (((Ioc 0 ⌊A*x⌋₊).filter (fun n => canonicalBinVector J x n = r)).card : ℝ) =
      ∑ n ∈ Ioc 0 ⌊A*x⌋₊, if canonicalBinVector J x n = r then (1 : ℝ) else 0 := by
    rw [← sum_filter]
    simp
  unfold binStateDensity binStateGeneratingAverage
  rw [he]
  simp_rw [hc]
  rw [sum_comm, sum_div]
  apply sum_congr rfl
  intro a ha
  rw [← mul_sum]
  ring

theorem binStateDensity_sum (J : ℕ) (A x : ℝ) :
    (∑ r : BinCountState J, binStateDensity J A x r) = (⌊A*x⌋₊ : ℝ)/(A*x) := by
  classical
  have he := finite_state_sum (Ioc 0 ⌊A*x⌋₊) (canonicalBinVector J x) (fun _ => (1 : ℝ))
  simp only [mul_one, sum_const, nsmul_eq_mul, mul_one, Nat.card_Ioc, Nat.sub_zero] at he
  simp only [binStateDensity, ← sum_div, ← he]

theorem binStateDistribution_of_generating_limits (J : ℕ) (L : BinCountState J → ℝ)
    (hL : ∀ A : ℝ, 0 < A → ∀ a : BinCountState J,
      Tendsto (fun x => binStateGeneratingAverage J (fun i => interpolationNode (a i)) A x)
        atTop (𝓝 (L a))) :
    ∃ ν : BinCountState J → ℝ,
      (∀ r, 0 ≤ ν r) ∧ (∑ r, ν r = 1) ∧
      (∀ A : ℝ, 0 < A → ∀ r, Tendsto (fun x => binStateDensity J A x r) atTop (𝓝 (ν r))) := by
  classical
  have hc (r : BinCountState J) : ∃ c : BinCountState J → ℝ,
      ∀ t : BinCountState J, (if t = r then (1 : ℝ) else 0) =
        ∑ a : BinCountState J, c a * ∏ i, interpolationNode (a i)^(t i).val :=
    exists_bounded_real_count_interpolation (@interpolationNode (J+1)) (interpolationNode_injective _)
      (fun t => if t = r then 1 else 0)
  choose c hc using hc
  let ν (r : BinCountState J) : ℝ := ∑ a, c r a * L a
  have hν (A : ℝ) (hA : 0 < A) (r : BinCountState J) :
      Tendsto (fun x => binStateDensity J A x r) atTop (𝓝 (ν r)) := by
    have ht := tendsto_finsetSum univ (fun a _ => (hL A hA a).const_mul (c r a))
    convert ht using 1
    funext x
    exact binStateDensity_interpolation r (c r) (hc r) A x
  refine ⟨ν, ?_, ?_, hν⟩
  · intro r
    apply ge_of_tendsto (hν 1 zero_lt_one r)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_nonneg (Nat.cast_nonneg _) (by simpa using hx.le)
  · have hsum := tendsto_finsetSum univ (fun r _ => hν 1 zero_lt_one r)
    have hfloor := tendsto_nat_floor_div_atTop (R := ℝ)
    simp only [binStateDensity_sum, one_mul] at hsum
    exact tendsto_nhds_unique hsum hfloor

end JointDickman

end OAI
