import OAI.Combinatorics.PerfectMatching.Calculus

namespace OAI

/-!
The second-variation inequality at a maximum of the actual entropy defect.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def entropyDefect (G : LooplessGraph V E) (m : ℝ) (y : E → ℝ) : ℝ :=
  entropyBarrier m (entropy y)-maxMatchingEntropy G y

theorem score_law_eventually_simplex {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) (hcenter : ∑ i, p i*a i = 0) :
    ∀ᶠ t : ℝ in 𝓝 0, (fun i => p i+t*(p i*a i)) ∈ probabilitySimplex ι := by
  have hh : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, 0 < 1+t*a i := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : Continuous (fun t : ℝ => 1+t*a i) := by fun_prop
    exact (isOpen_lt continuous_const hc).mem_nhds (by norm_num)
  filter_upwards [hh] with t ht
  constructor
  · intro i
    have h := mul_nonneg (hp.1 i) (ht i).le
    nlinarith
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, hp.2, hcenter]
    ring

omit [Fintype V] [DecidableEq V] in
theorem mean_score_support (G : LooplessGraph V E) {p : G.Matching → ℝ}
    (hp : p ∈ probabilitySimplex G.Matching) (a : G.Matching → ℝ) :
    ∀ e, G.mean p e = 0 → G.mean (fun M => p M*a M) e = 0 := by
  intro e he
  have hterms : ∀ M, p M*G.indicator M e = 0 := by
    have hh := (Finset.sum_eq_zero_iff_of_nonneg
      (fun M (_ : M ∈ Finset.univ) => mul_nonneg (hp.1 M) (G.indicator_nonneg M e))).mp he
    exact fun M => hh M (Finset.mem_univ M)
  apply Finset.sum_eq_zero
  intro M _
  calc
    _ = a M*(p M*G.indicator M e) := by ring
    _ = 0 := by rw [hterms, mul_zero]

omit [Fintype V] [DecidableEq V] in
/-- A maximum of the *actual* entropy defect satisfies the second-variation
inequality. The comparison uses optimizing probability laws rather than a replacement for H. -/
theorem matching_defect_second_variation (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (hopt : entropy p = maxMatchingEntropy G x) {m : ℝ} (hm : m ≠ 0)
    (hmax : ∀ y ∈ G.polytope, entropyDefect G m y ≤ entropyDefect G m x)
    (u : E → ℝ) (c : ℝ) (hcenter : ∑ M, p M*linearScore G u c M = 0) :
    (8*Real.exp (-entropy x/m)-1)*
        (∑ e, (G.mean (fun M => p M*linearScore G u c M) e)^2/x e) +
      (8*Real.exp (-entropy x/m)/m)*
        (entropyLineD x (G.mean (fun M => p M*linearScore G u c M)) 0)^2 +
      (∑ M, p M*(linearScore G u c M)^2) ≤ 0 := by
  let a := linearScore G u c
  let v := G.mean (fun M => p M*a M)
  let c₀ := ∑ M, p M*Real.log (p M)
  let c₁ := ∑ M, (p M*a M)*Real.log (p M)
  have hsupp : ∀ e, x e = 0 → v e = 0 := by
    rw [← hp.2]
    exact mean_score_support G hp.1 a
  apply entropy_second_variation x v hsupp hp.1 a hcenter hm c₀ c₁
  filter_upwards [score_law_eventually_simplex hp.1 a hcenter] with t ht
  let r := fun M => p M+t*(p M*a M)
  have hr : r ∈ probabilitySimplex G.Matching := ht
  have hrmean : G.mean r = fun e => x e+t*v e := by
    change G.meanLinear (p+t • (fun M => p M*a M)) = _
    rw [map_add, map_smul]
    change G.mean p+t • v = _
    rw [hp.2]
    rfl
  have hdual := matching_entropy_dual_bound G hp hopt hr
    (fun M hM => by dsimp [r]; simp [hM]) u c t
  have hscore : (∑ M, r M*a M) = t*(∑ M, p M*(a M)^2) := by
    dsimp [r]
    simp_rw [add_mul, mul_assoc t, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hcenter, zero_add]
    congr 1
    apply Finset.sum_congr rfl
    intro M _
    ring
  have hlog : (∑ M, r M*Real.log (p M)) = c₀+t*c₁ := by
    dsimp [r, c₀, c₁]
    simp_rw [add_mul, mul_assoc t, Finset.sum_add_distrib, ← Finset.mul_sum]
  change maxMatchingEntropy G (G.mean r) ≤
    Real.log (partition p a t) - (∑ M, r M*Real.log (p M)) - t*(∑ M, r M*a M) at hdual
  rw [hlog, hscore] at hdual
  have hmaxr := hmax (G.mean r) (G.mean_mem_polytope hr)
  dsimp only [entropyDefect] at hmaxr
  have hzero := partition_zero hp.1 a
  simp only [zero_mul, zero_pow (by omega : 2 ≠ 0), add_zero, hzero,
    Real.log_one, sub_zero]
  rw [← hopt] at hmaxr
  rw [entropy_eq p] at hmaxr
  rw [← hrmean]
  dsimp only [c₀] at *
  nlinarith

end MatchingEntropy

end

end OAI
