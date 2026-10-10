import OAI.Combinatorics.MatchingEntropy.MatchingCovariance

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def binaryEntropy (x : E → ℝ) : ℝ := entropy x + entropy (fun e => 1 - x e)

def separableLower (x : E → ℝ) : ℝ := entropy x - 3 * entropy (fun e => 1 - x e)

def structuralBase (k : ℕ) : ℝ :=
  if k = 1 then 1 else (k : ℝ) * (1 - 1 / (k : ℝ)) ^ (3 * (k - 1))

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem continuous_separableLower : Continuous (separableLower (E := E)) := by
  exact continuous_entropy.sub (continuous_const.mul (continuous_entropy.comp (by fun_prop)))

def separableLineD (x v : E → ℝ) (t : ℝ) : ℝ :=
  entropyLineD x v t - 3 * entropyLineD (fun e => 1-x e) (fun e => -v e) t

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem separable_line_eventually_hasDerivAt (x v : E → ℝ)
    (hzero : ∀ e, x e = 0 → v e = 0) (hone : ∀ e, x e = 1 → v e = 0) :
    ∀ᶠ t : ℝ in 𝓝 0,
      HasDerivAt (fun t => separableLower (fun e => x e+t*v e))
        (separableLineD x v t) t := by
  have hbar : ∀ e, 1-x e=0 → -v e=0 := by
    intro e he
    rw [hone e (by linarith), neg_zero]
  filter_upwards [entropy_line_eventually_hasDerivAt x v hzero,
    entropy_line_eventually_hasDerivAt (fun e => 1-x e) (fun e => -v e) hbar]
    with t ht hb
  have he : (fun t => separableLower (fun e => x e+t*v e)) =
      (fun t => entropy (fun e => x e+t*v e) -
        3 * entropy (fun e => (1-x e)+t*(-v e))) := by
    funext t
    unfold separableLower
    congr 2
    congr 1
    funext e
    ring
  rw [he]
  exact ht.sub (hb.const_mul 3)

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem separableLineD_hasDerivAt (x v : E → ℝ)
    (hzero : ∀ e, x e = 0 → v e = 0) (hone : ∀ e, x e = 1 → v e = 0) :
    HasDerivAt (separableLineD x v)
      (-(∑ e, (v e)^2/x e) + 3*(∑ e, (v e)^2/(1-x e))) 0 := by
  have hbar : ∀ e, 1-x e=0 → -v e=0 := by
    intro e he
    rw [hone e (by linarith), neg_zero]
  have hd := (entropyLineD_hasDerivAt x v hzero).sub
    ((entropyLineD_hasDerivAt (fun e => 1-x e) (fun e => -v e) hbar).const_mul 3)
  exact hd.congr_deriv (by simp only [neg_sq]; ring)

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem separable_second_variation {A : Type uA} [Fintype A]
    (x v : E → ℝ) (hzero : ∀ e, x e=0 → v e=0) (hone : ∀ e, x e=1 → v e=0)
    {p : A → ℝ} (hp : p ∈ probabilitySimplex A) (a : A → ℝ)
    (hcenter : ∑ i, p i*a i=0) (c₀ c₁ : ℝ)
    (hlocal : IsLocalMax (fun t => separableLower (fun e => x e+t*v e) +
      c₀+t*c₁+t^2*(∑ i, p i*(a i)^2)-Real.log (partition p a t)) 0) :
    -(∑ e, (v e)^2/x e) + 3*(∑ e, (v e)^2/(1-x e)) +
      (∑ i, p i*(a i)^2) ≤ 0 := by
  have hf := separable_line_eventually_hasDerivAt x v hzero hone
  have hg : ∀ᶠ t : ℝ in 𝓝 0, HasDerivAt (fun t => Real.log (partition p a t))
      (partition (fun i => p i*a i) a t / partition p a t) t :=
    Filter.Eventually.of_forall (logPartition_hasDerivAt hp a)
  have hd := second_deriv_quadratic_adjustment (c₀ := c₀) (c₁ := c₁)
    (v := ∑ i, p i*(a i)^2) hf hg (separableLineD_hasDerivAt x v hzero hone)
    (logPartition_second hp a)
  have hc : ContinuousAt (fun t => separableLower (fun e => x e+t*v e) +
      c₀+t*c₁+t^2*(∑ i, p i*(a i)^2)-Real.log (partition p a t)) 0 := by
    apply ContinuousAt.sub
    · apply ContinuousAt.add
      · apply ContinuousAt.add
        · exact hf.self_of_nhds.continuousAt.add_const c₀
        · fun_prop
      · fun_prop
    · exact hg.self_of_nhds.continuousAt
  have hh := second_deriv_nonpos_of_local_max hlocal hc
  rw [hd.deriv, hcenter] at hh
  nlinarith

omit [Fintype V] [DecidableEq V] in
theorem mean_score_one (G : LooplessGraph V E) {p : G.Matching → ℝ}
    (hp : p ∈ probabilitySimplex G.Matching) (a : G.Matching → ℝ)
    (hcenter : ∑ M, p M*a M=0) :
    ∀ e, G.mean p e=1 → G.mean (fun M => p M*a M) e=0 := by
  intro e he
  have hz : ∑ M, p M*(1-G.indicator M e)=0 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hp.2]
    change 1-G.mean p e=0
    rw [he, sub_self]
  have hterms : ∀ M, p M*(1-G.indicator M e)=0 := by
    exact fun M => (Finset.sum_eq_zero_iff_of_nonneg
      (fun M (_ : M ∈ Finset.univ) =>
        mul_nonneg (hp.1 M) (sub_nonneg.mpr (G.indicator_le_one M e)))).mp hz M (by simp)
  calc
    _ = ∑ M, p M*a M := by
      apply Finset.sum_congr rfl
      intro M _
      have hh := hterms M
      have hh' : a M*(p M*(1-G.indicator M e))=0 := by rw [hh, mul_zero]
      nlinarith [hh']
    _ = 0 := hcenter

omit [Fintype V] [DecidableEq V] in

theorem matching_separable_second_variation (G : LooplessGraph V E) {x : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws x)
    (hopt : entropy p=maxMatchingEntropy G x)
    (hmax : ∀ y ∈ G.polytope, separableLower y-maxMatchingEntropy G y ≤
      separableLower x-maxMatchingEntropy G x)
    (u : E → ℝ) (c : ℝ) (hcenter : ∑ M, p M*linearScore G u c M=0) :
    -(∑ e, (G.mean (fun M => p M*linearScore G u c M) e)^2/x e) +
      3*(∑ e, (G.mean (fun M => p M*linearScore G u c M) e)^2/(1-x e)) +
      (∑ M, p M*(linearScore G u c M)^2) ≤ 0 := by
  let a := linearScore G u c
  let v := G.mean (fun M => p M*a M)
  let c₀ := ∑ M, p M*Real.log (p M)
  let c₁ := ∑ M, (p M*a M)*Real.log (p M)
  have hzero : ∀ e, x e=0 → v e=0 := by
    rw [← hp.2]
    exact mean_score_support G hp.1 a
  have hone : ∀ e, x e=1 → v e=0 := by
    rw [← hp.2]
    exact mean_score_one G hp.1 a hcenter
  apply separable_second_variation x v hzero hone hp.1 a hcenter c₀ c₁
  filter_upwards [score_law_eventually_simplex hp.1 a hcenter] with t ht
  let r := fun M => p M+t*(p M*a M)
  have hr : r ∈ probabilitySimplex G.Matching := ht
  have hrmean : G.mean r=fun e => x e+t*v e := by
    change G.meanLinear (p+t • (fun M => p M*a M)) = _
    rw [map_add, map_smul]
    change G.mean p+t • v = _
    rw [hp.2]
    rfl
  have hdual := matching_entropy_dual_bound G hp hopt hr
    (fun M hM => by dsimp [r]; simp [hM]) u c t
  have hscore : (∑ M, r M*a M)=t*(∑ M, p M*(a M)^2) := by
    dsimp [r]
    simp_rw [add_mul, mul_assoc t, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hcenter, zero_add]
    congr 1
    apply Finset.sum_congr rfl
    intro M _
    ring
  have hlog : (∑ M, r M*Real.log (p M))=c₀+t*c₁ := by
    dsimp [r, c₀, c₁]
    simp_rw [add_mul, mul_assoc t, Finset.sum_add_distrib, ← Finset.mul_sum]
  change maxMatchingEntropy G (G.mean r) ≤
    Real.log (partition p a t) - (∑ M, r M*Real.log (p M)) - t*(∑ M, r M*a M) at hdual
  rw [hlog, hscore] at hdual
  have hmaxr := hmax (G.mean r) (G.mean_mem_polytope hr)
  have hpart := partition_zero hp.1 a
  simp only [zero_mul, zero_pow (by omega : 2 ≠ 0), add_zero, hpart,
    Real.log_one, sub_zero]
  rw [← hopt, entropy_eq p] at hmaxr
  rw [← hrmean]
  dsimp only [c₀] at *
  nlinarith

end MatchingEntropyBounds

end

end OAI
