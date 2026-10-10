import OAI.Combinatorics.SharpThreshold.Model
import OAI.Combinatorics.SharpThreshold.RussoReindex

namespace OAI

noncomputable section

namespace Problem313

/-- Derivative of the Bernoulli mass of a single graph configuration. -/
theorem hasDerivAt_graphWeight {n : ℕ} (p : ℝ) (x : GraphConfig n) :
    HasDerivAt (fun q => graphWeight q x)
      (∑ e : GraphEdge n, (if x e = true then (1 : ℝ) else -1) *
        ∏ j ∈ Finset.univ.erase e, if x j = true then p else 1 - p) p := by
  classical
  have h (e : GraphEdge n) :
      HasDerivAt (fun q : ℝ => if x e = true then q else 1 - q)
        (if x e = true then (1 : ℝ) else -1) p := by
    split_ifs
    · exact hasDerivAt_id p
    · simpa using (hasDerivAt_id p).const_sub (1 : ℝ)
  simpa only [graphWeight, smul_eq_mul, mul_comm] using
    (HasDerivAt.fun_finsetProd (u := Finset.univ) (fun e _ => h e))

/-- The finite product rule for the graph probability polynomial. -/
theorem hasDerivAt_graphMean_raw {n : ℕ} (f : GraphConfig n → Bool) (p : ℝ) :
    HasDerivAt (fun q => graphMean q f)
      (∑ e : GraphEdge n, ∑ x : GraphConfig n,
        ((if x e = true then (1 : ℝ) else -1) *
          ∏ j ∈ Finset.univ.erase e, if x j = true then p else 1 - p) *
          boolReal (f x)) p := by
  classical
  have h := HasDerivAt.fun_sum (u := (Finset.univ : Finset (GraphConfig n)))
    (fun x _ => (hasDerivAt_graphWeight p x).mul_const (boolReal (f x)))
  simp_rw [Finset.sum_mul] at h
  rw [Finset.sum_comm] at h
  exact h

/-- The graph probability is a differentiable polynomial, without a monotonicity assumption. -/
theorem differentiable_graphMean {n : ℕ} (f : GraphConfig n → Bool) :
    Differentiable ℝ (fun p => graphMean p f) :=
  fun p => (hasDerivAt_graphMean_raw f p).differentiableAt

/-- Continuity of graph probability as a function of the edge bias. -/
theorem continuous_graphMean_russo {n : ℕ} (f : GraphConfig n → Bool) :
    Continuous (fun p => graphMean p f) :=
  (differentiable_graphMean f).continuous

/-- Every increasing property has nonnegative Boolean coordinate differences. -/
theorem increasing_update_false_true {n : ℕ} {f : GraphConfig n → Bool}
    (hf : IncreasingGraphProperty f) (x : GraphConfig n) (e : GraphEdge n) :
    f (Function.update x e false) = true → f (Function.update x e true) = true := by
  classical
  apply hf
  intro j hj
  by_cases hje : j = e
  · subst j
    simp
  · simpa [Function.update_of_ne hje] using hj

/-- For an increasing Boolean function the coordinate difference is its pivotal indicator. -/
theorem boolReal_update_sub_eq_indicator {n : ℕ} {f : GraphConfig n → Bool}
    (hf : IncreasingGraphProperty f) (x : GraphConfig n) (e : GraphEdge n) :
    boolReal (f (Function.update x e true)) - boolReal (f (Function.update x e false)) =
      if f (Function.update x e true) ≠ f (Function.update x e false) then 1 else 0 := by
  classical
  have h := increasing_update_false_true hf x e
  cases ht : f (Function.update x e true) <;>
    cases he : f (Function.update x e false) <;>
    simp_all [boolReal]

/-- Monotone pivotal influence is the expectation of the oriented coordinate difference. -/
theorem edgeInfluence_eq_sum_boolReal_sub {n : ℕ} {f : GraphConfig n → Bool}
    (hf : IncreasingGraphProperty f) (p : ℝ) (e : GraphEdge n) :
    edgeInfluence p f e = ∑ x : GraphConfig n, graphWeight p x *
      (boolReal (f (Function.update x e true)) -
        boolReal (f (Function.update x e false))) := by
  classical
  unfold edgeInfluence
  apply Finset.sum_congr rfl
  intro x _
  rw [boolReal_update_sub_eq_indicator hf]
  split_ifs <;> simp

/-- Russo--Margulis formula with pivotal total influence.
The identity is polynomial, so no restriction to biases in `[0,1]` is necessary. -/
theorem hasDerivAt_graphMean {n : ℕ} {f : GraphConfig n → Bool}
    (hf : IncreasingGraphProperty f) (p : ℝ) :
    HasDerivAt (fun q => graphMean q f) (totalInfluence p f) p := by
  classical
  convert hasDerivAt_graphMean_raw f p using 1
  unfold totalInfluence
  apply Finset.sum_congr rfl
  intro e _
  rw [edgeInfluence_eq_sum_boolReal_sub hf]
  exact (russo_sum_reindex p e (fun x => boolReal (f x))).symm

/-- Derivative form of the Russo--Margulis identity. -/
theorem deriv_graphMean {n : ℕ} {f : GraphConfig n → Bool}
    (hf : IncreasingGraphProperty f) (p : ℝ) :
    deriv (fun q => graphMean q f) p = totalInfluence p f :=
  (hasDerivAt_graphMean hf p).deriv

end Problem313

end

end OAI
