import OAI.Combinatorics.PerfectMatching.Entropy

namespace OAI

/-!
Support and first-order identities for entropy-maximizing matching laws.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

/-- Concavity of actual finite-law Shannon entropy. -/
theorem entropy_mix_ge {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1-t) * entropy p + t * entropy q ≤
      entropy (fun i => (1-t)*p i + t*q i) := by
  unfold entropy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simpa only [smul_eq_mul] using Real.concaveOn_negMulLog.2
    (hp i) (hq i) (sub_nonneg.mpr ht.2) ht.1 (by ring : 1-t+t=1)

/-- A zero probability gains a strict logarithmic bonus under mixing.
This is the boundary argument needed to obtain a positive entropy optimizer
on the entire face, not an assumed regularity of H. -/
theorem entropy_mix_zero_bonus {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) {j : ι} (hj : p j = 0)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1-t) * entropy p + t * entropy q + q j * Real.negMulLog t ≤
      entropy (fun i => (1-t)*p i + t*q i) := by
  classical
  have hterm : ∀ i, (1-t) * Real.negMulLog (p i) + t * Real.negMulLog (q i) +
      (if i=j then q j * Real.negMulLog t else 0) ≤
        Real.negMulLog ((1-t)*p i+t*q i) := by
    intro i
    by_cases hi : i=j
    · subst i
      simp only [hj, Real.negMulLog_zero, mul_zero, zero_add, ite_true,
        Real.negMulLog_mul]
      linarith
    · simp only [hi, ↓reduceIte, add_zero]
      simpa only [smul_eq_mul] using Real.concaveOn_negMulLog.2
        (hp i) (hq i) (sub_nonneg.mpr ht.2) ht.1 (by ring : 1-t+t=1)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, entropy] using hh

/-- Every entropy maximizer on a convex feasible set has maximal support. -/
theorem entropy_maximizer_support {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hmax : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      entropy (fun i => (1-t)*p i+t*q i) ≤ entropy p) {j : ι} (hjq : 0 < q j) :
    0 < p j := by
  by_contra hj
  have hj0 : p j = 0 := le_antisymm (le_of_not_gt hj) (hp j)
  have hqp : entropy q ≤ entropy p := by simpa using hmax 1 (by constructor <;> norm_num)
  let c := (entropy p-entropy q)/(q j)+1
  have hc : 0 < c := by dsimp [c]; positivity
  let t := Real.exp (-c)
  have htp : 0 < t := Real.exp_pos _
  have ht : t ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨htp.le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hc.le)⟩
  have hbonus := (entropy_mix_zero_bonus hp hq hj0 ht).trans (hmax t ht)
  have hlog : Real.log t = -c := Real.log_exp _
  rw [Real.negMulLog, hlog] at hbonus
  have he : q j * c = entropy p-entropy q+q j := by
    dsimp [c]
    field_simp
  nlinarith

omit [Fintype V] [DecidableEq V] in
/-- The preceding support conclusion for the concrete matching-law optimizer. -/
theorem matching_optimizer_support (G : LooplessGraph V E) {y : E → ℝ}
    {p q : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y)
    (hq : q ∈ G.feasibleLaws y) (hopt : entropy p = maxMatchingEntropy G y)
    {M : G.Matching} (hM : 0 < q M) : 0 < p M := by
  apply entropy_maximizer_support hp.1.1 hq.1.1 _ hM
  intro t ht
  apply le_trans (entropy_le_maxMatchingEntropy (G := G) (y := y) ?_) (le_of_eq hopt.symm)
  constructor
  · exact convex_probabilitySimplex _ hp.1 hq.1
      (sub_nonneg.mpr ht.2) ht.1 (by ring)
  · calc
      G.mean (fun i => (1-t)*p i+t*q i) =
          (1-t) • G.mean p + t • G.mean q := by
        exact (G.meanLinear).map_add ((1-t) • p) (t • q) |>.trans (by
          rw [LinearMap.map_smul, LinearMap.map_smul]; rfl)
      _ = y := by rw [hp.2, hq.2]; ext e; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring


/-- Supporting-line inequality for -x log x, with no positivity assumption
on the comparison probability x. -/
theorem negMulLog_tangent {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    Real.negMulLog x ≤ -x * Real.log y + y-x := by
  have h := mul_le_mul_of_nonneg_left
    (Real.negMulLog_le_one_sub_self (div_nonneg hx hy.le)) hy.le
  have he : Real.negMulLog x = -x * Real.log y + y * Real.negMulLog (x/y) := by
    calc
      Real.negMulLog x = Real.negMulLog (y * (x/y)) := by congr 1; field_simp
      _ = (x/y) * Real.negMulLog y + y * Real.negMulLog (x/y) := Real.negMulLog_mul _ _
      _ = _ := by unfold Real.negMulLog; field_simp
  rw [he]
  have hdiv : y * (x/y) = x := by field_simp
  nlinarith

/-- Gibbs' inequality on a finite set, with the exact support condition
needed on boundary faces. -/
theorem entropy_le_crossEntropy {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (hq : q ∈ probabilitySimplex ι)
    (hsupp : ∀ i, p i = 0 → q i = 0) :
    entropy q ≤ -∑ i, q i * Real.log (p i) := by
  have hterm : ∀ i, Real.negMulLog (q i) ≤
      -(q i * Real.log (p i)) + p i-q i := by
    intro i
    by_cases hi : p i = 0
    · simp [hi, hsupp i hi]
    · simpa only [neg_mul] using negMulLog_tangent (hq.1 i)
        (lt_of_le_of_ne (hp.1 i) (Ne.symm hi))
  have hh := Finset.sum_le_sum (s := Finset.univ) fun i _ => hterm i
  simpa only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, hp.2, hq.2, add_sub_cancel_right, entropy] using hh

/-- Derivative of entropy along a line supported on the positive probabilities. -/
theorem entropy_line_hasDerivAt {ι : Type*} [Fintype ι] (p v : ι → ℝ)
    (hsupp : ∀ i, p i = 0 → v i = 0) :
    HasDerivAt (fun t : ℝ => entropy (fun i => p i+t*v i))
      (-∑ i, v i * Real.log (p i) - ∑ i, v i) 0 := by
  have hd : ∀ i, HasDerivAt (fun t : ℝ => Real.negMulLog (p i+t*v i))
      ((-Real.log (p i)-1)*v i) 0 := by
    intro i
    by_cases hi : p i = 0
    · simpa only [hi, hsupp i hi, mul_zero, add_zero, Real.negMulLog_zero] using
        (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    · have hp : p i+(0 : ℝ)*v i ≠ 0 := by simpa using hi
      simpa only [zero_mul, add_zero, one_mul, Function.comp_def, id_eq] using
        (Real.hasDerivAt_negMulLog hp).comp 0
          (((hasDerivAt_id (0 : ℝ)).mul_const (v i)).const_add (p i))
  have he : (∑ i, (-Real.log (p i)-1)*v i) =
      -∑ i, v i*Real.log (p i) - ∑ i, v i := by
    simp_rw [sub_mul, one_mul, neg_mul, mul_comm (Real.log (p _))]
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [← he]
  simpa only [entropy, Finset.sum_apply] using (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i))

omit [Fintype V] [DecidableEq V] in
/-- The log probabilities of the actual optimizer annihilate every feasible
mass/mean-preserving linear variation. No exponential representation assumed. -/
theorem matching_optimizer_log_annihilates (G : LooplessGraph V E) {y : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y)
    (hopt : entropy p = maxMatchingEntropy G y) (v : G.Matching → ℝ)
    (hvsum : ∑ M, v M = 0) (hvmean : G.mean v = 0)
    (hsupp : ∀ M, p M = 0 → v M = 0) :
    ∑ M, v M * Real.log (p M) = 0 := by
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ M, 0 ≤ p M+t*v M := by
    apply Filter.eventually_all.mpr
    intro M
    by_cases hM : p M = 0
    · exact Filter.Eventually.of_forall (fun t => by simp [hM, hsupp M hM])
    · have hpos : 0 < p M := lt_of_le_of_ne (hp.1.1 M) (Ne.symm hM)
      have hc : Continuous (fun t : ℝ => p M+t*v M) := by fun_prop
      have hh : {t : ℝ | 0 < p M+t*v M} ∈ 𝓝 0 :=
        (isOpen_lt continuous_const hc).mem_nhds (by simpa using hpos)
      exact Filter.Eventually.mono hh (fun t ht => ht.le)
  have hlocal : IsLocalMax (fun t : ℝ => entropy (fun M => p M+t*v M)) 0 := by
    filter_upwards [hev] with t ht
    have hmean : G.mean (fun M => p M+t*v M) = y := by
      change G.meanLinear (p+t • v) = y
      rw [map_add, map_smul]
      change G.mean p + t • G.mean v = y
      rw [hp.2, hvmean, smul_zero, add_zero]
    have hsum : ∑ M, (p M+t*v M) = 1 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hp.1.2, hvsum, mul_zero, add_zero]
    have hle := entropy_le_maxMatchingEntropy (G := G) ⟨⟨ht, hsum⟩, hmean⟩
    simpa only [zero_mul, add_zero, ← hopt] using hle
  have hh := hlocal.deriv_eq_zero
  rw [(entropy_line_hasDerivAt p v hsupp).deriv, hvsum] at hh
  linarith


/-- A finite nonnegative vector permits small positive motion in any direction
which does not point outwards at its zero coordinates. -/
theorem exists_pos_nonneg_perturb {ι : Type*} [Fintype ι] (p v : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hz : ∀ i, p i = 0 → 0 ≤ v i) :
    ∃ t : ℝ, 0 < t ∧ ∀ i, 0 ≤ p i+t*v i := by
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, p i ≠ 0 → 0 ≤ p i+t*v i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : p i = 0
    · exact Filter.Eventually.of_forall (fun _ h => (h hi).elim)
    · have hc : Continuous (fun t : ℝ => p i+t*v i) := by fun_prop
      have hh : {t : ℝ | 0 < p i+t*v i} ∈ 𝓝 0 :=
        (isOpen_lt continuous_const hc).mem_nhds
          (by simpa using lt_of_le_of_ne (hp i) (Ne.symm hi))
      exact Filter.Eventually.mono hh (fun t ht _ => ht.le)
  have he' := (hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Set.Ioi 0)
  obtain ⟨t, ht, htp⟩ := he'.exists
  refine ⟨t, htp, fun i => ?_⟩
  by_cases hi : p i = 0
  · rw [hi, zero_add]
    exact mul_nonneg htp.le (hz i hi)
  · exact ht i hi

omit [Fintype V] [DecidableEq V] in
/-- The support of an optimizing law is a face: every law at a mean generated
by that support is itself supported there. This avoids assuming a face
representation of the marginal polytope in the entropy-optimization step. -/
theorem matching_optimizer_face_support (G : LooplessGraph V E) {y : E → ℝ}
    {p : G.Matching → ℝ} (hp : p ∈ G.feasibleLaws y)
    (hopt : entropy p = maxMatchingEntropy G y)
    {q r : G.Matching → ℝ} (hq : q ∈ probabilitySimplex G.Matching)
    (hr : r ∈ probabilitySimplex G.Matching) (hmean : G.mean q = G.mean r)
    (hrsupport : ∀ M, p M = 0 → r M = 0) :
    ∀ M, p M = 0 → q M = 0 := by
  obtain ⟨t, htp, ht⟩ := exists_pos_nonneg_perturb p (q-r) hp.1.1
    (fun M hM => by simpa [hrsupport M hM] using hq.1 M)
  have hsum : ∑ M, (p M+t*(q-r) M) = 1 := by
    simp only [Pi.sub_apply, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_sub_distrib, hp.1.2, hq.2, hr.2]
    ring
  have hmean' : G.mean (fun M => p M+t*(q-r) M) = y := by
    change G.meanLinear (p+t • (q-r)) = y
    rw [map_add, map_smul, map_sub]
    change G.mean p + t • (G.mean q-G.mean r) = y
    rw [hp.2, hmean, sub_self, smul_zero, add_zero]
  intro M hM
  by_contra hqM
  have hqMp : 0 < q M := lt_of_le_of_ne (hq.1 M) (Ne.symm hqM)
  have hpM := matching_optimizer_support G hp ⟨⟨ht, hsum⟩, hmean'⟩ hopt
    (M := M) (by simpa [hM, hrsupport M hM] using mul_pos htp hqMp)
  simp [hM] at hpM

end MatchingEntropy

end

end OAI
