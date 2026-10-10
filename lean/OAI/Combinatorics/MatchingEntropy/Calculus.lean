import OAI.Combinatorics.MatchingEntropy.Duality

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

universe uV uE uI uJ uA uB uC uW uF uD uι

namespace MatchingEntropyBounds

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def entropyLineD {ι : Type uι} [Fintype ι] (x v : ι → ℝ) (t : ℝ) : ℝ :=
  -∑ i, v i * Real.log (x i+t*v i) - ∑ i, v i

theorem entropy_line_hasDerivAt_at {ι : Type uι} [Fintype ι] (x v : ι → ℝ)
    (t : ℝ) (h : ∀ i, x i+t*v i ≠ 0 ∨ v i = 0) :
    HasDerivAt (fun t : ℝ => entropy (fun i => x i+t*v i)) (entropyLineD x v t) t := by
  have hd : ∀ i, HasDerivAt (fun t : ℝ => Real.negMulLog (x i+t*v i))
      ((-Real.log (x i+t*v i)-1)*v i) t := by
    intro i
    rcases h i with hi | hi
    · simpa only [one_mul, Function.comp_def, id_eq] using
        (Real.hasDerivAt_negMulLog hi).comp t
          (((hasDerivAt_id t).mul_const (v i)).const_add (x i))
    · simpa only [hi, mul_zero, add_zero] using (hasDerivAt_const t (Real.negMulLog (x i)))
  have he : (∑ i, (-Real.log (x i+t*v i)-1)*v i) = entropyLineD x v t := by
    simp_rw [sub_mul, one_mul, neg_mul, mul_comm (Real.log (x _+t*v _))]
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    rfl
  rw [← he]
  simpa only [entropy, Finset.sum_apply] using
    (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i))

theorem entropy_line_deriv_eventually {ι : Type uι} [Fintype ι] (x v : ι → ℝ)
    (hsupp : ∀ i, x i = 0 → v i = 0) :
    deriv (fun t : ℝ => entropy (fun i => x i+t*v i)) =ᶠ[𝓝 0] entropyLineD x v := by
  have hh : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, x i+t*v i ≠ 0 ∨ v i = 0 := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : x i = 0
    · exact Filter.Eventually.of_forall (fun t => Or.inr (hsupp i hi))
    · have hc : ContinuousAt (fun t : ℝ => x i+t*v i) 0 := by fun_prop
      have hn := hc.eventually_ne (show x i+(0:ℝ)*v i ≠ 0 by simpa using hi)
      exact hn.mono (fun t ht => Or.inl ht)
  filter_upwards [hh] with t ht
  exact (entropy_line_hasDerivAt_at x v t ht).deriv

theorem entropyLineD_hasDerivAt {ι : Type uι} [Fintype ι] (x v : ι → ℝ)
    (hsupp : ∀ i, x i = 0 → v i = 0) :
    HasDerivAt (entropyLineD x v) (-∑ i, (v i)^2/x i) 0 := by
  have hd : ∀ i, HasDerivAt (fun t : ℝ => v i*Real.log (x i+t*v i))
      ((v i)^2/x i) 0 := by
    intro i
    by_cases hi : x i = 0
    · simpa only [hi, hsupp i hi, zero_mul, zero_pow (by omega : 2 ≠ 0), zero_div] using
        (hasDerivAt_const (0:ℝ) (0:ℝ))
    · have hh := ((((hasDerivAt_id (0:ℝ)).mul_const (v i)).const_add (x i)).log
          (by simpa using hi)).const_mul (v i)
      simpa only [id_eq, one_mul, zero_mul, add_zero, pow_two, mul_div_assoc] using hh
  change HasDerivAt (fun t : ℝ => -(∑ i, v i*Real.log (x i+t*v i)) - ∑ i, v i)
    (-∑ i, (v i)^2/x i) 0
  exact (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hd i)).neg.sub_const (∑ i, v i)

theorem entropy_line_second {ι : Type uι} [Fintype ι] (x v : ι → ℝ)
    (hsupp : ∀ i, x i = 0 → v i = 0) :
    HasDerivAt (deriv (fun t : ℝ => entropy (fun i => x i+t*v i)))
      (-∑ i, (v i)^2/x i) 0 :=
  (entropyLineD_hasDerivAt x v hsupp).congr_of_eventuallyEq
    (entropy_line_deriv_eventually x v hsupp)

theorem second_deriv_quadratic_adjustment {f fD g gD : ℝ → ℝ} {fDD gDD c₀ c₁ v : ℝ}
    (hf : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt f (fD t) t)
    (hg : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt g (gD t) t)
    (hfD : HasDerivAt fD fDD 0) (hgD : HasDerivAt gD gDD 0) :
    HasDerivAt (deriv (fun t => f t+c₀+t*c₁+t^2*v-g t))
      (fDD+2*v-gDD) 0 := by
  have hfirst : deriv (fun t => f t+c₀+t*c₁+t^2*v-g t) =ᶠ[𝓝 (0:ℝ)]
      (fun t => fD t+c₁+2*t*v-gD t) := by
    filter_upwards [hf, hg] with t hft hgt
    have hd := (((hft.add_const c₀).fun_add ((hasDerivAt_id t).mul_const c₁)).fun_add
      (((hasDerivAt_id t).fun_pow 2).mul_const v)).fun_sub hgt
    simpa only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq, one_mul,
      Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] using hd.deriv
  have hd := ((hfD.add_const c₁).fun_add
    (((hasDerivAt_id (0:ℝ)).const_mul 2).mul_const v)).fun_sub hgD
  have hd' : HasDerivAt (fun t => fD t+c₁+2*t*v-gD t) (fDD+2*v-gDD) 0 := by
    simpa only [Pi.add_apply, Pi.sub_apply, id_eq, mul_one] using hd
  exact hd'.congr_of_eventuallyEq hfirst

theorem second_deriv_nonpos_of_local_max {f : ℝ → ℝ} {x : ℝ}
    (hm : IsLocalMax f x) (hc : ContinuousAt f x) : deriv (deriv f) x ≤ 0 := by
  by_contra h
  have hp : 0 < deriv (deriv f) x := lt_of_not_ge h
  have hmin := isLocalMin_of_deriv_deriv_pos hp hm.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 x] (fun _ => f x) := by
    filter_upwards [hm, hmin] with y h₁ h₂
    exact le_antisymm h₁ h₂
  have hh := he.deriv.deriv_eq
  simp only [deriv_const', deriv_const] at hh
  linarith

theorem entropy_line_eventually_hasDerivAt {ι : Type uι} [Fintype ι] (x v : ι → ℝ)
    (hsupp : ∀ i, x i = 0 → v i = 0) :
    ∀ᶠ t : ℝ in 𝓝 0,
      HasDerivAt (fun t : ℝ => entropy (fun i => x i+t*v i)) (entropyLineD x v t) t := by
  have hh : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, x i+t*v i ≠ 0 ∨ v i = 0 := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : x i = 0
    · exact Filter.Eventually.of_forall (fun t => Or.inr (hsupp i hi))
    · have hc : ContinuousAt (fun t : ℝ => x i+t*v i) 0 := by fun_prop
      have hn := hc.eventually_ne (show x i+(0:ℝ)*v i ≠ 0 by simpa using hi)
      exact hn.mono (fun t ht => Or.inl ht)
  exact hh.mono (fun t ht => entropy_line_hasDerivAt_at x v t ht)

theorem score_law_eventually_simplex {ι : Type uι} [Fintype ι] {p : ι → ℝ}
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

end MatchingEntropyBounds

end

end OAI
