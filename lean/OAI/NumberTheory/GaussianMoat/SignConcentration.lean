import OAI.NumberTheory.GaussianMoat.SignedArithmetic

namespace OAI

universe uIota

namespace GaussianMoat

open MeasureTheory ProbabilityTheory
open scoped NNReal
noncomputable def fairCoin : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure
instance fairCoin_probability : IsProbabilityMeasure fairCoin := by
  unfold fairCoin
  infer_instance
noncomputable def signMeasure (ι : Type uIota) [Fintype ι] : Measure (ι → Bool) :=
  Measure.pi (fun _ => fairCoin)
instance signMeasure_probability (ι : Type uIota) [Fintype ι] : IsProbabilityMeasure (signMeasure ι) := by
  unfold signMeasure
  infer_instance

theorem fairCoin_mean (f : Bool → ℝ) : ∫ b, f b ∂fairCoin = (f false + f true) / 2 := by
  have hf : Integrable f fairCoin := Integrable.of_mem_Icc
    (min (f false) (f true)) (max (f false) (f true)) (by fun_prop) (by
      apply ae_of_all
      intro b
      cases b <;> simp)
  rw [integral_fintype hf]
  simp [fairCoin, measureReal_def,
    PMF.uniformOfFintype_apply]
  ring

theorem sign_hoeffding {ι : Type uIota} [Fintype ι] (f : ι → Bool → ℝ) (w : ι → ℝ)
    (hf : ∀ i b, f i b ∈ Set.Icc 0 (w i)) {ε : ℝ} (hε : 0 ≤ ε) :
    (signMeasure ι).real {σ | ε + ∑ i, (f i false + f i true) / 2 ≤ ∑ i, f i (σ i)}
      ≤ Real.exp (-ε ^ 2 / (2 * ∑ i, (((‖w i‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))) := by
  classical
  let X : ι → (ι → Bool) → ℝ := fun i σ => f i (σ i) - (f i false + f i true) / 2
  have hsub (i : ι) : HasSubgaussianMGF (X i) ((‖w i‖₊ / 2) ^ 2) (signMeasure ι) := by
    have h := hasSubgaussianMGF_of_mem_Icc (μ := fairCoin) (X := f i)
      (by fun_prop) (ae_of_all _ (hf i))
    rw [fairCoin_mean] at h
    simp only [sub_zero] at h
    have he := (measurePreserving_eval (fun _ : ι => fairCoin) i).map_eq
    rw [← he] at h
    have heval : AEMeasurable (Function.eval i : (ι → Bool) → Bool) (signMeasure ι) :=
      (measurable_pi_apply i).aemeasurable
    exact HasSubgaussianMGF.of_map heval h
  have hind : iIndepFun X (signMeasure ι) :=
    iIndepFun_pi (X := fun i b => f i b - (f i false + f i true) / 2) (fun _ => by fun_prop)
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind
    (s := Finset.univ) (fun i _ => hsub i) hε
  simpa only [X, Finset.sum_sub_distrib, le_sub_iff_add_le, NNReal.coe_sum] using h

open scoped Classical in

noncomputable def SplitSieve.eligible (s : SplitSieve) (v : GaussianInt) : Finset ℕ :=
  s.primes.filter (fun p => s.factor p ∣ v ∨ star (s.factor p) ∣ v)

noncomputable def SplitSieve.lineLog (s : SplitSieve) (v : GaussianInt) (p : ℕ) (b : Bool) : ℝ := by
  classical
  exact if signedFactor (s.factor p) b ∣ v then Real.log p else 0

theorem SplitSieve.eligible_log_bound (s : SplitSieve) {v : GaussianInt} (hv : v ≠ 0) :
    ∑ p ∈ s.eligible v, Real.log (p : ℝ) ≤ Real.log (v.norm : ℝ) := by
  classical
  let σ : ℕ → Bool := fun p => decide (s.factor p ∣ v)
  have hnorm := s.eligible_product_le_norm (s.eligible v)
    (Finset.filter_subset _ _) σ hv (by
      intro p hp
      obtain ⟨_, hleft | hright⟩ := Finset.mem_filter.mp hp
      · simp [σ, signedFactor, hleft]
      · by_cases hd : s.factor p ∣ v
        · simp [σ, signedFactor, hd]
        · simpa [σ, signedFactor, hd] using hright)
  have hnorm' : ∏ p ∈ s.eligible v, (p : ℝ) ≤ (v.norm : ℝ) := by
    have h : ((∏ p ∈ s.eligible v, (p : ℤ)) : ℝ) ≤ (v.norm : ℝ) := by exact_mod_cast hnorm
    push_cast at h
    exact h
  have hpos (p : ℕ) (hp : p ∈ s.eligible v) : 0 < (p : ℝ) := by
    exact_mod_cast (s.prime_mem p (Finset.mem_filter.mp hp).1).pos
  have hlog := Real.log_le_log (Finset.prod_pos hpos) hnorm'
  rw [Real.log_prod (fun p hp => (hpos p hp).ne')] at hlog
  exact hlog

theorem SplitSieve.lineLog_mean (s : SplitSieve) {v : GaussianInt}
    (hv : PrimitiveDirection v) (hv0 : v ≠ 0) :
    ∑ p : s.primes, (s.lineLog v p false + s.lineLog v p true) / 2 ≤
      Real.log (v.norm : ℝ) / 2 := by
  classical
  have heq : ∑ p : s.primes, (s.lineLog v p false + s.lineLog v p true) =
      ∑ p ∈ s.eligible v, Real.log (p : ℝ) := by
    rw [Finset.sum_coe_sort s.primes (fun p => s.lineLog v p false + s.lineLog v p true),
      SplitSieve.eligible, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    have hp2 : p ≠ 2 := by have hm := s.mod_four p hp; omega
    have hnot := not_both_factors_dvd_primitive (s.prime_mem p hp) hp2 (s.factor_norm p hp) hv
    by_cases h1 : s.factor p ∣ v <;> by_cases h2 : star (s.factor p) ∣ v
    · exact False.elim (hnot ⟨h1,h2⟩)
    all_goals simp [SplitSieve.lineLog, signedFactor, h1, h2]
  rw [← Finset.sum_div, heq]
  exact div_le_div_of_nonneg_right (s.eligible_log_bound hv0) (by norm_num)

theorem SplitSieve.lineLog_tail (s : SplitSieve) {v : GaussianInt}
    (hv : PrimitiveDirection v) (hv0 : v ≠ 0) {ε : ℝ} (hε : 0 ≤ ε) :
    (signMeasure s.primes).real {σ |
      Real.log (v.norm : ℝ) / 2 + ε ≤ ∑ p : s.primes, s.lineLog v p (σ p)}
    ≤ Real.exp (-ε ^ 2 / (2 * ∑ p : s.primes,
      (((‖Real.log (p : ℝ)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))) := by
  classical
  apply le_trans (measureReal_mono (s₂ := {σ |
    ε + ∑ p : s.primes, (s.lineLog v p false + s.lineLog v p true) / 2 ≤
      ∑ p : s.primes, s.lineLog v p (σ p)}) ?_)
  · apply sign_hoeffding (fun p : s.primes => s.lineLog v p) (fun p => Real.log (p : ℝ))
    · intro p b
      have hp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by
        exact_mod_cast (s.prime_mem p p.property).one_lt.le)
      unfold SplitSieve.lineLog
      split_ifs
      · exact ⟨hp, le_rfl⟩
      · exact ⟨le_rfl, hp⟩
    · exact hε
  · intro σ hσ
    have hmean := s.lineLog_mean hv hv0
    change Real.log (v.norm : ℝ) / 2 + ε ≤ _ at hσ
    change ε + _ ≤ _
    linarith

end GaussianMoat

end OAI
