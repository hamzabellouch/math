import OAI.Analysis.LpDimension.CompoundPoisson

namespace OAI

noncomputable section
open MeasureTheory Filter Matrix NormedSpace Metric Module Set ProbabilityTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator ENNReal NNReal RealInnerProductSpace
universe u uE

namespace SubpolynomialLp

lemma exists_probability_charFun_limit
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : ℕ → ProbabilityMeasure E) (f : E → ℂ) (hf : ContinuousAt f 0)
    (h : ∀ t, Tendsto (fun n => charFun (μ n) t) atTop (𝓝 (f t))) :
    ∃ ν : ProbabilityMeasure E, (∀ t, charFun ν t = f t) ∧ Tendsto μ atTop (𝓝 ν) := by
  have ht : IsTightMeasureSet (Set.range (fun n => (μ n : Measure E))) :=
    isTightMeasureSet_of_tendsto_charFun hf h
  have hc : IsCompact (closure (Set.range μ)) :=
    isCompact_closure_of_isTightMeasureSet (by convert! ht using 1; ext x; simp)
  obtain ⟨ν, _, φ, hφ, hν⟩ := hc.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  have hcf : ∀ t, charFun ν t = f t := by
    intro t
    exact tendsto_nhds_unique
      ((ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hν) t)
      ((h t).comp hφ.tendsto_atTop)
  refine ⟨ν, hcf, ProbabilityMeasure.tendsto_of_tendsto_charFun (fun t => ?_)⟩
  simpa only [hcf] using h t


def paretoJump (p a : ℝ) : Measure ℝ :=
  ENNReal.ofReal (a^p) • (powerIntensity p).restrict (Set.Ioi a)

lemma paretoJump_probability (p a : ℝ) (hp : 0 < p) (ha : 0 < a) :
    IsProbabilityMeasure (paretoJump p a) := by
  constructor
  simp only [paretoJump, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
    powerIntensity_tail p a hp ha]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ha.le p), ← Real.rpow_add ha,
    add_neg_cancel, Real.rpow_zero, ENNReal.ofReal_one]

lemma paretoJump_cos_exponent (p a t : ℝ) (hp : 0 < p) (ha : 0 < a) :
    a^(-p) * ((∫ r, Real.cos (t*r) ∂paretoJump p a)-1) =
      p * ∫ r in Set.Ioi a, stableKernel p t r := by
  have := paretoJump_probability p a hp ha
  have hi : Integrable (fun r => Real.cos (t*r)) (paretoJump p a) :=
    (integrable_const (1:ℝ)).mono' (by fun_prop) (ae_of_all _ (fun r => by
      simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (t*r)))
  have hc : (∫ _ : ℝ, (1:ℝ) ∂paretoJump p a) = 1 := by simp
  rw [← hc, ← integral_sub hi (integrable_const _)]
  rw [paretoJump, integral_smul_measure, ENNReal.toReal_ofReal (Real.rpow_nonneg ha.le _),
    smul_eq_mul, ← mul_assoc, ← Real.rpow_add ha, neg_add_cancel, Real.rpow_zero, one_mul,
    powerIntensity_restrict_integral p hp _ measurableSet_Ioi (Set.Ioi_subset_Ioi ha.le)]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun r => by simp only [stableKernel, smul_eq_mul]; ring)

def stableApprox (p a : ℝ) : Measure ℝ :=
  compoundPoisson (Real.toNNReal (a^(-p))) (symmetrize (paretoJump p a))

lemma stableApprox_probability (p a : ℝ) (hp : 0 < p) (ha : 0 < a) :
    IsProbabilityMeasure (stableApprox p a) := by
  have := paretoJump_probability p a hp ha
  unfold stableApprox
  infer_instance

lemma charFun_stableApprox (p a t : ℝ) (hp : 0 < p) (ha : 0 < a) :
    charFun (stableApprox p a) t =
      Complex.exp (p * ∫ r in Set.Ioi a, stableKernel p t r) := by
  have := paretoJump_probability p a hp ha
  rw [stableApprox, charFun_compoundPoisson, charFun_symmetrize,
    Real.coe_toNNReal _ (Real.rpow_nonneg ha.le _)]
  congr 1
  norm_cast
  exact paretoJump_cos_exponent p a t hp ha

lemma positive_cutoff_union :
    (⋃ n : ℕ, Set.Ioi ((n+1:ℝ)⁻¹)) = Set.Ioi (0:ℝ) := by
  ext r
  simp only [Set.mem_iUnion, Set.mem_Ioi]
  constructor
  · rintro ⟨n, hn⟩
    exact lt_trans (by positivity) hn
  · intro hr
    obtain ⟨n, hn⟩ := exists_nat_gt r⁻¹
    refine ⟨n, ?_⟩
    have h : r⁻¹ < (n:ℝ)+1 := by linarith
    have h' := (inv_lt_inv₀ (by positivity : (0:ℝ) < n+1) (inv_pos.mpr hr)).mpr h
    simpa using h'

lemma stableKernel_cutoff_limit (p t : ℝ) (hp : 0 < p) (hp2 : p < 2) :
    Tendsto (fun n : ℕ => ∫ r in Set.Ioi ((n+1:ℝ)⁻¹), stableKernel p t r)
      atTop (𝓝 (|t|^p * ∫ r in Set.Ioi 0, stableKernel p 1 r)) := by
  rw [← stableKernel_scaling p t hp]
  have hi : IntegrableOn (stableKernel p t) (⋃ n : ℕ, Set.Ioi ((n+1:ℝ)⁻¹)) := by
    rw [positive_cutoff_union]
    exact stableKernel_integrable p t hp hp2
  have hm : Monotone (fun n : ℕ => Set.Ioi ((n+1:ℝ)⁻¹)) := by
    intro n m hnm
    apply Set.Ioi_subset_Ioi
    apply inv_anti₀ (by positivity)
    exact_mod_cast Nat.add_le_add_right hnm 1
  simpa only [positive_cutoff_union] using
    tendsto_setIntegral_of_monotone (fun _ => measurableSet_Ioi) hm hi

lemma exists_stable_law (p : ℝ) (hp : 0 < p) (hp2 : p < 2) :
    ∃ μ : ProbabilityMeasure ℝ, ∀ t : ℝ,
      charFun μ t = Complex.exp ((p * |t|^p * ∫ r in Set.Ioi 0, stableKernel p 1 r : ℝ) : ℂ) := by
  let μ : ℕ → ProbabilityMeasure ℝ := fun n => ⟨stableApprox p ((n+1:ℝ)⁻¹),
    stableApprox_probability p _ hp (by positivity)⟩
  have h : ∀ t : ℝ, Tendsto (fun n => charFun (μ n) t) atTop
      (𝓝 (Complex.exp ((p * |t|^p * ∫ r in Set.Ioi 0, stableKernel p 1 r : ℝ) : ℂ))) := by
    intro t
    have he : ∀ n, charFun (μ n) t =
        Complex.exp ((p * ∫ r in Set.Ioi ((n+1:ℝ)⁻¹), stableKernel p t r : ℝ) : ℂ) := by
      intro n
      simpa only [μ, ProbabilityMeasure.coe_mk, Complex.ofReal_mul] using
        charFun_stableApprox p ((n+1:ℝ)⁻¹) t hp (by positivity)
    simp_rw [he]
    have ht := (Complex.continuous_exp.tendsto _).comp
      (Complex.continuous_ofReal.tendsto _ |>.comp ((stableKernel_cutoff_limit p t hp hp2).const_mul p))
    simpa only [Function.comp_def, mul_assoc] using ht
  obtain ⟨ν, hν, _⟩ := exists_probability_charFun_limit μ _ (by
    apply Continuous.continuousAt
    fun_prop (disch := positivity)) h
  exact ⟨ν, hν⟩

def stableConstant (p : ℝ) : ℝ := -p * ∫ r in Set.Ioi 0, stableKernel p 1 r

lemma stableConstant_pos (p : ℝ) (hp : 0 < p) (hp2 : p < 2) : 0 < stableConstant p := by
  have hi := (stableKernel_integrable p 1 hp hp2).neg
  have hn : ∀ᵐ r ∂volume.restrict (Set.Ioi (0:ℝ)), 0 ≤ -stableKernel p 1 r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    unfold stableKernel
    exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (Real.cos_le_one _)) (Real.rpow_nonneg (le_of_lt hr) _))
  have hsub : Set.Ioo (Real.pi/2) Real.pi ⊆ Function.support (fun r => -stableKernel p 1 r) := by
    intro r hr
    have hr0 : 0 < r := Real.pi_div_two_pos.trans hr.1
    have hc : Real.cos r < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt hr.1
      (hr.2.trans (by linarith [Real.pi_pos]))
    show -stableKernel p 1 r ≠ 0
    apply ne_of_gt
    unfold stableKernel
    simp only [one_mul]
    exact neg_pos.mpr (mul_neg_of_neg_of_pos (by linarith) (Real.rpow_pos_of_pos hr0 _))
  have hm : 0 < (volume.restrict (Set.Ioi (0:ℝ))) (Set.Ioo (Real.pi/2) Real.pi) := by
    rw [Measure.restrict_apply measurableSet_Ioo,
      Set.inter_eq_left.mpr (show Set.Ioo (Real.pi/2) Real.pi ⊆ Set.Ioi (0:ℝ) from
        fun r hr => Real.pi_div_two_pos.trans hr.1), Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by linarith [Real.pi_pos])
  have hpos := (integral_pos_iff_support_of_nonneg_ae hn hi).mpr
    (lt_of_lt_of_le hm (measure_mono hsub))
  rw [integral_neg] at hpos
  unfold stableConstant
  nlinarith


lemma exists_stable_law_full (p : ℝ) (hp : 0 < p) (hp2 : p < 2) :
    ∃ μ : ProbabilityMeasure ℝ, ∀ t : ℝ,
      charFun μ t = Complex.exp ((-stableConstant p*|t|^p:ℝ):ℂ) := by
  obtain ⟨μ,hμ⟩ := exists_stable_law p hp hp2
  refine ⟨μ,fun t => ?_⟩
  rw [hμ]
  congr 2
  unfold stableConstant
  ring

end SubpolynomialLp

end

end OAI
