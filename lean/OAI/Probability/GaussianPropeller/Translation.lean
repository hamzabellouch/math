import OAI.Probability.GaussianPropeller.Gram

namespace OAI

universe uE uX uY uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

namespace GaussianPropeller.Translation

lemma map_density_comp {X : Type uX} {Y : Type uY} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (g : X → Y) (hg : Measurable g)
    (f : Y → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity (f ∘ g)).map g = (μ.map g).withDensity f := by
  apply Measure.ext_of_lintegral
  intro h hh
  rw [lintegral_map hh hg]
  change (∫⁻ a, (h ∘ g) a ∂μ.withDensity (f ∘ g)) = _
  rw [lintegral_withDensity_eq_lintegral_mul _ (hf.comp hg) (hh.comp hg),
    lintegral_withDensity_eq_lintegral_mul _ hf hh]
  exact (lintegral_map (hf.mul hh) hg).symm

lemma product_density {ι : Type uι} [Fintype ι]
    (f : ι → ℝ → ℝ) (hf : ∀ i, Integrable (f i))
    (hn : ∀ i x, 0 ≤ f i x) :
    Measure.pi (fun i => volume.withDensity (fun x => ENNReal.ofReal (f i x))) =
      volume.withDensity (fun x : ι → ℝ => ENNReal.ofReal (∏ i, f i (x i))) := by
  classical
  have hii (i : ι) : IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (f i x))) := by
    apply isFiniteMeasure_withDensity
    rw [← ofReal_integral_eq_lintegral_ofReal (hf i) (ae_of_all _ (hn i))]
    exact ENNReal.ofReal_ne_top
  apply Measure.pi_eq
  intro s hs
  have hp : Integrable (fun x : ι → ℝ => ∏ i, f i (x i)) volume :=
    Integrable.fintype_prod hf
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← ofReal_integral_eq_lintegral_ofReal hp.restrict (ae_of_all _ (fun x =>
      Finset.prod_nonneg (fun i _ => hn i (x i))))]
  have heq : (univ.pi s).indicator (fun x : ι → ℝ => ∏ i, f i (x i)) =
      (fun x => ∏ i, (s i).indicator (f i) (x i)) := by
    funext x
    by_cases hx : x ∈ univ.pi s
    · simp only [Set.mem_univ_pi] at hx
      rw [Set.indicator_of_mem (show x ∈ univ.pi s by simpa only [Set.mem_univ_pi] using hx)]
      exact Finset.prod_congr rfl (fun i _ => (Set.indicator_of_mem (hx i) (f i)).symm)
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_univ_pi, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      symm
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi (f i))
  rw [← integral_indicator (MeasurableSet.univ_pi hs), heq,
    integral_fintype_prod_volume_eq_prod (fun i => (s i).indicator (f i)),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (fun x =>
      Set.indicator_nonneg (fun x _ => hn i x) x))]
  apply Finset.prod_congr rfl
  intro i _
  rw [integral_indicator (hs i), withDensity_apply _ (hs i),
    ofReal_integral_eq_lintegral_ofReal (hf i).restrict (ae_of_all _ (hn i))]

lemma pi_gaussian_density {ι : Type uι} [Fintype ι] (a : ι → ℝ) :
    Measure.pi (fun i => gaussianReal (a i) 1) =
      volume.withDensity (fun x : ι → ℝ =>
        ENNReal.ofReal (∏ i, gaussianPDFReal (a i) 1 (x i))) := by
  simp_rw [gaussianReal_of_var_ne_zero _ (by norm_num : (1 : NNReal) ≠ 0),
    gaussianPDF_def]
  exact product_density _ (fun i => integrable_gaussianPDFReal (a i) 1)
    (fun i => gaussianPDFReal_nonneg (a i) 1)

noncomputable def stdDensity {ι : Type uι} [Fintype ι]
    (x : EuclideanSpace ℝ ι) : ℝ := ∏ i, gaussianPDFReal 0 1 (x i)

lemma measurable_stdDensity {ι : Type uι} [Fintype ι] :
    Measurable (stdDensity : EuclideanSpace ℝ ι → ℝ) := by
  unfold stdDensity
  fun_prop

lemma stdGaussian_density {ι : Type uι} [Fintype ι] :
    stdGaussian (EuclideanSpace ℝ ι) =
      volume.withDensity (fun x => ENNReal.ofReal (stdDensity x)) := by
  rw [← map_pi_eq_stdGaussian, pi_gaussian_density (fun _ => 0)]
  have hm := map_density_comp (volume : Measure (ι → ℝ)) (WithLp.toLp 2)
    (PiLp.volume_preserving_toLp ι).measurable
    (fun x => ENNReal.ofReal (stdDensity x))
    (measurable_stdDensity.ennreal_ofReal)
  rw [(PiLp.volume_preserving_toLp ι).map_eq] at hm
  exact hm

lemma stdDensity_pos {ι : Type uι} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    0 < stdDensity x := by
  apply Finset.prod_pos
  intro i _
  exact gaussianPDFReal_pos _ _ _ (by norm_num)

lemma stdDensity_eq {ι : Type uι} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    stdDensity x = (Real.sqrt (2*Real.pi))⁻¹ ^ (Fintype.card ι) *
      Real.exp (-‖x‖^2/2) := by
  simp only [stdDensity, gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum]
  congr 2
  rw [← Finset.sum_div, Finset.sum_neg_distrib]
  congr 2
  simp [EuclideanSpace.norm_sq_eq]

lemma stdDensity_add {ι : Type uι} [Fintype ι]
    (x v : EuclideanSpace ℝ ι) :
    stdDensity (x+v) = stdDensity x * Real.exp (-⟪v,x⟫-‖v‖^2/2) := by
  rw [stdDensity_eq, stdDensity_eq, mul_assoc, ← Real.exp_add]
  congr 2
  rw [norm_add_sq_real, real_inner_comm x v]
  ring

lemma stdGaussian_map_add {ι : Type uι} [Fintype ι]
    (v : EuclideanSpace ℝ ι) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun x => x+v) =
      (stdGaussian (EuclideanSpace ℝ ι)).withDensity
        (fun x => ENNReal.ofReal (Real.exp (⟪v,x⟫-‖v‖^2/2))) := by
  have hm := map_density_comp (volume : Measure (EuclideanSpace ℝ ι))
    (fun x => x+v) (by fun_prop)
    (fun x => ENNReal.ofReal (stdDensity (x-v))) (by
      exact measurable_stdDensity.comp (by fun_prop) |>.ennreal_ofReal)
  simp only [Function.comp_def, add_sub_cancel_right] at hm
  rw [(measurePreserving_add_right volume v).map_eq] at hm
  rw [stdGaussian_density, hm, ← withDensity_mul volume
    measurable_stdDensity.ennreal_ofReal (by fun_prop)]
  congr 1
  funext x
  rw [sub_eq_add_neg, stdDensity_add, inner_neg_left, norm_neg, neg_neg,
    ENNReal.ofReal_mul (le_of_lt (stdDensity_pos x))]
  rfl

lemma translated_integral {ι : Type uι} [Fintype ι]
    (v : EuclideanSpace ℝ ι) (A : Set (EuclideanSpace ℝ ι)) (hA : MeasurableSet A) :
    ((stdGaussian (EuclideanSpace ℝ ι)).map (fun x => x-v)).real A =
      ∫ x in A, Real.exp (-⟪v,x⟫-‖v‖^2/2) ∂stdGaussian (EuclideanSpace ℝ ι) := by
  simp_rw [sub_eq_add_neg]
  rw [stdGaussian_map_add]
  simp only [inner_neg_left, norm_neg]
  rw [measureReal_def, withDensity_apply _ hA,
    ← integral_eq_lintegral_of_nonneg_ae (ae_of_all _
      (fun x => (Real.exp_pos (-⟪v,x⟫-‖v‖^2/2)).le)) (by fun_prop)]
  simp only [sub_eq_add_neg]

lemma integrable_exp_inner {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (h : E) (t : ℝ) : Integrable (fun x => Real.exp (t*⟪h,x⟫)) (stdGaussian E) := by
  let L : StrongDual ℝ E := innerSL ℝ h
  have hi : Integrable (fun x : ℝ => Real.exp (t*x)) ((stdGaussian E).map L) := by
    rw [IsGaussian.map_eq_gaussianReal L]
    exact integrable_exp_mul_gaussianReal t
  exact hi.comp_aemeasurable L.continuous.aemeasurable

lemma integrableExpSet_neg_inner_restrict {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (h : E) (A : Set E) :
    integrableExpSet (fun x => -⟪h,x⟫) ((stdGaussian E).restrict A) = univ := by
  ext t
  simp only [Set.mem_univ, iff_true]
  change Integrable (fun x => Real.exp (t * -⟪h,x⟫)) ((stdGaussian E).restrict A)
  simpa only [inner_neg_left] using (integrable_exp_inner (-h) t).restrict (s := A)

lemma translation_derivative {ι : Type uι} [Fintype ι]
    (h : EuclideanSpace ℝ ι) (A : Set (EuclideanSpace ℝ ι)) (hA : MeasurableSet A) :
    HasDerivAt (fun u : ℝ =>
      ((stdGaussian (EuclideanSpace ℝ ι)).map (fun x => x-u•h)).real A)
      (-⟪h, ∫ x in A, x ∂stdGaussian (EuclideanSpace ℝ ι)⟫) 0 := by
  have hd := hasDerivAt_mgf (X := fun x => -⟪h,x⟫)
    (μ := (stdGaussian (EuclideanSpace ℝ ι)).restrict A) (t := 0) (by
      rw [integrableExpSet_neg_inner_restrict, interior_univ]; trivial)
  simp only [zero_mul, Real.exp_zero, mul_one, integral_neg] at hd
  have he : HasDerivAt (fun u : ℝ => Real.exp (-u^2*‖h‖^2/2)) 0 0 := by
    convert (((hasDerivAt_pow 2 (0:ℝ)).neg.mul_const (‖h‖^2)).div_const 2).exp using 1
    simp
  have hp := he.mul hd
  simp only [zero_pow (by norm_num : 2 ≠ 0), neg_zero, zero_mul, zero_div,
    Real.exp_zero, one_mul, zero_add] at hp
  have hinner : (∫ x in A, ⟪h,x⟫ ∂stdGaussian (EuclideanSpace ℝ ι)) =
      ⟪h, ∫ x in A, x ∂stdGaussian (EuclideanSpace ℝ ι)⟫ :=
    integral_inner (IsGaussian.integrable_id (μ := stdGaussian (EuclideanSpace ℝ ι))).restrict h
  rw [hinner] at hp
  apply hp.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro u
  dsimp only [Pi.mul_apply]
  rw [translated_integral (u•h) A hA]
  simp only [inner_smul_left, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    starRingEnd_apply, star_trivial, mgf]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← Real.exp_add]
  congr 1
  ring

end GaussianPropeller.Translation

end OAI
