import OAI.Geometry.Riemannian.HarmonicCore.ClassicalHarmonic

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal
open FourierTransform TemperedDistribution
open scoped SchwartzMap BoundedContinuousFunction
open Function ContinuousLinearMap
open scoped Convolution

namespace HarmonicCounterexample.Main.SmoothMetric3

lemma coefficientCLM_tendsto_ae (A : ℕ → E3 → E3 →L[ℝ] E3)
    (B : E3 → E3 →L[ℝ] E3) (C : ℝ)
    (hA : ∀ n, AEStronglyMeasurable (A n) (volume : Measure E3))
    (hB : AEStronglyMeasurable B (volume : Measure E3))
    (hAC : ∀ n x, ‖A n x‖ ≤ C) (hBC : ∀ x, ‖B x‖ ≤ C)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun n ↦ A n x) atTop (𝓝 (B x)))
    (u : DerivativeL2) :
    Tendsto (fun n ↦ coefficientCLM (A n) C (hA n) (hAC n) u) atTop
      (𝓝 (coefficientCLM B C hB hBC u)) := by
  have hC : 0 ≤ C := (norm_nonneg (B 0)).trans (hBC 0)
  let v (n : ℕ) : DerivativeL2 :=
    coefficientCLM (A n) C (hA n) (hAC n) u-coefficientCLM B C hB hBC u
  have hv (n : ℕ) : (v n : E3 → E3) =ᵐ[volume] fun x ↦ A n x (u x)-B x (u x) := by
    filter_upwards [Lp.coeFn_sub (coefficientCLM (A n) C (hA n) (hAC n) u)
      (coefficientCLM B C hB hBC u),
      (coefficient_memLp (A n) C (hA n) (hAC n) u).coeFn_toLp,
      (coefficient_memLp B C hB hBC u).coeFn_toLp] with x hx hy hz
    exact hx.trans (congrArg₂ HSub.hSub hy hz)
  have hnorm (n : ℕ) : ∀ᵐ x ∂volume, ‖v n x‖ ≤ (2*C)*‖u x‖ := by
    filter_upwards [hv n] with x hx
    rw [hx]
    calc
      ‖A n x (u x)-B x (u x)‖ ≤ ‖A n x (u x)‖+‖B x (u x)‖ := norm_sub_le _ _
      _ ≤ C*‖u x‖+C*‖u x‖ := add_le_add
        ((A n x).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (hAC n x) (norm_nonneg _)))
        ((B x).le_opNorm _ |>.trans (mul_le_mul_of_nonneg_right (hBC x) (norm_nonneg _)))
      _ = (2*C)*‖u x‖ := by ring
  have hint : Integrable (fun x ↦ (2*C)^2*‖u x‖^2) (volume : Measure E3) := by
    simpa only [real_inner_self_eq_norm_sq] using (L2.integrable_inner u u (𝕜:=ℝ)).const_mul ((2*C)^2)
  have ht : Tendsto (fun n ↦ ∫ x,‖v n x‖^2) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (F:=fun n x ↦ ‖v n x‖^2) (fun x ↦ (2*C)^2*‖u x‖^2)
      (fun n ↦ (continuous_pow 2).comp_aestronglyMeasurable (Lp.aestronglyMeasurable (v n)).norm) hint
      (fun n ↦ ?_) (f:=fun _ : E3 ↦ (0:ℝ)) ?_
    · simpa only [integral_zero] using h
    · filter_upwards [hnorm n] with x hx
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hx 2
    · have hall : ∀ᵐ x ∂volume, ∀ n, v n x = A n x (u x)-B x (u x) := ae_all_iff.mpr hv
      filter_upwards [hlim,hall] with x hx hy
      simp only [hy]
      have hax : Tendsto (fun n ↦ A n x (u x)) atTop (𝓝 (B x (u x))) :=
        ((ContinuousLinearMap.apply ℝ E3 (u x)).continuous.tendsto (B x)).comp hx
      have hsub : Tendsto (fun n ↦ A n x (u x)-B x (u x)) atTop (𝓝 (0:E3)) := by
        simpa only [sub_self] using hax.sub (tendsto_const_nhds (x:=B x (u x)))
      simpa only [norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)] using hsub.norm.pow 2
  have he (n : ℕ) : (∫ x,‖v n x‖^2)=‖v n‖^2 := by
    rw [←real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  simp only [he] at ht
  have hn : Tendsto (fun n ↦ ‖v n‖) atTop (𝓝 0) := by
    have hs := (Real.continuous_sqrt.tendsto 0).comp ht
    change Tendsto (fun n ↦ Real.sqrt (‖v n‖^2)) atTop (𝓝 (Real.sqrt 0)) at hs
    simpa only [Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hs
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

lemma gradient_smooth_scalar_comp {ρ : ℝ → ℝ} {f : E3 → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (hf : ContDiff ℝ ∞ f) (x : E3) :
    gradient (ρ ∘ f) x = deriv ρ (f x) • gradient f x := by
  have hd := ((hρ.differentiable (by simp)).differentiableAt.hasDerivAt).comp_hasFDerivAt x
    ((hf.differentiable (by simp)).differentiableAt.hasFDerivAt)
  simp only [gradient,hd.fderiv,map_smul]



lemma coefficientCLM_tendsto_joint (A : ℕ → E3 → E3 →L[ℝ] E3)
    (B : E3 → E3 →L[ℝ] E3) (C : ℝ)
    (hA : ∀ n, AEStronglyMeasurable (A n) (volume : Measure E3))
    (hB : AEStronglyMeasurable B (volume : Measure E3))
    (hAC : ∀ n x, ‖A n x‖ ≤ C) (hBC : ∀ x, ‖B x‖ ≤ C)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun n ↦ A n x) atTop (𝓝 (B x)))
    (u : ℕ → DerivativeL2) (v : DerivativeL2) (hu : Tendsto u atTop (𝓝 v)) :
    Tendsto (fun n ↦ coefficientCLM (A n) C (hA n) (hAC n) (u n)) atTop
      (𝓝 (coefficientCLM B C hB hBC v)) := by
  have hb (n : ℕ) : ‖coefficientCLM (A n) C (hA n) (hAC n) (u n)-
      coefficientCLM (A n) C (hA n) (hAC n) v‖ ≤ C*‖u n-v‖ := by
    rw [←map_sub]
    exact coefficientLinear_norm (A n) C (hA n) (hAC n) (u n-v)
  have hz := squeeze_zero (fun n ↦ norm_nonneg _) hb
    (by simpa only [mul_zero] using tendsto_const_nhds.mul (tendsto_iff_norm_sub_tendsto_zero.mp hu))
  have ht := coefficientCLM_tendsto_ae A B C hA hB hAC hBC hlim v
  have hsum := (tendsto_zero_iff_norm_tendsto_zero.mpr hz).add ht
  simpa only [sub_add_cancel,zero_add] using hsum

noncomputable def scalarDerivativeField (ρ : ℝ → ℝ) (f : ValueL2) (x : E3) : E3 →L[ℝ] E3 :=
  deriv ρ (f x) • ContinuousLinearMap.id ℝ E3

lemma scalarDerivativeField_measurable (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (f : ValueL2) :
    AEStronglyMeasurable (scalarDerivativeField ρ f) (volume : Measure E3) :=
  ((hρ.continuous_deriv (by simp)).comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)).smul aestronglyMeasurable_const

lemma scalarDerivativeField_bound (ρ : ℝ → ℝ) (K : NNReal)
    (hK : ∀ t, ‖deriv ρ t‖ ≤ K) (f : ValueL2) (x : E3) : ‖scalarDerivativeField ρ f x‖ ≤ K := by
  rw [scalarDerivativeField,norm_smul]
  exact (mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le).trans (hK _)

lemma sobolev_smooth_composition (R : ℝ) (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hρ0 : ρ 0=0) (K : NNReal) (hK : ∀ t, ‖deriv ρ t‖ ≤ K) (u : ZeroSobolev R) :
    ∃ v : ZeroSobolev R,
      (sobolevValue R v : E3 → ℝ) =ᵐ[volume] (fun x ↦ ρ ((sobolevValue R u) x)) ∧
      (sobolevDerivative R v : E3 → E3) =ᵐ[volume]
        (fun x ↦ deriv ρ ((sobolevValue R u) x) • (sobolevDerivative R u) x) := by
  have hLip : LipschitzWith K ρ := lipschitzWith_of_nnnorm_deriv_le
    (hρ.differentiable (by simp)) (fun t ↦ by exact_mod_cast hK t)
  obtain ⟨z,hz,hzt⟩ := mem_closure_iff_seq_limit.mp u.property
  choose φ hφ using hz
  have hv : Tendsto (fun n ↦ testValueLinear R (φ n)) atTop (𝓝 (sobolevValue R u)) := by
    have h := (WithLp.fstL 2 ℝ ValueL2 DerivativeL2).continuous.continuousAt.tendsto.comp hzt
    convert h using 1
    · funext n
      dsimp only [Function.comp_apply]
      rw [←hφ n]
      rfl
    · rfl
  have hd : Tendsto (fun n ↦ testDerivativeLinear R (φ n)) atTop (𝓝 (sobolevDerivative R u)) := by
    have h := (WithLp.sndL 2 ℝ ValueL2 DerivativeL2).continuous.continuousAt.tendsto.comp hzt
    convert h using 1
    · funext n
      dsimp only [Function.comp_apply]
      rw [←hφ n]
      rfl
    · rfl
  obtain ⟨ns,hns,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  let f (n : ℕ) : ValueL2 := testValueLinear R (φ (ns n))
  let A (n : ℕ) := scalarDerivativeField ρ (f n)
  let B := scalarDerivativeField ρ (sobolevValue R u)
  let hA := fun n ↦ scalarDerivativeField_measurable ρ hρ (f n)
  let hB := scalarDerivativeField_measurable ρ hρ (sobolevValue R u)
  let hAC := fun n ↦ scalarDerivativeField_bound ρ K hK (f n)
  let hBC := scalarDerivativeField_bound ρ K hK (sobolevValue R u)
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun n ↦ A n x) atTop (𝓝 (B x)) := by
    filter_upwards [hae] with x hx
    exact (((hρ.continuous_deriv (by simp)).tendsto _).comp hx).smul tendsto_const_nhds
  let ψ (n : ℕ) : DirichletTest R := ⟨ρ ∘ (φ (ns n)),
    hρ.comp (φ (ns n)).property.1,(φ (ns n)).property.2.1.comp_left hρ0,
    (tsupport_comp_subset hρ0 _).trans (φ (ns n)).property.2.2⟩
  have hψv (n : ℕ) : testValueLinear R (ψ n)=hLip.compLp hρ0 (f n) := by
    apply Lp.ext
    filter_upwards [(ψ n).value_memLp.coeFn_toLp,hLip.coeFn_compLp hρ0 (f n),
      (φ (ns n)).value_memLp.coeFn_toLp] with x h1 h2 h3
    change (f n) x = ((φ (ns n)):E3 → ℝ) x at h3
    exact h1.trans (by change ρ (((φ (ns n)):E3 → ℝ) x) = _; rw [←h3]; exact h2.symm)
  have hψd (n : ℕ) : testDerivativeLinear R (ψ n)=
      coefficientCLM (A n) K (hA n) (hAC n) (testDerivativeLinear R (φ (ns n))) := by
    apply Lp.ext
    filter_upwards [(ψ n).derivative_memLp.coeFn_toLp,
      (coefficient_memLp (A n) K (hA n) (hAC n) (testDerivativeLinear R (φ (ns n)))).coeFn_toLp,
      (φ (ns n)).value_memLp.coeFn_toLp,(φ (ns n)).derivative_memLp.coeFn_toLp] with x h1 h2 h3 h4
    change ((testDerivativeLinear R) (ψ n)) x = gradient ((ψ n):E3 → ℝ) x at h1
    change (coefficientCLM (A n) K (hA n) (hAC n) (testDerivativeLinear R (φ (ns n)))) x = _ at h2
    rw [h1,h2]
    change gradient (ρ ∘ (φ (ns n))) x = deriv ρ ((f n) x) • (testDerivativeLinear R (φ (ns n))) x
    rw [gradient_smooth_scalar_comp hρ (φ (ns n)).property.1]
    change _ = deriv ρ ((testValueLinear R (φ (ns n))) x) • (testDerivativeLinear R (φ (ns n))) x
    change ((testValueLinear R) (φ (ns n))) x = ((φ (ns n)):E3 → ℝ) x at h3
    change ((testDerivativeLinear R) (φ (ns n))) x = gradient ((φ (ns n)):E3 → ℝ) x at h4
    rw [h3,h4]
  let e := (WithLp.prodContinuousLinearEquiv 2 ℝ ValueL2 DerivativeL2).symm
  let V := hLip.compLp hρ0 (sobolevValue R u)
  let W := coefficientCLM B K hB hBC (sobolevDerivative R u)
  have hVt : Tendsto (fun n ↦ testValueLinear R (ψ n)) atTop (𝓝 V) := by
    simp only [hψv]
    exact (hLip.continuous_compLp hρ0).continuousAt.tendsto.comp (hv.comp hns.tendsto_atTop)
  have hWt : Tendsto (fun n ↦ testDerivativeLinear R (ψ n)) atTop (𝓝 W) := by
    simp only [hψd]
    exact coefficientCLM_tendsto_joint A B K hA hB hAC hBC hlim _ _ (hd.comp hns.tendsto_atTop)
  have hmem : e (V,W) ∈ zeroSobolevSpace R := by
    apply (testGraph R).range.isClosed_topologicalClosure.mem_of_tendsto
      (e.continuous.continuousAt.tendsto.comp (hVt.prodMk_nhds hWt))
    exact Eventually.of_forall fun n ↦ subset_closure (Set.mem_range_self (ψ n))
  refine ⟨⟨e (V,W),hmem⟩,hLip.coeFn_compLp hρ0 (sobolevValue R u),?_⟩
  exact (coefficient_memLp B K hB hBC (sobolevDerivative R u)).coeFn_toLp



lemma tsupport_comp_add_subset {ρ : ℝ → ℝ} (H f : E3 → ℝ) :
    tsupport (fun x ↦ ρ ((H:E3 → ℝ) x+f x)) ⊆ tsupport f ∪ tsupport (ρ ∘ H) := by
  apply closure_minimal ?_ ((isClosed_tsupport f).union (isClosed_tsupport (ρ ∘ H)))
  intro x hx
  by_contra hn
  have hf := image_eq_zero_of_notMem_tsupport (not_or.mp hn).1
  have hH := image_eq_zero_of_notMem_tsupport (not_or.mp hn).2
  exact hx (by simpa only [hf,add_zero,Function.comp_apply] using hH)

lemma sobolev_affine_smooth_composition (R S : ℝ) (H : DirichletTest S)
    (ρ : ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρ0 : ρ 0=0)
    (hS : tsupport (ρ ∘ (H:E3 → ℝ)) ⊆ Metric.ball 0 R)
    (K : NNReal) (hK : ∀ t, ‖deriv ρ t‖ ≤ K) (u : ZeroSobolev R) :
    ∃ v : ZeroSobolev R,
      (sobolevValue R v : E3 → ℝ) =ᵐ[volume]
        (fun x ↦ ρ ((testValueLinear S H+sobolevValue R u) x)) ∧
      (sobolevDerivative R v : E3 → E3) =ᵐ[volume]
        (fun x ↦ deriv ρ ((testValueLinear S H+sobolevValue R u) x) •
          (testDerivativeLinear S H+sobolevDerivative R u) x) := by
  have hLip : LipschitzWith K ρ := lipschitzWith_of_nnnorm_deriv_le
    (hρ.differentiable (by simp)) (fun t ↦ by exact_mod_cast hK t)
  obtain ⟨z,hz,hzt⟩ := mem_closure_iff_seq_limit.mp u.property
  choose φ hφ using hz
  have hv0 : Tendsto (fun n ↦ testValueLinear R (φ n)) atTop (𝓝 (sobolevValue R u)) := by
    have h := (WithLp.fstL 2 ℝ ValueL2 DerivativeL2).continuous.continuousAt.tendsto.comp hzt
    convert h using 1
    · funext n
      dsimp only [Function.comp_apply]
      rw [←hφ n]
      rfl
    · rfl
  have hd0 : Tendsto (fun n ↦ testDerivativeLinear R (φ n)) atTop (𝓝 (sobolevDerivative R u)) := by
    have h := (WithLp.sndL 2 ℝ ValueL2 DerivativeL2).continuous.continuousAt.tendsto.comp hzt
    convert h using 1
    · funext n
      dsimp only [Function.comp_apply]
      rw [←hφ n]
      rfl
    · rfl
  have hv := (tendsto_const_nhds (x:=testValueLinear S H)).add hv0
  have hd := (tendsto_const_nhds (x:=testDerivativeLinear S H)).add hd0
  obtain ⟨ns,hns,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  let f (n : ℕ) : ValueL2 := testValueLinear S H+testValueLinear R (φ (ns n))
  let d (n : ℕ) : DerivativeL2 := testDerivativeLinear S H+testDerivativeLinear R (φ (ns n))
  let A (n : ℕ) := scalarDerivativeField ρ (f n)
  let B := scalarDerivativeField ρ (testValueLinear S H+sobolevValue R u)
  let hA := fun n ↦ scalarDerivativeField_measurable ρ hρ (f n)
  let hB := scalarDerivativeField_measurable ρ hρ (testValueLinear S H+sobolevValue R u)
  let hAC := fun n ↦ scalarDerivativeField_bound ρ K hK (f n)
  let hBC := scalarDerivativeField_bound ρ K hK (testValueLinear S H+sobolevValue R u)
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun n ↦ A n x) atTop (𝓝 (B x)) := by
    filter_upwards [hae] with x hx
    exact (((hρ.continuous_deriv (by simp)).tendsto _).comp hx).smul tendsto_const_nhds
  let ψ (n : ℕ) : DirichletTest R := ⟨fun x ↦ ρ ((H:E3 → ℝ) x+((φ (ns n)):E3 → ℝ) x),
    hρ.comp (H.property.1.add (φ (ns n)).property.1),
    (H.property.2.1.add (φ (ns n)).property.2.1).comp_left hρ0,
    (tsupport_comp_add_subset H (φ (ns n))).trans (union_subset (φ (ns n)).property.2.2 hS)⟩
  have hfv (n : ℕ) : (f n : E3 → ℝ) =ᵐ[volume] fun x ↦ (H:E3 → ℝ) x+((φ (ns n)):E3 → ℝ) x := by
    filter_upwards [Lp.coeFn_add (testValueLinear S H) (testValueLinear R (φ (ns n))),
      H.value_memLp.coeFn_toLp,(φ (ns n)).value_memLp.coeFn_toLp] with x h1 h2 h3
    exact h1.trans (congrArg₂ HAdd.hAdd h2 h3)
  have hfd (n : ℕ) : (d n : E3 → E3) =ᵐ[volume] fun x ↦ gradient (H:E3 → ℝ) x+gradient ((φ (ns n)):E3 → ℝ) x := by
    filter_upwards [Lp.coeFn_add (testDerivativeLinear S H) (testDerivativeLinear R (φ (ns n))),
      H.derivative_memLp.coeFn_toLp,(φ (ns n)).derivative_memLp.coeFn_toLp] with x h1 h2 h3
    exact h1.trans (congrArg₂ HAdd.hAdd h2 h3)
  have hψv (n : ℕ) : testValueLinear R (ψ n)=hLip.compLp hρ0 (f n) := by
    apply Lp.ext
    filter_upwards [(ψ n).value_memLp.coeFn_toLp,hLip.coeFn_compLp hρ0 (f n),hfv n] with x h1 h2 h3
    exact h1.trans (by change ρ ((H:E3 → ℝ) x+((φ (ns n)):E3 → ℝ) x) = _; rw [←h3]; exact h2.symm)
  have hψd (n : ℕ) : testDerivativeLinear R (ψ n)=
      coefficientCLM (A n) K (hA n) (hAC n) (d n) := by
    apply Lp.ext
    filter_upwards [(ψ n).derivative_memLp.coeFn_toLp,
      (coefficient_memLp (A n) K (hA n) (hAC n) (d n)).coeFn_toLp,hfv n,hfd n] with x h1 h2 h3 h4
    change ((testDerivativeLinear R) (ψ n)) x = gradient ((ψ n):E3 → ℝ) x at h1
    change (coefficientCLM (A n) K (hA n) (hAC n) (d n)) x = _ at h2
    rw [h1,h2]
    change gradient (ρ ∘ (fun y ↦ (H:E3 → ℝ) y+((φ (ns n)):E3 → ℝ) y)) x = deriv ρ ((f n) x) • (d n) x
    rw [gradient_smooth_scalar_comp hρ (H.property.1.add (φ (ns n)).property.1),h3,h4]
    congr 1
    exact congrFun (gradient_add_smooth H.property.1 (φ (ns n)).property.1) x
  let e := (WithLp.prodContinuousLinearEquiv 2 ℝ ValueL2 DerivativeL2).symm
  let V := hLip.compLp hρ0 (testValueLinear S H+sobolevValue R u)
  let W := coefficientCLM B K hB hBC (testDerivativeLinear S H+sobolevDerivative R u)
  have hVt : Tendsto (fun n ↦ testValueLinear R (ψ n)) atTop (𝓝 V) := by
    simp only [hψv]
    exact (hLip.continuous_compLp hρ0).continuousAt.tendsto.comp (hv.comp hns.tendsto_atTop)
  have hWt : Tendsto (fun n ↦ testDerivativeLinear R (ψ n)) atTop (𝓝 W) := by
    simp only [hψd]
    exact coefficientCLM_tendsto_joint A B K hA hB hAC hBC hlim _ _ (hd.comp hns.tendsto_atTop)
  have hmem : e (V,W) ∈ zeroSobolevSpace R := by
    apply (testGraph R).range.isClosed_topologicalClosure.mem_of_tendsto
      (e.continuous.continuousAt.tendsto.comp (hVt.prodMk_nhds hWt))
    exact Eventually.of_forall fun n ↦ subset_closure (Set.mem_range_self (ψ n))
  refine ⟨⟨e (V,W),hmem⟩,hLip.coeFn_compLp hρ0 (testValueLinear S H+sobolevValue R u),?_⟩
  exact (coefficient_memLp B K hB hBC (testDerivativeLinear S H+sobolevDerivative R u)).coeFn_toLp

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
