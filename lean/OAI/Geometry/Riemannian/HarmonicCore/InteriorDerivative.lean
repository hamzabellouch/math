import OAI.Geometry.Riemannian.HarmonicCore.WeakLimits

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal

namespace HarmonicCounterexample.Main.SmoothMetric3
lemma value_eq_of_test_pairings (u v : ValueL2)
    (h : ∀ R : ℝ, ∀ φ : DirichletTest R,
      ⟪u,testValueLinear R φ⟫_ℝ = ⟪v,testValueLinear R φ⟫_ℝ) : u = v := by
  have hz : ∀ᵐ x ∂(volume : Measure E3), (u-v) x = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero ((Lp.memLp (u-v)).locallyIntegrable (by norm_num))
    intro φ hφ hc
    obtain ⟨R,hR⟩ := hc.isBounded.subset_ball (0:E3)
    let ψ : DirichletTest R := ⟨φ,hφ,hc,hR⟩
    have he : ⟪u-v,testValueLinear R ψ⟫_ℝ = 0 := by rw [inner_sub_left,h R ψ,sub_self]
    rw [L2.inner_def] at he
    convert he using 1
    apply integral_congr_ae
    filter_upwards [ψ.value_memLp.coeFn_toLp] with x hx
    change φ x * (u-v) x = (testValueLinear R ψ) x * (u-v) x
    rw [show (testValueLinear R ψ) x = φ x from hx]
  apply sub_eq_zero.mp
  apply Lp.ext
  filter_upwards [hz,Lp.coeFn_zero (E:=ℝ) (p:=2) (μ:=(volume:Measure E3))] with x hx h0
  rw [hx,h0]
  rfl

lemma scalarValue_inner (χ : E3 → ℝ) (hχ : Continuous χ) (K : ℝ)
    (hK : ∀ x, ‖χ x‖ ≤ K) (u v : ValueL2) :
    ⟪scalarFieldCLM χ hχ K hK u,v⟫_ℝ = ⟪u,scalarFieldCLM χ hχ K hK v⟫_ℝ := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [scalarFieldCLM_coe χ hχ K hK u,scalarFieldCLM_coe χ hχ K hK v] with x hx hy
  simp only [hx,hy,inner_smul_left,inner_smul_right,conj_trivial]

lemma scalarValue_test (R : ℝ) (φ : DirichletTest R)
    (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (K : ℝ) (hK : ∀ x, ‖χ x‖ ≤ K) :
    scalarFieldCLM χ hχ.continuous K hK (testValueLinear R φ) =
      testValueLinear R (φ.localize χ hχ) := by
  apply Lp.ext
  filter_upwards [scalarFieldCLM_coe χ hχ.continuous K hK (testValueLinear R φ),
    φ.value_memLp.coeFn_toLp,(φ.localize χ hχ).value_memLp.coeFn_toLp] with x h1 h2 h3
  change (scalarFieldCLM χ hχ.continuous K hK (testValueLinear R φ)) x =
    ((φ.localize χ hχ).value_memLp.toLp _) x
  rw [h1,h3]
  change χ x * (φ.value_memLp.toLp _) x = χ x * (φ:E3 → ℝ) x
  rw [h2]

lemma componentL2_scalar (a : E3) (χ : E3 → ℝ) (hχ : Continuous χ) (K : ℝ)
    (hK : ∀ x, ‖χ x‖ ≤ K) (u : DerivativeL2) :
    componentL2 a (scalarFieldCLM χ hχ K hK u) =
      scalarFieldCLM χ hχ K hK (componentL2 a u) := by
  apply Lp.ext
  filter_upwards [componentL2_coe a (scalarFieldCLM χ hχ K hK u),
    scalarFieldCLM_coe χ hχ K hK u,componentL2_coe a u,
    scalarFieldCLM_coe χ hχ K hK (componentL2 a u)] with x h1 h2 h3 h4
  rw [h1,h2,h4,h3,inner_smul_right]
  rfl

lemma sobolev_component_weak (T : ℝ) (u : ZeroSobolev T) (a : E3) :
    HasWeakDirectionalDerivative (sobolevValue T u) (componentL2 a (sobolevDerivative T u)) a := by
  intro R φ
  have h := sobolev_integration_by_parts T u φ.property.1 φ.property.2.1 a
  have he : ⟪sobolevDerivative T u,(smooth_smul_memLp φ.property.1 φ.property.2.1 a).toLp _⟫_ℝ =
      ⟪componentL2 a (sobolevDerivative T u),testValueLinear R φ⟫_ℝ := by
    rw [L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(smooth_smul_memLp φ.property.1 φ.property.2.1 a).coeFn_toLp,
      componentL2_coe a (sobolevDerivative T u),φ.value_memLp.coeFn_toLp] with x h1 h2 h3
    have hx : (testValueLinear R φ) x = (φ:E3 → ℝ) x := h3
    rw [h1,h2,hx,inner_smul_right]
    simp [real_inner_comm]
  rw [he] at h
  exact neg_eq_iff_eq_neg.mp h.symm

lemma sobolev_norm_le_gradient (R : ℝ) (u : ZeroSobolev R) :
    ‖u‖ ≤ (poincareConstant R+1)*‖sobolevDerivative R u‖ := by
  have h := sobolev_norm_sq_le R u
  have hp := poincareConstant_nonneg R
  have hd := norm_nonneg (sobolevDerivative R u)
  have hs : 0 ≤ 2*poincareConstant R*‖sobolevDerivative R u‖^2 := by positivity
  have hn : 0 ≤ (poincareConstant R+1)*‖sobolevDerivative R u‖ := by positivity
  nlinarith [sq_nonneg (‖u‖-(poincareConstant R+1)*‖sobolevDerivative R u‖)]

theorem weak_interior_derivative_sobolev (R S T : ℝ) (hRS : R < S)
    (A : E3 → E3 →L[ℝ] E3) (C L c : ℝ) (hc : 0 < c) (hL0 : 0 ≤ L)
    (hA : Continuous A) (hC : ∀ x, ‖A x‖ ≤ C) (hL : ∀ x y, ‖A y-A x‖ ≤ L*‖y-x‖)
    (hpos : ∀ x v, c*‖v‖^2 ≤ ⟪A x v,v⟫_ℝ)
    (u : ZeroSobolev T)
    (hu : ∀ v : ZeroSobolev S,
      ⟪coefficientCLM A C hA.aestronglyMeasurable hC (sobolevDerivative T u),sobolevDerivative S v⟫_ℝ = 0)
    (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ Metric.ball 0 R)
    (K D : ℝ) (hK : ∀ x, ‖χ x‖ ≤ K) (hD : ∀ x, ‖gradient χ x‖ ≤ D)
    (a : E3) :
    ∃ w : ZeroSobolev R,
      ‖w‖ ≤ (poincareConstant R+1)*(((((2*C+2)/c+1)*(D+K*L))+D)*‖a‖*‖sobolevDerivative T u‖) ∧
      sobolevValue R w = scalarFieldCLM χ hχ.continuous K hK (componentL2 a (sobolevDerivative T u)) := by
  let v : ℝ → ZeroSobolev R := fun h ↦ cutoffSobolev R (T+‖h • a‖) χ hχ hsupp K D hK hD
    (finiteDifferenceSobolev T a h u)
  have hb : ∀ᶠ h : ℝ in 𝓝[≠] 0,
      ‖v h‖ ≤ (poincareConstant R+1)*(((((2*C+2)/c+1)*(D+K*L))+D)*‖a‖*‖sobolevDerivative T u‖) := by
    have hcont : ContinuousAt (fun h : ℝ ↦ R+‖h • a‖) 0 := by fun_prop
    have he : ∀ᶠ h : ℝ in 𝓝 (0:ℝ), R+‖h • a‖ < S :=
      hcont.eventually (gt_mem_nhds (by simpa only [zero_smul,norm_zero,add_zero] using hRS))
    filter_upwards [he.filter_mono nhdsWithin_le_nhds] with h hh
    apply (sobolev_norm_le_gradient R (v h)).trans
    apply mul_le_mul_of_nonneg_left _ (add_nonneg (poincareConstant_nonneg R) zero_le_one)
    change ‖scalarFieldCLM χ hχ.continuous K hK (finiteDifferenceL2 a h (sobolevDerivative T u)) +
      gradientFieldCLM χ hχ D hD (finiteDifferenceL2 a h (sobolevValue T u))‖ ≤ _
    have h1 := weak_gradient_finiteDifference_bound R S T A C L c hc hL0 hA hC hL hpos
      u hu χ hχ hsupp K D hK hD a h hh.le
    have hD0 : 0 ≤ D := (norm_nonneg (gradient χ 0)).trans (hD 0)
    have h2 : ‖gradientFieldCLM χ hχ D hD (finiteDifferenceL2 a h (sobolevValue T u))‖ ≤
        D*‖a‖*‖sobolevDerivative T u‖ := by
      exact (gradientFieldCLM_norm χ hχ D hD _).trans
        (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (sobolev_finiteDifference_bound T u a h) hD0)
    exact (norm_add_le _ _).trans (by nlinarith only [h1,h2])
  obtain ⟨w,hw,hwt⟩ := bounded_family_test_limit v _ hb
  refine ⟨w,hw,value_eq_of_test_pairings _ _ ?_⟩
  intro Q φ
  have hn : Tendsto (fun h : ℝ ↦ -h) (𝓝[≠] 0) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_,?_⟩
    · simpa only [neg_zero] using (continuous_neg.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      simpa only [mem_compl_iff,mem_singleton_iff,neg_eq_zero] using hh
  have ht := (test_finiteDifference_tendsto Q (φ.localize χ hχ) a).comp hn
  have hi : Tendsto (fun h : ℝ ↦ -⟪sobolevValue T u,finiteDifferenceL2 a (-h)
      (testValueLinear Q (φ.localize χ hχ))⟫_ℝ) (𝓝[≠] 0)
      (𝓝 (-⟪sobolevValue T u,testDirection (φ.localize χ hχ) a⟫_ℝ)) :=
    (tendsto_const_nhds.inner (𝕜:=ℝ) ht).neg
  have he := hwt ((sobolevValue R).adjoint (testValueLinear Q φ))
    (-⟪sobolevValue T u,testDirection (φ.localize χ hχ) a⟫_ℝ)
  have hv : ∀ h : ℝ, ⟪v h,(sobolevValue R).adjoint (testValueLinear Q φ)⟫_ℝ =
      -⟪sobolevValue T u,finiteDifferenceL2 a (-h) (testValueLinear Q (φ.localize χ hχ))⟫_ℝ := by
    intro h
    rw [ContinuousLinearMap.adjoint_inner_right]
    change ⟪scalarFieldCLM χ hχ.continuous K hK (finiteDifferenceL2 a h (sobolevValue T u)),testValueLinear Q φ⟫_ℝ = _
    rw [scalarValue_inner,scalarValue_test,finiteDifferenceL2_inner]
  have he' := he (hi.congr (fun h ↦ (hv h).symm))
  rw [ContinuousLinearMap.adjoint_inner_right] at he'
  rw [he',scalarValue_inner,scalarValue_test]
  exact (sobolev_component_weak T u a Q (φ.localize χ hχ)).symm

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
