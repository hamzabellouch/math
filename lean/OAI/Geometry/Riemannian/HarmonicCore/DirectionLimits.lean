import OAI.Geometry.Riemannian.HarmonicCore.ForcedDerivative
import OAI.Geometry.Riemannian.HarmonicCore.EnergyStability

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal

namespace HarmonicCounterexample.Main.SmoothMetric3

lemma component_testDerivative (R : ℝ) (φ : DirichletTest R) (a : E3) :
    componentL2 a (testDerivativeLinear R φ) = testDirection φ a := by
  apply Lp.ext
  filter_upwards [componentL2_coe a (testDerivativeLinear R φ),φ.derivative_memLp.coeFn_toLp,
    (smooth_direction_memLp φ.property.1 φ.property.2.1 a).coeFn_toLp] with x h1 h2 h3
  change (componentL2 a (testDerivativeLinear R φ)) x =
    ((smooth_direction_memLp φ.property.1 φ.property.2.1 a).toLp _) x
  rw [h1,h3]
  change ⟪a,(φ.derivative_memLp.toLp _) x⟫_ℝ = _
  rw [h2,real_inner_comm,inner_gradient_left]

lemma testGraph_snd (R : ℝ) (φ : DirichletTest R) :
    (testGraph R φ).snd = testDerivativeLinear R φ := rfl

lemma derivative_test_approximation (R : ℝ) (u : ZeroSobolev R) (ε : ℝ) (hε : 0 < ε) :
    ∃ φ : DirichletTest R, ‖sobolevDerivative R u-testDerivativeLinear R φ‖ < ε := by
  obtain ⟨v,hv,hlim⟩ := mem_closure_iff_seq_limit.mp u.property
  have hder : Tendsto (fun n ↦ (v n).snd) atTop (𝓝 (sobolevDerivative R u)) :=
    (WithLp.sndL 2 ℝ ValueL2 DerivativeL2).continuous.continuousAt.tendsto.comp hlim
  obtain ⟨n,hn⟩ := (Metric.tendsto_nhds.mp hder ε hε).exists
  obtain ⟨φ,hφ⟩ := hv n
  refine ⟨φ,?_⟩
  rw [←hφ] at hn
  rw [testGraph_snd,dist_comm,dist_eq_norm] at hn
  exact hn

theorem sobolev_finiteDifference_tendsto (R : ℝ) (u : ZeroSobolev R) (a : E3) :
    Tendsto (fun h : ℝ ↦ finiteDifferenceL2 a h (sobolevValue R u))
      (𝓝[≠] 0) (𝓝 (componentL2 a (sobolevDerivative R u))) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε/(3*(‖a‖+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨φ,hφ⟩ := derivative_test_approximation R u δ hδ
  let v : ZeroSobolev R := ⟨testGraph R φ,subset_closure (Set.mem_range_self φ)⟩
  have hv : sobolevValue R v = testValueLinear R φ := rfl
  have hd : sobolevDerivative R v = testDerivativeLinear R φ := rfl
  have ht := Metric.tendsto_nhds.mp (test_finiteDifference_tendsto R φ a) (ε/3) (by positivity)
  filter_upwards [ht] with h hh
  rw [dist_eq_norm] at hh ⊢
  have h1 : ‖finiteDifferenceL2 a h (sobolevValue R u)-finiteDifferenceL2 a h (testValueLinear R φ)‖ ≤
      ‖a‖*‖sobolevDerivative R u-testDerivativeLinear R φ‖ := by
    have hb := sobolev_finiteDifference_bound R (u-v) a h
    simpa only [map_sub,hv,hd] using hb
  have h2 : ‖testDirection φ a-componentL2 a (sobolevDerivative R u)‖ ≤
      ‖a‖*‖sobolevDerivative R u-testDerivativeLinear R φ‖ := by
    rw [←component_testDerivative,←map_sub]
    exact (componentL2_norm a _).trans_eq (by rw [norm_sub_rev])
  have htri := norm_sub_le_norm_sub_add_norm_sub (finiteDifferenceL2 a h (sobolevValue R u))
    (finiteDifferenceL2 a h (testValueLinear R φ)) (componentL2 a (sobolevDerivative R u))
  have htri' := norm_sub_le_norm_sub_add_norm_sub (finiteDifferenceL2 a h (testValueLinear R φ))
    (testDirection φ a) (componentL2 a (sobolevDerivative R u))
  have he : 3*(‖a‖+1)*δ = ε := by dsimp [δ]; field_simp
  have hm : ‖a‖*‖sobolevDerivative R u-testDerivativeLinear R φ‖ ≤ ‖a‖*δ :=
    mul_le_mul_of_nonneg_left hφ.le (norm_nonneg a)
  nlinarith [norm_nonneg a]

lemma forcing_finiteDifference_tendsto {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E3)
    (N : ℝ) (F : DerivativeL2) (w : ι → ZeroSobolev N)
    (hw : ∀ i, sobolevValue N (w i) = componentL2 (b i) F) (a : E3) :
    Tendsto (fun h : ℝ ↦ finiteDifferenceL2 a h F) (𝓝[≠] 0)
      (𝓝 (∑ i,vectorizeL2 (b i) (componentL2 a (sobolevDerivative N (w i))))) := by
  classical
  have ht := tendsto_finsetSum Finset.univ (fun i _ ↦
    (vectorizeL2 (b i)).continuous.tendsto _ |>.comp (sobolev_finiteDifference_tendsto N (w i) a))
  simpa only [Function.comp_apply,hw,vectorizeL2_finiteDifference,←map_sum,vectorize_component_sum] using ht



lemma smooth_operator_taylor_bound (A : E3 → E3 →L[ℝ] E3) (hA : ContDiff ℝ ∞ A)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hQbound : ∀ x y, ‖fderiv ℝ A y-fderiv ℝ A x‖ ≤ Q*‖y-x‖) (x y : E3) :
    ‖A y-A x-fderiv ℝ A x (y-x)‖ ≤ Q*‖y-x‖^2 := by
  have hh := (convex_closedBall x ‖y-x‖).norm_image_sub_le_of_norm_fderiv_le'
    (φ:=fderiv ℝ A x) (fun z _ ↦ hA.differentiable (by simp) z)
    (C:=Q*‖y-x‖) (fun z hz ↦ (hQbound x z).trans
      (mul_le_mul_of_nonneg_left (by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz) hQ))
    (Metric.mem_closedBall_self (norm_nonneg _))
    (by simp only [Metric.mem_closedBall,dist_eq_norm]; exact le_rfl)
  simpa only [pow_two,mul_assoc] using hh

lemma coefficientDirection_continuous (A : E3 → E3 →L[ℝ] E3) (hA : ContDiff ℝ ∞ A) (a : E3) :
    Continuous (fun x ↦ fderiv ℝ A x a) :=
  (hA.continuous_fderiv (by simp)).clm_apply continuous_const

lemma coefficientDirection_bound (A : E3 → E3 →L[ℝ] E3) (L : ℝ) (hL0 : 0 ≤ L)
    (hL : ∀ x y, ‖A y-A x‖ ≤ L*‖y-x‖) (a : E3) :
    ∀ x, ‖fderiv ℝ A x a‖ ≤ L*‖a‖ := by
  intro x
  apply ((fderiv ℝ A x).le_opNorm a).trans
  exact mul_le_mul_of_nonneg_right
    (norm_fderiv_le_of_lip' ℝ hL0 (Filter.Eventually.of_forall (hL x))) (norm_nonneg a)

noncomputable def coefficientDirectionCLM (A : E3 → E3 →L[ℝ] E3) (hA : ContDiff ℝ ∞ A)
    (L : ℝ) (hL0 : 0 ≤ L) (hL : ∀ x y, ‖A y-A x‖ ≤ L*‖y-x‖) (a : E3) :
    DerivativeL2 →L[ℝ] DerivativeL2 :=
  coefficientCLM (fun x ↦ fderiv ℝ A x a) (L*‖a‖)
    (coefficientDirection_continuous A hA a).aestronglyMeasurable
    (coefficientDirection_bound A L hL0 hL a)

lemma differenceCoefficient_taylor_bound (A : E3 → E3 →L[ℝ] E3) (hA : ContDiff ℝ ∞ A)
    (Q : ℝ) (hQ : 0 ≤ Q)
    (hQbound : ∀ x y, ‖fderiv ℝ A y-fderiv ℝ A x‖ ≤ Q*‖y-x‖)
    (a : E3) (h : ℝ) (hh : h ≠ 0) (x : E3) :
    ‖differenceCoefficient A a h x-fderiv ℝ A x a‖ ≤ Q*‖h‖*‖a‖^2 := by
  have he : differenceCoefficient A a h x-fderiv ℝ A x a =
      h⁻¹ • (A (x+h • a)-A x-h • fderiv ℝ A x a) := by
    rw [smul_sub,smul_smul,inv_mul_cancel₀ hh,one_smul]
    rfl
  have ht := smooth_operator_taylor_bound A hA Q hQ hQbound x (x+h • a)
  rw [add_sub_cancel_left,map_smul] at ht
  rw [he,norm_smul,norm_inv]
  apply (mul_le_mul_of_nonneg_left ht (inv_nonneg.mpr (norm_nonneg h))).trans_eq
  rw [norm_smul]
  field_simp [norm_ne_zero_iff.mpr hh]

theorem differenceCoefficientCLM_tendsto (A : E3 → E3 →L[ℝ] E3) (hA : ContDiff ℝ ∞ A)
    (L Q : ℝ) (hL0 : 0 ≤ L) (hQ : 0 ≤ Q)
    (hL : ∀ x y, ‖A y-A x‖ ≤ L*‖y-x‖)
    (hQbound : ∀ x y, ‖fderiv ℝ A y-fderiv ℝ A x‖ ≤ Q*‖y-x‖) (a : E3) (u : DerivativeL2) :
    Tendsto (fun h : ℝ ↦ differenceCoefficientCLM A L hA.continuous hL a h u) (𝓝[≠] 0)
      (𝓝 (coefficientDirectionCLM A hA L hL0 hL a u)) := by
  have hb : ∀ᶠ h : ℝ in 𝓝[≠] 0,
      ‖differenceCoefficientCLM A L hA.continuous hL a h u-coefficientDirectionCLM A hA L hL0 hL a u‖ ≤
        (Q*‖h‖*‖a‖^2)*‖u‖ := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact coefficientCLM_difference_bound (differenceCoefficient A a h) (fun x ↦ fderiv ℝ A x a)
      (L*‖a‖) (L*‖a‖) (Q*‖h‖*‖a‖^2)
      (differenceCoefficient_continuous A hA.continuous a h).aestronglyMeasurable
      (coefficientDirection_continuous A hA a).aestronglyMeasurable
      (differenceCoefficient_bound A L hL a h) (coefficientDirection_bound A L hL0 hL a)
      (fun x ↦ differenceCoefficient_taylor_bound A hA Q hQ hQbound a h hh x) u
  have ht : Tendsto (fun h : ℝ ↦ (Q*‖h‖*‖a‖^2)*‖u‖) (𝓝[≠] 0) (𝓝 0) := by
    have hc : ContinuousAt (fun h : ℝ ↦ (Q*‖h‖*‖a‖^2)*‖u‖) 0 := by fun_prop
    simpa only [norm_zero,mul_zero,zero_mul] using hc.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero' (Filter.Eventually.of_forall (fun _ ↦ norm_nonneg _)) hb ht)

lemma shiftedCoefficientCLM_tendsto (A : E3 → E3 →L[ℝ] E3) (hA : Continuous A)
    (C L : ℝ) (hC : ∀ x, ‖A x‖ ≤ C) (hL : ∀ x y, ‖A y-A x‖ ≤ L*‖y-x‖)
    (a : E3) (u : DerivativeL2) :
    Tendsto (fun h : ℝ ↦ shiftedCoefficientCLM A C hA hC (h • a) u) (𝓝 (0:ℝ))
      (𝓝 (coefficientCLM A C hA.aestronglyMeasurable hC u)) := by
  have hb (h : ℝ) :
      ‖shiftedCoefficientCLM A C hA hC (h • a) u-coefficientCLM A C hA.aestronglyMeasurable hC u‖ ≤
        (L*‖h • a‖)*‖u‖ := by
    apply coefficientCLM_difference_bound (shiftedCoefficient A (h • a)) A C C (L*‖h • a‖)
    intro x
    simpa only [shiftedCoefficient,add_sub_cancel_left] using hL x (x+h • a)
  have ht : Tendsto (fun h : ℝ ↦ (L*‖h • a‖)*‖u‖) (𝓝 (0:ℝ)) (𝓝 0) := by
    have hc : ContinuousAt (fun h : ℝ ↦ (L*‖h • a‖)*‖u‖) 0 := by fun_prop
    simpa only [zero_smul,norm_zero,mul_zero,zero_mul] using hc.tendsto
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (squeeze_zero (fun _ ↦ norm_nonneg _) hb ht)



lemma shiftedCoefficientCLM_tendsto_apply (A : E3 → E3 →L[ℝ] E3) (hA : Continuous A)
    (C L : ℝ) (hC : ∀ x, ‖A x‖ ≤ C) (hL : ∀ x y, ‖A y-A x‖ ≤ L*‖y-x‖)
    (a : E3) (v : ℝ → DerivativeL2) (w : DerivativeL2)
    (hv : Tendsto v (𝓝[≠] 0) (𝓝 w)) :
    Tendsto (fun h : ℝ ↦ shiftedCoefficientCLM A C hA hC (h • a) (v h)) (𝓝[≠] 0)
      (𝓝 (coefficientCLM A C hA.aestronglyMeasurable hC w)) := by
  have hb (h : ℝ) :
      ‖shiftedCoefficientCLM A C hA hC (h • a) (v h)-shiftedCoefficientCLM A C hA hC (h • a) w‖ ≤
        C*‖v h-w‖ := by
    rw [←map_sub]
    exact coefficientLinear_norm (shiftedCoefficient A (h • a)) C
      (shiftedCoefficient_continuous A hA (h • a)).aestronglyMeasurable
      (shiftedCoefficient_bound A C hC (h • a)) (v h-w)
  have hz := squeeze_zero (fun h ↦ norm_nonneg _) hb
    (by simpa only [mul_zero] using (tendsto_const_nhds.mul (tendsto_iff_norm_sub_tendsto_zero.mp hv)))
  have ht := shiftedCoefficientCLM_tendsto A hA C L hC hL a w |>.mono_left (show 𝓝[≠] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hsum := (tendsto_zero_iff_norm_tendsto_zero.mpr hz).add ht
  simpa only [sub_add_cancel,zero_add] using hsum

theorem sobolev_direction_graph {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E3)
    (T N : ℝ) (u : ZeroSobolev T) (w : ι → ZeroSobolev N)
    (hw : ∀ i, sobolevValue N (w i) = componentL2 (b i) (sobolevDerivative T u)) (a : E3) :
    ∃ q : ZeroSobolev (T+1),
      sobolevValue (T+1) q = componentL2 a (sobolevDerivative T u) ∧
      sobolevDerivative (T+1) q =
        ∑ i,vectorizeL2 (b i) (componentL2 a (sobolevDerivative N (w i))) := by
  let e := (WithLp.prodContinuousLinearEquiv 2 ℝ ValueL2 DerivativeL2).symm
  let W := ∑ i,vectorizeL2 (b i) (componentL2 a (sobolevDerivative N (w i)))
  have ht := e.continuous.continuousAt.tendsto.comp
    ((sobolev_finiteDifference_tendsto T u a).prodMk_nhds
      (forcing_finiteDifference_tendsto b N (sobolevDerivative T u) w hw a))
  have he : ∀ᶠ h : ℝ in 𝓝[≠] 0, ‖h • a‖ < 1 := by
    have hc : ContinuousAt (fun h : ℝ ↦ ‖h • a‖) 0 := by fun_prop
    exact (hc.tendsto.eventually (gt_mem_nhds (by simp))).filter_mono nhdsWithin_le_nhds
  have hmem : e (componentL2 a (sobolevDerivative T u),W) ∈ zeroSobolevSpace (T+1) := by
    apply (testGraph (T+1)).range.isClosed_topologicalClosure.mem_of_tendsto ht
    filter_upwards [he] with h hh
    exact (includeSobolev (show T+‖h • a‖ ≤ T+1 by linarith)
      (finiteDifferenceSobolev T a h u)).property
  exact ⟨⟨_,hmem⟩,rfl,rfl⟩

theorem weak_direction_equation {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℝ E3) (d : OrthonormalBasis κ ℝ E3)
    (R S T N M : ℝ) (hRS : R < S)
    (A : E3 → E3 →L[ℝ] E3) (hA : ContDiff ℝ ∞ A) (C L Q : ℝ)
    (hC : ∀ x, ‖A x‖ ≤ C) (hL0 : 0 ≤ L) (hQ : 0 ≤ Q)
    (hL : ∀ x y, ‖A y-A x‖ ≤ L*‖y-x‖)
    (hQbound : ∀ x y, ‖fderiv ℝ A y-fderiv ℝ A x‖ ≤ Q*‖y-x‖)
    (u : ZeroSobolev T) (F : DerivativeL2)
    (hu : ∀ v : ZeroSobolev S,
      ⟪coefficientCLM A C hA.continuous.aestronglyMeasurable hC (sobolevDerivative T u),sobolevDerivative S v⟫_ℝ =
        ⟪F,sobolevDerivative S v⟫_ℝ)
    (w : ι → ZeroSobolev N)
    (hw : ∀ i, sobolevValue N (w i) = componentL2 (b i) (sobolevDerivative T u))
    (z : κ → ZeroSobolev M) (hz : ∀ i, sobolevValue M (z i) = componentL2 (d i) F) (a : E3) :
    ∃ q : ZeroSobolev (T+1),
      sobolevValue (T+1) q = componentL2 a (sobolevDerivative T u) ∧
      ∀ v : ZeroSobolev R,
        ⟪coefficientCLM A C hA.continuous.aestronglyMeasurable hC (sobolevDerivative (T+1) q),sobolevDerivative R v⟫_ℝ =
          ⟪(∑ i,vectorizeL2 (d i) (componentL2 a (sobolevDerivative M (z i))))-
            coefficientDirectionCLM A hA L hL0 hL a (sobolevDerivative T u),sobolevDerivative R v⟫_ℝ := by
  obtain ⟨q,hq,hqd⟩ := sobolev_direction_graph b T N u w hw a
  refine ⟨q,hq,fun v ↦ ?_⟩
  have ht := forcing_finiteDifference_tendsto b N (sobolevDerivative T u) w hw a
  rw [←hqd] at ht
  have hleft := (shiftedCoefficientCLM_tendsto_apply A hA.continuous C L hC hL a _ _ ht).inner (𝕜:=ℝ) (tendsto_const_nhds (x:=sobolevDerivative R v))
  have hright := ((forcing_finiteDifference_tendsto d M F z hz a).sub
    (differenceCoefficientCLM_tendsto A hA L Q hL0 hQ hL hQbound a (sobolevDerivative T u))).inner (𝕜:=ℝ) (tendsto_const_nhds (x:=sobolevDerivative R v))
  have he : ∀ᶠ h : ℝ in 𝓝[≠] 0, R+‖h • a‖ ≤ S := by
    have hc : ContinuousAt (fun h : ℝ ↦ R+‖h • a‖) 0 := by fun_prop
    have hh : R+‖(0:ℝ) • a‖ < S := by simpa using hRS
    exact ((hc.tendsto.eventually (gt_mem_nhds hh)).mono (fun h hh ↦ hh.le)).filter_mono nhdsWithin_le_nhds
  have heq : (fun h : ℝ ↦ ⟪shiftedCoefficientCLM A C hA.continuous hC (h • a)
      (finiteDifferenceL2 a h (sobolevDerivative T u)),sobolevDerivative R v⟫_ℝ) =ᶠ[𝓝[≠] 0]
      (fun h : ℝ ↦ ⟪finiteDifferenceL2 a h F-differenceCoefficientCLM A L hA.continuous hL a h
        (sobolevDerivative T u),sobolevDerivative R v⟫_ℝ) := by
    filter_upwards [he] with h hh
    exact weak_finiteDifference_forced R S T A C L hA.continuous hC hL u F hu a h hh v
  exact tendsto_nhds_unique hleft (hright.congr' heq.symm)

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
