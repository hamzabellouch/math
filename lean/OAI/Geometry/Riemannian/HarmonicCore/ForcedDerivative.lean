import OAI.Geometry.Riemannian.HarmonicCore.CutoffBounds

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal

namespace HarmonicCounterexample.Main.SmoothMetric3

noncomputable def vectorizeL2 (b : E3) : ValueL2 →L[ℝ] DerivativeL2 :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight b).compLpL 2 volume

lemma vectorizeL2_coe (b : E3) (u : ValueL2) :
    (vectorizeL2 b u : E3 → E3) =ᵐ[volume] fun x ↦ u x • b :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight b).coeFn_compLpL u

lemma vectorizeL2_norm (b : E3) (u : ValueL2) : ‖vectorizeL2 b u‖ ≤ ‖b‖*‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [vectorizeL2_coe b u] with x hx
  rw [hx,norm_smul,mul_comm]

lemma vectorizeL2_translate (b a : E3) (u : ValueL2) :
    vectorizeL2 b (translateL2 a u) = translateL2 a (vectorizeL2 b u) := by
  apply Lp.ext
  have ht := (measurePreserving_add_right (volume : Measure E3) a).quasiMeasurePreserving
  filter_upwards [vectorizeL2_coe b (translateL2 a u),translateL2_coe a u,
    translateL2_coe a (vectorizeL2 b u),ht.ae (vectorizeL2_coe b u)] with x h1 h2 h3 h4
  rw [h1,h2,h3,h4]

lemma vectorizeL2_finiteDifference (b a : E3) (h : ℝ) (u : ValueL2) :
    vectorizeL2 b (finiteDifferenceL2 a h u) = finiteDifferenceL2 a h (vectorizeL2 b u) := by
  simp only [finiteDifferenceL2_apply,map_smul,map_sub,vectorizeL2_translate]

lemma vectorize_component_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E3)
    (F : DerivativeL2) : ∑ i,vectorizeL2 (b i) (componentL2 (b i) F) = F := by
  classical
  apply Lp.ext
  have h1 := Lp.coeFn_finsetSum (Finset.univ) (fun i ↦ vectorizeL2 (b i) (componentL2 (b i) F))
  have h2 : ∀ᵐ x ∂(volume : Measure E3), ∀ i,
      (vectorizeL2 (b i) (componentL2 (b i) F)) x = ⟪b i,F x⟫_ℝ • b i := by
    rw [ae_all_iff]
    intro i
    filter_upwards [vectorizeL2_coe (b i) (componentL2 (b i) F),componentL2_coe (b i) F] with x hx hy
    rw [hx,hy]
  filter_upwards [h1,h2] with x hx hy
  rw [hx]
  simpa only [Finset.sum_apply,hy] using b.sum_repr' (F x)

lemma forcing_finiteDifference_bound {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E3)
    (N : ℝ) (F : DerivativeL2) (w : ι → ZeroSobolev N)
    (hw : ∀ i, sobolevValue N (w i) = componentL2 (b i) F) (a : E3) (h : ℝ) :
    ‖finiteDifferenceL2 a h F‖ ≤ (∑ i,‖sobolevDerivative N (w i)‖)*‖a‖ := by
  classical
  calc
    _ = ‖∑ i,vectorizeL2 (b i) (finiteDifferenceL2 a h (sobolevValue N (w i)))‖ := by
      simp only [hw,vectorizeL2_finiteDifference,←map_sum,vectorize_component_sum]
    _ ≤ ∑ i,‖vectorizeL2 (b i) (finiteDifferenceL2 a h (sobolevValue N (w i)))‖ := norm_sum_le _ _
    _ ≤ ∑ i,‖a‖*‖sobolevDerivative N (w i)‖ := by
      apply Finset.sum_le_sum
      intro i hi
      have hn := vectorizeL2_norm (b i) (finiteDifferenceL2 a h (sobolevValue N (w i)))
      rw [b.norm_eq_one i,one_mul] at hn
      exact hn.trans (sobolev_finiteDifference_bound N (w i) a h)
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem weak_finiteDifference_forced (R S T : ℝ) (A : E3 → E3 →L[ℝ] E3) (C L : ℝ)
    (hA : Continuous A) (hC : ∀ x, ‖A x‖ ≤ C) (hL : ∀ x y, ‖A y-A x‖ ≤ L*‖y-x‖)
    (u : ZeroSobolev T) (F : DerivativeL2)
    (hu : ∀ v : ZeroSobolev S,
      ⟪coefficientCLM A C hA.aestronglyMeasurable hC (sobolevDerivative T u),sobolevDerivative S v⟫_ℝ =
        ⟪F,sobolevDerivative S v⟫_ℝ)
    (a : E3) (h : ℝ) (hRS : R+‖h • a‖ ≤ S) (v : ZeroSobolev R) :
    ⟪shiftedCoefficientCLM A C hA hC (h • a) (finiteDifferenceL2 a h (sobolevDerivative T u)),sobolevDerivative R v⟫_ℝ =
      ⟪finiteDifferenceL2 a h F-differenceCoefficientCLM A L hA hL a h (sobolevDerivative T u),sobolevDerivative R v⟫_ℝ := by
  have hRS' : R+‖(-h) • a‖ ≤ S := by simpa only [neg_smul,norm_neg] using hRS
  let v' : ZeroSobolev S := includeSobolev hRS' (finiteDifferenceSobolev R a (-h) v)
  have hvd : sobolevDerivative S v' = finiteDifferenceL2 a (-h) (sobolevDerivative R v) := rfl
  have he := hu v'
  rw [hvd] at he
  have he' : ⟪finiteDifferenceL2 a h (coefficientCLM A C hA.aestronglyMeasurable hC (sobolevDerivative T u)),sobolevDerivative R v⟫_ℝ =
      ⟪finiteDifferenceL2 a h F,sobolevDerivative R v⟫_ℝ := by
    rw [finiteDifferenceL2_inner,finiteDifferenceL2_inner,he]
  rw [finiteDifference_coefficient_product A C L hA hC hL a h,inner_add_left] at he'
  rw [inner_sub_left]
  linarith



theorem localized_differenceLimit (R T : ℝ) (u : ZeroSobolev T)
    (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ Metric.ball 0 R)
    (K D : ℝ) (hK : ∀ x, ‖χ x‖ ≤ K) (hD : ∀ x, ‖gradient χ x‖ ≤ D)
    (a : E3) (M : ℝ)
    (hb : ∀ᶠ h : ℝ in 𝓝[≠] 0,
      ‖cutoffSobolev R (T+‖h • a‖) χ hχ hsupp K D hK hD
        (finiteDifferenceSobolev T a h u)‖ ≤ M) :
    ∃ w : ZeroSobolev R, ‖w‖ ≤ M ∧
      sobolevValue R w = scalarFieldCLM χ hχ.continuous K hK (componentL2 a (sobolevDerivative T u)) := by
  let v : ℝ → ZeroSobolev R := fun h ↦ cutoffSobolev R (T+‖h • a‖) χ hχ hsupp K D hK hD
    (finiteDifferenceSobolev T a h u)
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



lemma weak_forced_gradient_finiteDifference_bound (R S T : ℝ)
    (A : E3 → E3 →L[ℝ] E3) (C L c : ℝ) (hc : 0 < c)
    (hA : Continuous A) (hC : ∀ x, ‖A x‖ ≤ C) (hL : ∀ x y, ‖A y-A x‖ ≤ L*‖y-x‖)
    (hpos : ∀ x v, c*‖v‖^2 ≤ ⟪A x v,v⟫_ℝ)
    (u : ZeroSobolev T) (F : DerivativeL2)
    (hu : ∀ v : ZeroSobolev S,
      ⟪coefficientCLM A C hA.aestronglyMeasurable hC (sobolevDerivative T u),sobolevDerivative S v⟫_ℝ =
        ⟪F,sobolevDerivative S v⟫_ℝ)
    (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ Metric.ball 0 R)
    (K D : ℝ) (hK : ∀ x, ‖χ x‖ ≤ K) (hD : ∀ x, ‖gradient χ x‖ ≤ D)
    (a : E3) (h M : ℝ) (hRS : R+‖h • a‖ ≤ S) (hF : ‖finiteDifferenceL2 a h F‖ ≤ M) :
    ‖scalarFieldCLM χ hχ.continuous K hK (finiteDifferenceL2 a h (sobolevDerivative T u))‖ ≤
      ((2*C+2)/c+1)*(D*‖a‖*‖sobolevDerivative T u‖+K*(M+L*‖a‖*‖sobolevDerivative T u‖)) := by
  let w := finiteDifferenceSobolev T a h u
  let G := finiteDifferenceL2 a h F-differenceCoefficientCLM A L hA hL a h (sobolevDerivative T u)
  have hw := weak_caccioppoli_forcing R (T+‖h • a‖) (shiftedCoefficient A (h • a)) C c hc
    (shiftedCoefficient_continuous A hA (h • a)).aestronglyMeasurable
    (shiftedCoefficient_bound A C hC (h • a)) (fun x v ↦ hpos (x+h • a) v) w G
    (fun v ↦ weak_finiteDifference_forced R S T A C L hA hC hL u F hu a h hRS v)
    χ hχ hsupp K D hK hD
  change ‖scalarFieldCLM χ hχ.continuous K hK (finiteDifferenceL2 a h (sobolevDerivative T u))‖ ≤ _ at hw
  have hC0 : 0 ≤ C := (norm_nonneg (A 0)).trans (hC 0)
  have hK0 : 0 ≤ K := (norm_nonneg (χ 0)).trans (hK 0)
  have hD0 : 0 ≤ D := (norm_nonneg (gradient χ 0)).trans (hD 0)
  have hq : ‖gradientFieldCLM χ hχ D hD (sobolevValue (T+‖h • a‖) w)‖ ≤
      D*‖a‖*‖sobolevDerivative T u‖ := by
    change ‖gradientFieldCLM χ hχ D hD (finiteDifferenceL2 a h (sobolevValue T u))‖ ≤ _
    exact (gradientFieldCLM_norm χ hχ D hD _).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (sobolev_finiteDifference_bound T u a h) hD0)
  have hG : ‖G‖ ≤ M+L*‖a‖*‖sobolevDerivative T u‖ :=
    (norm_sub_le _ _).trans (add_le_add hF (differenceCoefficientCLM_norm A L hA hL a h _))
  have hr : ‖scalarFieldCLM χ hχ.continuous K hK G‖ ≤ K*(M+L*‖a‖*‖sobolevDerivative T u‖) :=
    (scalarFieldCLM_norm χ hχ.continuous K hK G).trans (mul_le_mul_of_nonneg_left hG hK0)
  exact hw.trans (mul_le_mul_of_nonneg_left (add_le_add hq hr) (by positivity))

theorem weak_forced_interior_derivative {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E3) (R S T N : ℝ) (hRS : R < S)
    (A : E3 → E3 →L[ℝ] E3) (C L c : ℝ) (hc : 0 < c)
    (hA : Continuous A) (hC : ∀ x, ‖A x‖ ≤ C) (hL : ∀ x y, ‖A y-A x‖ ≤ L*‖y-x‖)
    (hpos : ∀ x v, c*‖v‖^2 ≤ ⟪A x v,v⟫_ℝ)
    (u : ZeroSobolev T) (F : DerivativeL2) (wF : ι → ZeroSobolev N)
    (hwF : ∀ i, sobolevValue N (wF i) = componentL2 (b i) F)
    (hu : ∀ v : ZeroSobolev S,
      ⟪coefficientCLM A C hA.aestronglyMeasurable hC (sobolevDerivative T u),sobolevDerivative S v⟫_ℝ =
        ⟪F,sobolevDerivative S v⟫_ℝ)
    (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ Metric.ball 0 R)
    (K D : ℝ) (hK : ∀ x, ‖χ x‖ ≤ K) (hD : ∀ x, ‖gradient χ x‖ ≤ D) (a : E3) :
    ∃ w : ZeroSobolev R,
      ‖w‖ ≤ (poincareConstant R+1)*
        (((2*C+2)/c+1)*(D*‖a‖*‖sobolevDerivative T u‖+
          K*((∑ i,‖sobolevDerivative N (wF i)‖)*‖a‖+L*‖a‖*‖sobolevDerivative T u‖))+
          D*‖a‖*‖sobolevDerivative T u‖) ∧
      sobolevValue R w = scalarFieldCLM χ hχ.continuous K hK (componentL2 a (sobolevDerivative T u)) := by
  apply localized_differenceLimit R T u χ hχ hsupp K D hK hD a
  have hcont : ContinuousAt (fun h : ℝ ↦ R+‖h • a‖) 0 := by fun_prop
  have he : ∀ᶠ h : ℝ in 𝓝 (0:ℝ), R+‖h • a‖ < S :=
    hcont.eventually (gt_mem_nhds (by simpa only [zero_smul,norm_zero,add_zero] using hRS))
  filter_upwards [he.filter_mono nhdsWithin_le_nhds] with h hh
  apply (sobolev_norm_le_gradient R _).trans
  apply mul_le_mul_of_nonneg_left _ (add_nonneg (poincareConstant_nonneg R) zero_le_one)
  change ‖scalarFieldCLM χ hχ.continuous K hK (finiteDifferenceL2 a h (sobolevDerivative T u))+
    gradientFieldCLM χ hχ D hD (finiteDifferenceL2 a h (sobolevValue T u))‖ ≤ _
  have h1 := weak_forced_gradient_finiteDifference_bound R S T A C L c hc hA hC hL hpos u F hu
    χ hχ hsupp K D hK hD a h _ hh.le (forcing_finiteDifference_bound b N F wF hwF a h)
  have hD0 : 0 ≤ D := (norm_nonneg (gradient χ 0)).trans (hD 0)
  have h2 : ‖gradientFieldCLM χ hχ D hD (finiteDifferenceL2 a h (sobolevValue T u))‖ ≤
      D*‖a‖*‖sobolevDerivative T u‖ :=
    (gradientFieldCLM_norm χ hχ D hD _).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (sobolev_finiteDifference_bound T u a h) hD0)
  exact (norm_add_le _ _).trans (add_le_add h1 h2)

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
