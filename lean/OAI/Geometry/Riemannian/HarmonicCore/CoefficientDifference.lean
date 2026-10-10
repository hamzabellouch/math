import OAI.Geometry.Riemannian.HarmonicCore.FiniteDifference

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal

namespace HarmonicCounterexample.Main.SmoothMetric3
def shiftedCoefficient (A : E3 → E3 →L[ℝ] E3) (a : E3) : E3 → E3 →L[ℝ] E3 :=
  fun x ↦ A (x+a)

lemma shiftedCoefficient_continuous (A : E3 → E3 →L[ℝ] E3) (hA : Continuous A) (a : E3) :
    Continuous (shiftedCoefficient A a) := hA.comp (continuous_id.add continuous_const)

lemma shiftedCoefficient_bound (A : E3 → E3 →L[ℝ] E3) (C : ℝ) (hC : ∀ x, ‖A x‖ ≤ C) (a : E3) :
    ∀ x, ‖shiftedCoefficient A a x‖ ≤ C := fun x ↦ hC (x+a)

noncomputable def shiftedCoefficientCLM (A : E3 → E3 →L[ℝ] E3) (C : ℝ)
    (hA : Continuous A) (hC : ∀ x, ‖A x‖ ≤ C) (a : E3) : DerivativeL2 →L[ℝ] DerivativeL2 :=
  coefficientCLM (shiftedCoefficient A a) C (shiftedCoefficient_continuous A hA a).aestronglyMeasurable
    (shiftedCoefficient_bound A C hC a)

noncomputable def differenceCoefficient (A : E3 → E3 →L[ℝ] E3) (a : E3) (h : ℝ) : E3 → E3 →L[ℝ] E3 :=
  fun x ↦ h⁻¹ • (A (x+h • a)-A x)

lemma differenceCoefficient_continuous (A : E3 → E3 →L[ℝ] E3) (hA : Continuous A) (a : E3) (h : ℝ) :
    Continuous (differenceCoefficient A a h) := by
  change Continuous (fun x : E3 ↦ h⁻¹ • (A (x+h • a)-A x))
  have ht : Continuous (fun x : E3 ↦ x+h • a) := continuous_id.add continuous_const
  have hf : Continuous (fun x : E3 ↦ A (x+h • a)-A x) := (hA.comp ht).sub hA
  exact hf.const_smul h⁻¹

lemma differenceCoefficient_bound (A : E3 → E3 →L[ℝ] E3) (L : ℝ)
    (hL : ∀ x y, ‖A y-A x‖ ≤ L*‖y-x‖) (a : E3) (h : ℝ) :
    ∀ x, ‖differenceCoefficient A a h x‖ ≤ L*‖a‖ := by
  intro x
  have hL0 : 0 ≤ L := by
    have hz := hL 0 (coordinateVector 0)
    have hn : ‖coordinateVector 0‖ = 1 := by simp [coordinateVector]
    simpa [hn] using (norm_nonneg (A (coordinateVector 0)-A 0)).trans hz
  by_cases hh : h = 0
  · simp [differenceCoefficient,hh,mul_nonneg hL0 (norm_nonneg a)]
  · calc
      ‖differenceCoefficient A a h x‖ = ‖h‖⁻¹*‖A (x+h • a)-A x‖ := by simp only [differenceCoefficient,norm_smul,norm_inv]
      _ ≤ ‖h‖⁻¹*(L*‖h • a‖) := mul_le_mul_of_nonneg_left
        (by simpa only [add_sub_cancel_left] using hL x (x+h • a)) (inv_nonneg.mpr (norm_nonneg h))
      _ = L*‖a‖ := by rw [norm_smul]; field_simp [norm_ne_zero_iff.mpr hh]

noncomputable def differenceCoefficientCLM (A : E3 → E3 →L[ℝ] E3) (L : ℝ)
    (hA : Continuous A) (hL : ∀ x y, ‖A y-A x‖ ≤ L*‖y-x‖) (a : E3) (h : ℝ) : DerivativeL2 →L[ℝ] DerivativeL2 :=
  coefficientCLM (differenceCoefficient A a h) (L*‖a‖)
    (differenceCoefficient_continuous A hA a h).aestronglyMeasurable
    (differenceCoefficient_bound A L hL a h)

lemma differenceCoefficientCLM_norm (A : E3 → E3 →L[ℝ] E3) (L : ℝ)
    (hA : Continuous A) (hL : ∀ x y, ‖A y-A x‖ ≤ L*‖y-x‖) (a : E3) (h : ℝ) (u : DerivativeL2) :
    ‖differenceCoefficientCLM A L hA hL a h u‖ ≤ L*‖a‖*‖u‖ :=
  coefficientLinear_norm (differenceCoefficient A a h) (L*‖a‖)
    (differenceCoefficient_continuous A hA a h).aestronglyMeasurable
    (differenceCoefficient_bound A L hL a h) u

lemma finiteDifference_coefficient_product (A : E3 → E3 →L[ℝ] E3) (C L : ℝ)
    (hA : Continuous A) (hC : ∀ x, ‖A x‖ ≤ C) (hL : ∀ x y, ‖A y-A x‖ ≤ L*‖y-x‖)
    (a : E3) (h : ℝ) (u : DerivativeL2) :
    finiteDifferenceL2 a h (coefficientCLM A C hA.aestronglyMeasurable hC u) =
      shiftedCoefficientCLM A C hA hC (h • a) (finiteDifferenceL2 a h u) +
        differenceCoefficientCLM A L hA hL a h u := by
  apply Lp.ext
  let T := coefficientCLM A C hA.aestronglyMeasurable hC
  let S := shiftedCoefficientCLM A C hA hC (h • a)
  let D := differenceCoefficientCLM A L hA hL a h
  have ht := (measurePreserving_add_right (volume : Measure E3) (h • a)).quasiMeasurePreserving
  have htall : (T u:E3 → E3) =ᵐ[volume] fun x ↦ A x (u x) := (coefficient_memLp A C hA.aestronglyMeasurable hC u).coeFn_toLp
  have hsall : (S (finiteDifferenceL2 a h u):E3 → E3) =ᵐ[volume] fun x ↦ A (x+h • a) ((finiteDifferenceL2 a h u) x) :=
    (coefficient_memLp (shiftedCoefficient A (h • a)) C
      (shiftedCoefficient_continuous A hA (h • a)).aestronglyMeasurable
      (shiftedCoefficient_bound A C hC (h • a)) (finiteDifferenceL2 a h u)).coeFn_toLp
  have hdall : (D u:E3 → E3) =ᵐ[volume] fun x ↦ (differenceCoefficient A a h x) (u x) :=
    (coefficient_memLp (differenceCoefficient A a h) (L*‖a‖)
      (differenceCoefficient_continuous A hA a h).aestronglyMeasurable
      (differenceCoefficient_bound A L hL a h) u).coeFn_toLp
  filter_upwards [finiteDifferenceL2_coe a h (T u),htall,ht.ae htall,hsall,hdall,
    finiteDifferenceL2_coe a h u,Lp.coeFn_add (S (finiteDifferenceL2 a h u)) (D u)]
    with x h1 h2 h3 h4 h5 h6 h7
  change (finiteDifferenceL2 a h (T u)) x = (S (finiteDifferenceL2 a h u)+D u) x
  rw [h1,h2,h3,h7,Pi.add_apply,h4,h5,h6]
  simp only [differenceCoefficient,map_smul,map_sub,smul_apply,sub_apply]
  module

theorem weak_finiteDifference_equation (R S T : ℝ) (A : E3 → E3 →L[ℝ] E3) (C L : ℝ)
    (hA : Continuous A) (hC : ∀ x, ‖A x‖ ≤ C) (hL : ∀ x y, ‖A y-A x‖ ≤ L*‖y-x‖)
    (u : ZeroSobolev T)
    (hu : ∀ v : ZeroSobolev S,
      ⟪coefficientCLM A C hA.aestronglyMeasurable hC (sobolevDerivative T u),sobolevDerivative S v⟫_ℝ = 0)
    (a : E3) (h : ℝ) (hRS : R+‖h • a‖ ≤ S) (v : ZeroSobolev R) :
    ⟪shiftedCoefficientCLM A C hA hC (h • a) (finiteDifferenceL2 a h (sobolevDerivative T u)),sobolevDerivative R v⟫_ℝ =
      ⟪-(differenceCoefficientCLM A L hA hL a h (sobolevDerivative T u)),sobolevDerivative R v⟫_ℝ := by
  have hRS' : R+‖(-h) • a‖ ≤ S := by simpa only [neg_smul,norm_neg] using hRS
  let v' : ZeroSobolev S := includeSobolev hRS' (finiteDifferenceSobolev R a (-h) v)
  have hvd : sobolevDerivative S v' = finiteDifferenceL2 a (-h) (sobolevDerivative R v) := rfl
  have he := hu v'
  rw [hvd] at he
  have he' : ⟪finiteDifferenceL2 a h (coefficientCLM A C hA.aestronglyMeasurable hC (sobolevDerivative T u)),sobolevDerivative R v⟫_ℝ = 0 := by
    rw [finiteDifferenceL2_inner,he,neg_zero]
  rw [finiteDifference_coefficient_product A C L hA hC hL a h,inner_add_left] at he'
  rw [inner_neg_left]
  linarith

lemma scalarFieldCLM_norm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (χ : E3 → ℝ) (hχ : Continuous χ) (C : ℝ) (hC : ∀ x, ‖χ x‖ ≤ C)
    (u : Lp V 2 (volume : Measure E3)) :
    ‖scalarFieldCLM χ hχ C hC u‖ ≤ C*‖u‖ := by
  exact fieldLinear_norm (fun x ↦ χ x • ContinuousLinearMap.id ℝ V) C
    (hχ.smul continuous_const).aestronglyMeasurable
    (fun x ↦ by
      rw [norm_smul]
      exact (mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le).trans (hC x)) u

lemma gradientFieldCLM_norm (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (D : ℝ) (hD : ∀ x, ‖gradient χ x‖ ≤ D) (u : ValueL2) :
    ‖gradientFieldCLM χ hχ D hD u‖ ≤ D*‖u‖ := by
  exact fieldLinear_norm (fun x ↦ (ContinuousLinearMap.id ℝ ℝ).smulRight (gradient χ x)) D
    (by
      have hc : Continuous (fun x ↦ (ContinuousLinearMap.id ℝ ℝ).smulRight (gradient χ x)) :=
        (((ContinuousLinearMap.smulRightL ℝ ℝ E3) (ContinuousLinearMap.id ℝ ℝ)).continuous).comp
          (gradient_continuous hχ)
      exact hc.aestronglyMeasurable)
    (fun x ↦ by simpa only [ContinuousLinearMap.norm_smulRight_apply,
      ContinuousLinearMap.norm_id,one_mul] using hD x) u

theorem weak_gradient_finiteDifference_bound (R S T : ℝ) (A : E3 → E3 →L[ℝ] E3)
    (C L c : ℝ) (hc : 0 < c) (_hL0 : 0 ≤ L)
    (hA : Continuous A) (hC : ∀ x, ‖A x‖ ≤ C) (hL : ∀ x y, ‖A y-A x‖ ≤ L*‖y-x‖)
    (hpos : ∀ x v, c*‖v‖^2 ≤ ⟪A x v,v⟫_ℝ)
    (u : ZeroSobolev T)
    (hu : ∀ v : ZeroSobolev S,
      ⟪coefficientCLM A C hA.aestronglyMeasurable hC (sobolevDerivative T u),sobolevDerivative S v⟫_ℝ = 0)
    (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ Metric.ball 0 R)
    (K D : ℝ) (hK : ∀ x, ‖χ x‖ ≤ K) (hD : ∀ x, ‖gradient χ x‖ ≤ D)
    (a : E3) (h : ℝ) (hRS : R+‖h • a‖ ≤ S) :
    ‖scalarFieldCLM χ hχ.continuous K hK (finiteDifferenceL2 a h (sobolevDerivative T u))‖ ≤
      (((2*C+2)/c+1)*(D+K*L))*‖a‖*‖sobolevDerivative T u‖ := by
  let w := finiteDifferenceSobolev T a h u
  let F := -(differenceCoefficientCLM A L hA hL a h (sobolevDerivative T u))
  have hw := weak_caccioppoli_forcing R (T+‖h • a‖) (shiftedCoefficient A (h • a)) C c hc
    (shiftedCoefficient_continuous A hA (h • a)).aestronglyMeasurable
    (shiftedCoefficient_bound A C hC (h • a)) (fun x v ↦ hpos (x+h • a) v) w F
    (fun v ↦ weak_finiteDifference_equation R S T A C L hA hC hL u hu a h hRS v)
    χ hχ hsupp K D hK hD
  change ‖scalarFieldCLM χ hχ.continuous K hK (finiteDifferenceL2 a h (sobolevDerivative T u))‖ ≤ _ at hw
  have hC0 : 0 ≤ C := (norm_nonneg (A 0)).trans (hC 0)
  have hK0 : 0 ≤ K := (norm_nonneg (χ 0)).trans (hK 0)
  have hD0 : 0 ≤ D := (norm_nonneg (gradient χ 0)).trans (hD 0)
  have hB0 : 0 ≤ (2*C+2)/c+1 := by positivity
  have hq : ‖gradientFieldCLM χ hχ D hD (sobolevValue (T+‖h • a‖) w)‖ ≤
      D*‖a‖*‖sobolevDerivative T u‖ := by
    change ‖gradientFieldCLM χ hχ D hD (finiteDifferenceL2 a h (sobolevValue T u))‖ ≤ _
    exact (gradientFieldCLM_norm χ hχ D hD _).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (sobolev_finiteDifference_bound T u a h) hD0)
  have hr : ‖scalarFieldCLM χ hχ.continuous K hK F‖ ≤ K*L*‖a‖*‖sobolevDerivative T u‖ := by
    have hF : ‖F‖ ≤ L*‖a‖*‖sobolevDerivative T u‖ := by
      simpa only [F,norm_neg] using differenceCoefficientCLM_norm A L hA hL a h (sobolevDerivative T u)
    exact (scalarFieldCLM_norm χ hχ.continuous K hK F).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hF hK0)
  calc
    _ ≤ ((2*C+2)/c+1)*(‖gradientFieldCLM χ hχ D hD (sobolevValue (T+‖h • a‖) w)‖+
      ‖scalarFieldCLM χ hχ.continuous K hK F‖) := hw
    _ ≤ ((2*C+2)/c+1)*(D*‖a‖*‖sobolevDerivative T u‖+K*L*‖a‖*‖sobolevDerivative T u‖) :=
      mul_le_mul_of_nonneg_left (add_le_add hq hr) hB0
    _ = _ := by ring

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
