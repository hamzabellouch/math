import OAI.Geometry.Riemannian.HarmonicCore.Translation
import OAI.Geometry.Riemannian.HarmonicCore.Caccioppoli

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal

namespace HarmonicCounterexample.Main.SmoothMetric3
lemma zeroSobolevSpace_mono {R S : ℝ} (hRS : R ≤ S) : zeroSobolevSpace R ≤ zeroSobolevSpace S := by
  intro z hz
  apply closure_minimal (s:=Set.range (testGraph R)) ?_ (testGraph S).range.isClosed_topologicalClosure hz
  rintro _ ⟨u,rfl⟩
  let v : DirichletTest S := ⟨(u:E3 → ℝ),u.property.1,u.property.2.1,
    u.property.2.2.trans (Metric.ball_subset_ball hRS)⟩
  exact subset_closure ⟨v,rfl⟩

noncomputable def includeSobolev {R S : ℝ} (hRS : R ≤ S) (u : ZeroSobolev R) : ZeroSobolev S :=
  ⟨u,zeroSobolevSpace_mono hRS u.property⟩

noncomputable def finiteDifferenceL2 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : E3) (h : ℝ) : Lp V 2 (volume : Measure E3) →L[ℝ] Lp V 2 (volume : Measure E3) :=
  h⁻¹ • (translateL2 (h • a) - ContinuousLinearMap.id ℝ _)

lemma finiteDifferenceL2_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : E3) (h : ℝ) (u : Lp V 2 (volume : Measure E3)) :
    finiteDifferenceL2 a h u = h⁻¹ • (translateL2 (h • a) u-u) := rfl

lemma finiteDifferenceL2_coe {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : E3) (h : ℝ) (u : Lp V 2 (volume : Measure E3)) :
    (finiteDifferenceL2 a h u : E3 → V) =ᵐ[volume] fun x ↦ h⁻¹ • (u (x+h • a)-u x) := by
  filter_upwards [Lp.coeFn_smul h⁻¹ (translateL2 (h • a) u-u),
    Lp.coeFn_sub (translateL2 (h • a) u) u,translateL2_coe (h • a) u] with x h1 h2 h3
  change (h⁻¹ • (translateL2 (h • a) u-u) : Lp V 2 (volume : Measure E3)) x = _
  rw [h1,Pi.smul_apply,h2,Pi.sub_apply,h3]

lemma finiteDifferenceL2_inner {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (a : E3) (h : ℝ) (u v : Lp V 2 (volume : Measure E3)) :
    ⟪finiteDifferenceL2 a h u,v⟫_ℝ = -⟪u,finiteDifferenceL2 a (-h) v⟫_ℝ := by
  rw [finiteDifferenceL2_apply,finiteDifferenceL2_apply,real_inner_smul_left,
    real_inner_smul_right,inner_sub_left,inner_sub_right,translateL2_inner,neg_smul,inv_neg]
  ring

noncomputable def finiteDifferencePair (a : E3) (h : ℝ) : SobolevPair →L[ℝ] SobolevPair :=
  h⁻¹ • (translatePair (h • a)-ContinuousLinearMap.id ℝ _)

lemma finiteDifferencePair_mem (R : ℝ) (a : E3) (h : ℝ) (u : ZeroSobolev R) :
    finiteDifferencePair a h (u:SobolevPair) ∈ zeroSobolevSpace (R+‖h • a‖) := by
  apply (zeroSobolevSpace (R+‖h • a‖)).smul_mem
  apply (zeroSobolevSpace (R+‖h • a‖)).sub_mem
  · exact translatePair_mem R (h • a) u
  · exact zeroSobolevSpace_mono (le_add_of_nonneg_right (norm_nonneg _)) u.property

noncomputable def finiteDifferenceSobolev (R : ℝ) (a : E3) (h : ℝ) (u : ZeroSobolev R) :
    ZeroSobolev (R+‖h • a‖) := ⟨finiteDifferencePair a h u,finiteDifferencePair_mem R a h u⟩

lemma finiteDifferenceSobolev_value (R : ℝ) (a : E3) (h : ℝ) (u : ZeroSobolev R) :
    sobolevValue (R+‖h • a‖) (finiteDifferenceSobolev R a h u) = finiteDifferenceL2 a h (sobolevValue R u) := rfl

lemma finiteDifferenceSobolev_derivative (R : ℝ) (a : E3) (h : ℝ) (u : ZeroSobolev R) :
    sobolevDerivative (R+‖h • a‖) (finiteDifferenceSobolev R a h u) = finiteDifferenceL2 a h (sobolevDerivative R u) := rfl

lemma sobolev_finiteDifference_bound (R : ℝ) (u : ZeroSobolev R) (a : E3) (h : ℝ) :
    ‖finiteDifferenceL2 a h (sobolevValue R u)‖ ≤ ‖a‖ * ‖sobolevDerivative R u‖ := by
  rw [finiteDifferenceL2_apply,norm_smul,norm_inv]
  by_cases hh : h = 0
  · simp [hh,mul_nonneg (norm_nonneg a) (norm_nonneg _)]
  · calc
      _ ≤ ‖h‖⁻¹ * (‖h • a‖ * ‖sobolevDerivative R u‖) :=
        mul_le_mul_of_nonneg_left (sobolev_translation_bound R u (h • a)) (inv_nonneg.mpr (norm_nonneg h))
      _ = ‖a‖ * ‖sobolevDerivative R u‖ := by rw [norm_smul,← mul_assoc,← mul_assoc,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hh),one_mul]

theorem weak_caccioppoli_forcing (R S : ℝ) (A : E3 → E3 →L[ℝ] E3) (C c : ℝ) (hc : 0 < c)
    (hA : AEStronglyMeasurable A (volume : Measure E3))
    (hbound : ∀ x, ‖A x‖ ≤ C) (hpos : ∀ x v, c * ‖v‖^2 ≤ ⟪A x v,v⟫_ℝ)
    (u : ZeroSobolev S) (F : DerivativeL2)
    (hu : ∀ v : ZeroSobolev R,
      ⟪coefficientCLM A C hA hbound (sobolevDerivative S u),sobolevDerivative R v⟫_ℝ =
        ⟪F,sobolevDerivative R v⟫_ℝ)
    (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ Metric.ball 0 R)
    (K D : ℝ) (hK : ∀ x, ‖χ x‖ ≤ K) (hD : ∀ x, ‖gradient χ x‖ ≤ D) :
    ‖scalarFieldCLM χ hχ.continuous K hK (sobolevDerivative S u)‖ ≤
      ((2*C+2)/c+1) * (‖gradientFieldCLM χ hχ D hD (sobolevValue S u)‖ +
        ‖scalarFieldCLM χ hχ.continuous K hK F‖) := by
  let T : DerivativeL2 →L[ℝ] DerivativeL2 := scalarFieldCLM χ hχ.continuous K hK
  let B : DerivativeL2 →L[ℝ] DerivativeL2 := coefficientCLM A C hA hbound
  let du : DerivativeL2 := sobolevDerivative S u
  let p : DerivativeL2 := T du
  let q : DerivativeL2 := gradientFieldCLM χ hχ D hD (sobolevValue S u)
  let r : DerivativeL2 := T F
  let v := cutoffSobolev R S χ hχ hsupp K D hK hD u
  let w := localizeSobolev R χ hχ K D hK hD v
  have hw : sobolevDerivative R w = T (p+q)+T q := by
    change T (p+q)+gradientFieldCLM χ hχ D hD
      (scalarFieldCLM χ hχ.continuous K hK (sobolevValue S u)) = _
    rw [gradientField_scalar_commute]
  have hmove (z : DerivativeL2) : ⟪B du,T z⟫_ℝ = ⟪B p,z⟫_ℝ := by
    change ⟪coefficientCLM A C hA hbound du,scalarFieldCLM χ hχ.continuous K hK z⟫_ℝ = _
    rw [← scalarField_inner,scalarField_coefficient_commute]
  have hFmove (z : DerivativeL2) : ⟪F,T z⟫_ℝ = ⟪r,z⟫_ℝ := by
    exact (scalarField_inner χ hχ.continuous K hK F z).symm
  have he : ⟪B p,p⟫_ℝ+2*⟪B p,q⟫_ℝ = ⟪r,p⟫_ℝ+2*⟪r,q⟫_ℝ := by
    have h := hu w
    change ⟪B du,sobolevDerivative R w⟫_ℝ = ⟪F,sobolevDerivative R w⟫_ℝ at h
    rw [hw,inner_add_right,inner_add_right,hmove,hmove,hFmove,hFmove,
      inner_add_right,inner_add_right] at h
    linarith only [h]
  have hp : c*‖p‖^2 ≤ ⟪B p,p⟫_ℝ := coefficientCLM_coercive A C c hA hbound hpos p
  have hcross := real_inner_le_norm (-(B p)) q
  rw [inner_neg_left,norm_neg] at hcross
  have hnorm : ‖B p‖ ≤ C*‖p‖ := coefficientLinear_norm A C hA hbound p
  have hC : 0 ≤ C := (norm_nonneg (A 0)).trans (hbound 0)
  have henergy : c*‖p‖^2 ≤ 2*C*‖p‖*‖q‖ + ‖r‖*‖p‖ + 2*‖r‖*‖q‖ := by
    have hm := mul_le_mul_of_nonneg_right hnorm (norm_nonneg q)
    have h1 := real_inner_le_norm r p
    have h2 := real_inner_le_norm r q
    nlinarith only [hp, he, hcross, hm, h1, h2]
  let b : ℝ := ‖q‖+‖r‖
  have hb : 0 ≤ b := add_nonneg (norm_nonneg q) (norm_nonneg r)
  have henergy' : c*‖p‖^2 ≤ (2*C+1)*‖p‖*b+b^2 := by
    have h1 := mul_nonneg (mul_nonneg hC (norm_nonneg p)) (norm_nonneg r)
    have h2 := mul_nonneg (norm_nonneg p) (norm_nonneg q)
    dsimp [b]
    nlinarith only [henergy, h1, h2, sq_nonneg ‖q‖, sq_nonneg ‖r‖]
  change ‖p‖ ≤ ((2*C+2)/c+1)*b
  by_contra hn
  have hpn : ((2*C+2)/c+1)*b < ‖p‖ := lt_of_not_ge hn
  have hd : 1 ≤ (2*C+2)/c+1 := by
    have hd0 : 0 ≤ (2*C+2)/c := by positivity
    linarith only [hd0]
  have hpb : b ≤ ‖p‖ := (le_mul_of_one_le_left hb hd).trans hpn.le
  have hp0 : 0 < ‖p‖ := (mul_nonneg (zero_le_one.trans hd) hb).trans_lt hpn
  have hcp : (2*C+2+c)*b < c*‖p‖ := by
    have h := mul_lt_mul_of_pos_left hpn hc
    have hid : c*((2*C+2)/c+1) = 2*C+2+c := by field_simp
    simpa only [←mul_assoc,hid] using h
  have hstrict := mul_lt_mul_of_pos_right hcp hp0
  have hbb := mul_le_mul_of_nonneg_right hpb hb
  have hnon := mul_nonneg (mul_nonneg hc.le (norm_nonneg p)) hb
  nlinarith only [henergy', hstrict, hbb, hnon]

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
