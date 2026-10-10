import OAI.Geometry.Riemannian.HarmonicCore.Sobolev
import OAI.Geometry.Riemannian.HarmonicCore.Energy

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise
open scoped NNReal ENNReal

namespace HarmonicCounterexample.Main.SmoothMetric3
section FieldMultiplier
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma field_memLp (A : E3 → V →L[ℝ] W) (C : ℝ)
    (hA : AEStronglyMeasurable A (volume : Measure E3))
    (hbound : ∀ x, ‖A x‖ ≤ C) (u : Lp V 2 (volume : Measure E3)) :
    MemLp (fun x ↦ A x (u x)) 2 (volume : Measure E3) := by
  refine (Lp.memLp u).of_le_mul (c:=C)
    ((ContinuousLinearMap.id ℝ (V →L[ℝ] W)).aestronglyMeasurable_comp₂ hA (Lp.aestronglyMeasurable u)) ?_
  exact Filter.Eventually.of_forall fun x ↦
    (A x).le_opNorm (u x) |>.trans (mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _))

noncomputable def fieldLinear (A : E3 → V →L[ℝ] W) (C : ℝ)
    (hA : AEStronglyMeasurable A (volume : Measure E3))
    (hbound : ∀ x, ‖A x‖ ≤ C) : Lp V 2 (volume : Measure E3) →ₗ[ℝ] Lp W 2 (volume : Measure E3) where
  toFun u := (field_memLp A C hA hbound u).toLp (fun x ↦ A x (u x))
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(field_memLp A C hA hbound (u+v)).coeFn_toLp,
      (field_memLp A C hA hbound u).coeFn_toLp,
      (field_memLp A C hA hbound v).coeFn_toLp,
      Lp.coeFn_add u v, Lp.coeFn_add
        ((field_memLp A C hA hbound u).toLp _) ((field_memLp A C hA hbound v).toLp _)] with x h1 h2 h3 h4 h5
    simp only [h1,h5,Pi.add_apply,h2,h3,h4,map_add]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [(field_memLp A C hA hbound (c • u)).coeFn_toLp,
      (field_memLp A C hA hbound u).coeFn_toLp,
      Lp.coeFn_smul c u, Lp.coeFn_smul c ((field_memLp A C hA hbound u).toLp _)] with x h1 h2 h3 h4
    simp only [RingHom.id_apply,h1,h4,Pi.smul_apply,h2,h3,map_smul]

lemma fieldLinear_norm (A : E3 → V →L[ℝ] W) (C : ℝ)
    (hA : AEStronglyMeasurable A (volume : Measure E3))
    (hbound : ∀ x, ‖A x‖ ≤ C) (u : Lp V 2 (volume : Measure E3)) :
    ‖fieldLinear A C hA hbound u‖ ≤ C * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(field_memLp A C hA hbound u).coeFn_toLp] with x hx
  change ‖((field_memLp A C hA hbound u).toLp _) x‖ ≤ C * ‖u x‖
  rw [hx]
  exact (A x).le_opNorm (u x) |>.trans (mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _))

noncomputable def fieldCLM (A : E3 → V →L[ℝ] W) (C : ℝ)
    (hA : AEStronglyMeasurable A (volume : Measure E3))
    (hbound : ∀ x, ‖A x‖ ≤ C) : Lp V 2 (volume : Measure E3) →L[ℝ] Lp W 2 (volume : Measure E3) :=
  (fieldLinear A C hA hbound).mkContinuous C (fieldLinear_norm A C hA hbound)

lemma fieldCLM_coe (A : E3 → V →L[ℝ] W) (C : ℝ)
    (hA : AEStronglyMeasurable A (volume : Measure E3))
    (hbound : ∀ x, ‖A x‖ ≤ C) (u : Lp V 2 (volume : Measure E3)) :
    (fieldCLM A C hA hbound u : E3 → W) =ᵐ[volume] (fun x ↦ A x (u x)) :=
  (field_memLp A C hA hbound u).coeFn_toLp
end FieldMultiplier

lemma gradient_mul_smooth {u v : E3 → ℝ} (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) :
    gradient (fun x ↦ u x * v x) = fun x ↦ u x • gradient v x + v x • gradient u x := by
  funext x
  simp only [gradient]
  rw [fderiv_fun_mul (hu.differentiable (by simp) x) (hv.differentiable (by simp) x),map_add,map_smul,map_smul]

noncomputable def scalarFieldCLM {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (χ : E3 → ℝ) (hχ : Continuous χ) (C : ℝ) (hC : ∀ x, ‖χ x‖ ≤ C) :
    Lp V 2 (volume : Measure E3) →L[ℝ] Lp V 2 (volume : Measure E3) :=
  fieldCLM (fun x ↦ χ x • ContinuousLinearMap.id ℝ V) C
    ((hχ.smul continuous_const).aestronglyMeasurable)
    (fun x ↦ by
      rw [norm_smul]
      exact (mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le).trans (hC x))

lemma scalarFieldCLM_coe {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (χ : E3 → ℝ) (hχ : Continuous χ) (C : ℝ) (hC : ∀ x, ‖χ x‖ ≤ C)
    (u : Lp V 2 (volume : Measure E3)) :
    (scalarFieldCLM χ hχ C hC u : E3 → V) =ᵐ[volume] fun x ↦ χ x • u x := by
  exact fieldCLM_coe _ _ _ _ u

noncomputable def gradientFieldCLM (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (D : ℝ) (hD : ∀ x, ‖gradient χ x‖ ≤ D) : ValueL2 →L[ℝ] DerivativeL2 :=
  fieldCLM (fun x ↦ (ContinuousLinearMap.id ℝ ℝ).smulRight (gradient χ x)) D
    (by
      have hc : Continuous (fun x ↦ (ContinuousLinearMap.id ℝ ℝ).smulRight (gradient χ x)) :=
        (((ContinuousLinearMap.smulRightL ℝ ℝ E3) (ContinuousLinearMap.id ℝ ℝ)).continuous).comp
          (gradient_continuous hχ)
      exact hc.aestronglyMeasurable)
    (fun x ↦ by simpa only [ContinuousLinearMap.norm_smulRight_apply,
      ContinuousLinearMap.norm_id,one_mul] using hD x)

lemma gradientFieldCLM_coe (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (D : ℝ) (hD : ∀ x, ‖gradient χ x‖ ≤ D) (u : ValueL2) :
    (gradientFieldCLM χ hχ D hD u : E3 → E3) =ᵐ[volume] fun x ↦ u x • gradient χ x :=
  fieldCLM_coe _ _ _ _ u

noncomputable def localizePair (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (C D : ℝ) (hC : ∀ x, ‖χ x‖ ≤ C) (hD : ∀ x, ‖gradient χ x‖ ≤ D) :
    SobolevPair →L[ℝ] SobolevPair :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ ValueL2 DerivativeL2).symm.toContinuousLinearMap.comp
    (((scalarFieldCLM χ hχ.continuous C hC).comp (WithLp.fstL 2 ℝ ValueL2 DerivativeL2)).prod
      (((scalarFieldCLM χ hχ.continuous C hC).comp (WithLp.sndL 2 ℝ ValueL2 DerivativeL2)) +
        ((gradientFieldCLM χ hχ D hD).comp (WithLp.fstL 2 ℝ ValueL2 DerivativeL2))))

noncomputable def DirichletTest.localize {R : ℝ} (u : DirichletTest R)
    (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ) : DirichletTest R :=
  ⟨fun x ↦ χ x * (u:E3 → ℝ) x,hχ.mul u.property.1,u.property.2.1.mul_left,
    (tsupport_mul_subset_right (f:=χ) (g:=(u:E3 → ℝ))).trans u.property.2.2⟩

lemma localizePair_test (R : ℝ) (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (C D : ℝ) (hC : ∀ x, ‖χ x‖ ≤ C) (hD : ∀ x, ‖gradient χ x‖ ≤ D)
    (u : DirichletTest R) :
    localizePair χ hχ C D hC hD (testGraph R u) =
      testGraph R (u.localize χ hχ) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ ValueL2 DerivativeL2).injective
  apply Prod.ext
  · change scalarFieldCLM χ hχ.continuous C hC (testValueLinear R u) =
      testValueLinear R (u.localize χ hχ)
    apply Lp.ext
    filter_upwards [scalarFieldCLM_coe χ hχ.continuous C hC (testValueLinear R u),
      u.value_memLp.coeFn_toLp, (u.localize χ hχ).value_memLp.coeFn_toLp] with x h1 h2 h3
    change (scalarFieldCLM χ hχ.continuous C hC (testValueLinear R u)) x =
      ((u.localize χ hχ).value_memLp.toLp _) x
    rw [h1, h3]
    change χ x * (u.value_memLp.toLp _) x = χ x * (u:E3 → ℝ) x
    rw [h2]
  · change scalarFieldCLM χ hχ.continuous C hC (testDerivativeLinear R u) +
      gradientFieldCLM χ hχ D hD (testValueLinear R u) =
      testDerivativeLinear R (u.localize χ hχ)
    apply Lp.ext
    filter_upwards [scalarFieldCLM_coe χ hχ.continuous C hC (testDerivativeLinear R u),
      gradientFieldCLM_coe χ hχ D hD (testValueLinear R u),
      Lp.coeFn_add (scalarFieldCLM χ hχ.continuous C hC (testDerivativeLinear R u))
        (gradientFieldCLM χ hχ D hD (testValueLinear R u)),
      u.value_memLp.coeFn_toLp, u.derivative_memLp.coeFn_toLp,
      (u.localize χ hχ).derivative_memLp.coeFn_toLp] with x h1 h2 h3 h4 h5 h6
    change ((scalarFieldCLM χ hχ.continuous C hC (testDerivativeLinear R u) +
      gradientFieldCLM χ hχ D hD (testValueLinear R u))) x =
      ((u.localize χ hχ).derivative_memLp.toLp _) x
    rw [h3, Pi.add_apply, h1, h2, h6]
    change χ x • (u.derivative_memLp.toLp _) x + (u.value_memLp.toLp _) x • gradient χ x =
      gradient (fun y ↦ χ y * (u:E3 → ℝ) y) x
    rw [h4,h5,gradient_mul_smooth hχ u.property.1]

lemma localizePair_preserves (R : ℝ) (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (C D : ℝ) (hC : ∀ x, ‖χ x‖ ≤ C) (hD : ∀ x, ‖gradient χ x‖ ≤ D)
    (u : ZeroSobolev R) :
    localizePair χ hχ C D hC hD (u:SobolevPair) ∈ zeroSobolevSpace R := by
  have hclosed : IsClosed ((localizePair χ hχ C D hC hD) ⁻¹' (zeroSobolevSpace R : Set SobolevPair)) :=
    (testGraph R).range.isClosed_topologicalClosure.preimage (localizePair χ hχ C D hC hD).continuous
  apply closure_minimal (s:=Set.range (testGraph R)) ?_ hclosed u.property
  rintro _ ⟨v,rfl⟩
  change localizePair χ hχ C D hC hD (testGraph R v) ∈ zeroSobolevSpace R
  rw [localizePair_test]
  exact subset_closure ⟨v.localize χ hχ,rfl⟩

noncomputable def localizeSobolev (R : ℝ) (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (C D : ℝ) (hC : ∀ x, ‖χ x‖ ≤ C) (hD : ∀ x, ‖gradient χ x‖ ≤ D)
    (u : ZeroSobolev R) : ZeroSobolev R :=
  ⟨localizePair χ hχ C D hC hD u,localizePair_preserves R χ hχ C D hC hD u⟩

lemma localizeSobolev_value (R : ℝ) (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (C D : ℝ) (hC : ∀ x, ‖χ x‖ ≤ C) (hD : ∀ x, ‖gradient χ x‖ ≤ D)
    (u : ZeroSobolev R) :
    sobolevValue R (localizeSobolev R χ hχ C D hC hD u) =
      scalarFieldCLM χ hχ.continuous C hC (sobolevValue R u) := rfl

lemma localizeSobolev_derivative (R : ℝ) (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (C D : ℝ) (hC : ∀ x, ‖χ x‖ ≤ C) (hD : ∀ x, ‖gradient χ x‖ ≤ D)
    (u : ZeroSobolev R) :
    sobolevDerivative R (localizeSobolev R χ hχ C D hC hD u) =
      scalarFieldCLM χ hχ.continuous C hC (sobolevDerivative R u) +
      gradientFieldCLM χ hχ D hD (sobolevValue R u) := rfl

noncomputable def DirichletTest.cutoff {S : ℝ} (u : DirichletTest S)
    (R : ℝ) (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hsupp : tsupport χ ⊆ Metric.ball 0 R) : DirichletTest R :=
  ⟨fun x ↦ χ x * (u:E3 → ℝ) x,hχ.mul u.property.1,u.property.2.1.mul_left,
    (tsupport_mul_subset_left (f:=χ) (g:=(u:E3 → ℝ))).trans hsupp⟩

lemma localizePair_cutoff (R S : ℝ) (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hsupp : tsupport χ ⊆ Metric.ball 0 R)
    (C D : ℝ) (hC : ∀ x, ‖χ x‖ ≤ C) (hD : ∀ x, ‖gradient χ x‖ ≤ D)
    (u : DirichletTest S) :
    localizePair χ hχ C D hC hD (testGraph S u) =
      testGraph R (u.cutoff R χ hχ hsupp) := by
  rw [localizePair_test]
  rfl

lemma localizePair_mem_smaller (R S : ℝ) (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hsupp : tsupport χ ⊆ Metric.ball 0 R)
    (C D : ℝ) (hC : ∀ x, ‖χ x‖ ≤ C) (hD : ∀ x, ‖gradient χ x‖ ≤ D)
    (u : ZeroSobolev S) :
    localizePair χ hχ C D hC hD (u:SobolevPair) ∈ zeroSobolevSpace R := by
  have hclosed : IsClosed ((localizePair χ hχ C D hC hD) ⁻¹' (zeroSobolevSpace R : Set SobolevPair)) :=
    (testGraph R).range.isClosed_topologicalClosure.preimage (localizePair χ hχ C D hC hD).continuous
  apply closure_minimal (s:=Set.range (testGraph S)) ?_ hclosed u.property
  rintro _ ⟨v,rfl⟩
  change localizePair χ hχ C D hC hD (testGraph S v) ∈ zeroSobolevSpace R
  rw [localizePair_cutoff R S χ hχ hsupp]
  exact subset_closure ⟨v.cutoff R χ hχ hsupp,rfl⟩

noncomputable def cutoffSobolev (R S : ℝ) (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hsupp : tsupport χ ⊆ Metric.ball 0 R)
    (C D : ℝ) (hC : ∀ x, ‖χ x‖ ≤ C) (hD : ∀ x, ‖gradient χ x‖ ≤ D)
    (u : ZeroSobolev S) : ZeroSobolev R :=
  ⟨localizePair χ hχ C D hC hD u,localizePair_mem_smaller R S χ hχ hsupp C D hC hD u⟩

lemma scalarField_inner {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (χ : E3 → ℝ) (hχ : Continuous χ) (K : ℝ) (hK : ∀ x, ‖χ x‖ ≤ K)
    (u v : Lp V 2 (volume : Measure E3)) :
    ⟪scalarFieldCLM χ hχ K hK u,v⟫_ℝ = ⟪u,scalarFieldCLM χ hχ K hK v⟫_ℝ := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [scalarFieldCLM_coe χ hχ K hK u,scalarFieldCLM_coe χ hχ K hK v] with x h1 h2
  simp only [h1,h2,inner_smul_left,inner_smul_right,conj_trivial]

lemma scalarField_coefficient_commute (A : E3 → E3 →L[ℝ] E3) (C : ℝ)
    (hA : AEStronglyMeasurable A (volume : Measure E3)) (hbound : ∀ x, ‖A x‖ ≤ C)
    (χ : E3 → ℝ) (hχ : Continuous χ) (K : ℝ) (hK : ∀ x, ‖χ x‖ ≤ K)
    (u : DerivativeL2) :
    scalarFieldCLM χ hχ K hK (coefficientCLM A C hA hbound u) =
      coefficientCLM A C hA hbound (scalarFieldCLM χ hχ K hK u) := by
  apply Lp.ext
  filter_upwards [scalarFieldCLM_coe χ hχ K hK (coefficientCLM A C hA hbound u),
    (coefficient_memLp A C hA hbound u).coeFn_toLp,
    (coefficient_memLp A C hA hbound (scalarFieldCLM χ hχ K hK u)).coeFn_toLp,
    scalarFieldCLM_coe χ hχ K hK u] with x h1 h2 h3 h4
  change (scalarFieldCLM χ hχ K hK (coefficientCLM A C hA hbound u)) x =
    ((coefficient_memLp A C hA hbound (scalarFieldCLM χ hχ K hK u)).toLp _) x
  rw [h1,h3,h4]
  change χ x • ((coefficient_memLp A C hA hbound u).toLp _) x = _
  rw [h2,map_smul]

lemma gradientField_scalar_commute (χ : E3 → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (K D : ℝ) (hK : ∀ x, ‖χ x‖ ≤ K) (hD : ∀ x, ‖gradient χ x‖ ≤ D)
    (u : ValueL2) :
    gradientFieldCLM χ hχ D hD (scalarFieldCLM χ hχ.continuous K hK u) =
      scalarFieldCLM χ hχ.continuous K hK (gradientFieldCLM χ hχ D hD u) := by
  apply Lp.ext
  filter_upwards [gradientFieldCLM_coe χ hχ D hD (scalarFieldCLM χ hχ.continuous K hK u),
    scalarFieldCLM_coe χ hχ.continuous K hK u,
    scalarFieldCLM_coe χ hχ.continuous K hK (gradientFieldCLM χ hχ D hD u),
    gradientFieldCLM_coe χ hχ D hD u] with x h1 h2 h3 h4
  rw [h1,h2,h3,h4,smul_smul]
  rfl

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
