import OAI.Probability.ProjectionMoments.GaussianDensity

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace ProjectionMoments
attribute [fun_prop] measurable_lowerDensity

section Rotations
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

instance rotationLaw_probability : IsProbabilityMeasure (rotationLaw E) := by
  constructor
  simp only [rotationLaw, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel ((ne_of_gt (isOpen_univ.measure_pos (Measure.haar : Measure (Rotation E)) Set.univ_nonempty))) (measure_ne_top _ _)

instance rotationLaw_haar : (rotationLaw E).IsHaarMeasure := by
  unfold rotationLaw
  apply Measure.IsHaarMeasure.smul _
  · exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)
  · exact ENNReal.inv_ne_top.mpr (ne_of_gt (isOpen_univ.measure_pos (Measure.haar : Measure (Rotation E)) Set.univ_nonempty))

instance rotationLaw_right : (rotationLaw E).IsMulRightInvariant := by
  constructor
  intro Q
  let μ := (rotationLaw E).map (fun O => O * Q)
  have hprob : IsProbabilityMeasure μ := inferInstance
  have he := Measure.isMulInvariant_eq_smul_of_compactSpace μ (rotationLaw E)
  have hc := congrArg (fun ν : Measure (Rotation E) => ν Set.univ) he
  simp only [Measure.smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one] at hc
  have hc' : Measure.haarScalarFactor μ (rotationLaw E) = 1 :=
    ENNReal.coe_injective hc.symm
  simpa [hc'] using he

variable {E}

lemma rotation_transitive {ι : Type*} [Fintype ι] {u v : ι → E}
    (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v) :
    ∃ O : Rotation E, ∀ i, (O : E →L[ℝ] E) (u i) = v i := by
  classical
  let U := Submodule.span ℝ (Set.range u)
  let V := Submodule.span ℝ (Set.range v)
  let bu : OrthonormalBasis ι ℝ U := (Module.Basis.span hu.linearIndependent).toOrthonormalBasis
    (by convert! orthonormal_span hu using 1; ext i; simp)
  let bv : OrthonormalBasis ι ℝ V := (Module.Basis.span hv.linearIndependent).toOrthonormalBasis
    (by convert! orthonormal_span hv using 1; ext i; simp)
  let e : U ≃ₗᵢ[ℝ] V := bu.repr.trans bv.repr.symm
  let L : U →ₗᵢ[ℝ] E := V.subtypeₗᵢ.comp e.toLinearIsometry
  let O : E ≃ₗᵢ[ℝ] E := L.extend.toLinearIsometryEquiv rfl
  refine ⟨Unitary.linearIsometryEquiv.symm O, ?_⟩
  intro i
  change O (u i) = v i
  change L.extend (u i) = v i
  have he : e (bu i) = bv i := by
    simp only [e, LinearIsometryEquiv.trans_apply, OrthonormalBasis.repr_self,
      OrthonormalBasis.repr_symm_single]
  have hbui : (bu i : E) = u i := by simp [bu, Module.Basis.span_apply]
  have hbvi : (bv i : E) = v i := by simp [bv, Module.Basis.span_apply]
  rw [← hbui, LinearIsometry.extend_apply]
  change (e (bu i) : E) = _
  rw [he, hbvi]

variable [MeasurableSpace E] [BorelSpace E]

lemma measurable_rotateRows {ι : Type*} [Fintype ι] :
    Measurable (fun z : Rotation E × (ι → E) => rotateRows z.1 z.2) := by
  apply Continuous.measurable
  apply continuous_pi
  intro i
  exact (continuous_subtype_val.comp continuous_fst).clm_apply (continuous_apply i |>.comp continuous_snd)

@[fun_prop] lemma measurable_rotateRows_left {ι : Type*} [Fintype ι] (v : ι → E) :
    Measurable (fun O : Rotation E => rotateRows O v) :=
  measurable_rotateRows.comp (measurable_id.prodMk measurable_const)

@[fun_prop] lemma measurable_rotateRows_right {ι : Type*} [Fintype ι] (O : Rotation E) :
    Measurable (fun v : ι → E => rotateRows O v) :=
  measurable_rotateRows.comp (measurable_const.prodMk measurable_id)

omit [MeasurableSpace E] [BorelSpace E] in
lemma rotateRows_mul [MeasurableSpace E] [BorelSpace E] {ι : Type*} (O Q : Rotation E) (v : ι → E) :
    rotateRows (O*Q) v = rotateRows O (rotateRows Q v) := rfl

lemma rotationLaw_orbit_eq {ι : Type*} [Fintype ι] {u v : ι → E}
    (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v) :
    (rotationLaw E).map (fun O => rotateRows O u) =
      (rotationLaw E).map (fun O => rotateRows O v) := by
  obtain ⟨Q, hQ⟩ := rotation_transitive hu hv
  have he : rotateRows Q u = v := funext hQ
  have hm : Measurable (fun O : Rotation E => rotateRows O u) :=
    measurable_rotateRows.comp (measurable_id.prodMk measurable_const)
  rw [← he]
  conv_lhs => rw [← (measurePreserving_mul_right (rotationLaw E) Q).map_eq]
  rw [Measure.map_map hm (by fun_prop)]
  rfl

lemma gaussianRows_rotation_invariant (m : ℕ) (O : Rotation E) :
    (Measure.pi (fun _ : Fin m => stdGaussian E)).map (rotateRows O) =
      Measure.pi (fun _ : Fin m => stdGaussian E) := by
  change (Measure.pi (fun _ : Fin m => stdGaussian E)).map
    (fun v i => O.val (v i)) = _
  rw [Measure.pi_map_pi (f := fun _ : Fin m => (O.val : E →L[ℝ] E))
    (fun _ => O.val.continuous.measurable.aemeasurable)]
  congr 1
  funext j
  exact stdGaussian_map (Unitary.linearIsometryEquiv O)

end Rotations

section Triangular
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma coordinateMap_apply [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {m : ℕ} (A : Fin m → E) (x : E) (i : Fin m) :
    coordinateMap A x i = ⟪x, A i⟫ := by
  change WithLp.ofLp (rowMap A x) i = _
  rw [rowMap_apply]

def rowJacobian {m : ℕ} (A : Fin m → E) : ℝ :=
  ∏ i, ‖gramSchmidt ℝ A i‖

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rowJacobian_pos [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {m : ℕ} {A : Fin m → E} (hA : LinearIndependent ℝ A) :
    0 < rowJacobian A := Finset.prod_pos (fun i _ => norm_pos_iff.mpr (gramSchmidt_ne_zero i hA))

lemma rows_factor {m : ℕ} (A : Fin m → E) (hA : LinearIndependent ℝ A) :
    ∃ u : Fin m → E, Orthonormal ℝ u ∧
      ∃ T : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ),
        (∀ x, coordinateMap A x = T (coordinateMap u x)) ∧
        (volume : Measure (Fin m → ℝ)).map T =
          (ENNReal.ofReal (rowJacobian A))⁻¹ • volume := by
  let u := gramSchmidtNormed ℝ A
  let R : Matrix (Fin m) (Fin m) ℝ :=
    Matrix.diagonal (fun i => ‖gramSchmidt ℝ A i‖) * NoiselessRegression.gsUpper m A
  have hu : Orthonormal ℝ u := gramSchmidtNormed_orthonormal hA
  have hn (i : Fin m) : ‖gramSchmidt ℝ A i‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (gramSchmidt_ne_zero i hA)
  have hexp (j : Fin m) : ∑ i, R i j • u i = A j := by
    rw [← NoiselessRegression.gsUpper_expansion m A j]
    apply Finset.sum_congr rfl
    intro i _
    simp only [R, u, Matrix.diagonal_mul, gramSchmidtNormed, smul_smul]
    congr 1
    simp [hn i, mul_comm]
  have hdet : R.transpose.det = rowJacobian A := by
    dsimp only [R, rowJacobian]
    rw [Matrix.det_transpose, Matrix.det_mul, Matrix.det_diagonal,
      NoiselessRegression.gsUpper_det, mul_one]
  have hd : R.transpose.det ≠ 0 := by rw [hdet]; exact (rowJacobian_pos hA).ne'
  let T := (R.transpose.toLinearEquiv' (Matrix.invertibleOfIsUnitDet R.transpose (isUnit_iff_ne_zero.mpr hd))).toContinuousLinearEquiv
  refine ⟨u, hu, T, ?_, ?_⟩
  · intro x
    ext j
    rw [coordinateMap_apply, ← hexp j]
    change ⟪x, ∑ i, R i j • u i⟫ = Matrix.mulVec R.transpose (coordinateMap u x) j
    simp only [inner_sum, inner_smul_right, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply, coordinateMap_apply]
  · change (volume : Measure (Fin m → ℝ)).map (Matrix.toLin' R.transpose) = _
    rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hd,
      abs_of_pos (inv_pos.mpr (by rw [hdet]; exact rowJacobian_pos hA)), hdet,
      ENNReal.ofReal_inv_of_pos (rowJacobian_pos hA)]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma norm_rowMap_le [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {m : ℕ} {u : Fin m → E} (hu : Orthonormal ℝ u) :
    ‖rowMap u‖ ≤ 1 := by
  apply (rowMap u).opNorm_le_bound zero_le_one
  intro x
  rw [one_mul]
  have h := hu.sum_inner_products_le (x := x) (s := Finset.univ)
  apply (sq_le_sq₀ (norm_nonneg (rowMap u x)) (norm_nonneg x)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  simpa only [rowMap_apply, Real.norm_eq_abs, sq_abs,
    WithLp.ofLp_toLp, real_inner_comm] using h

omit [MeasurableSpace E] [BorelSpace E] in
lemma rowJacobian_le [MeasurableSpace E] [BorelSpace E] {m : ℕ} (A : Fin m → E) :
    rowJacobian A ≤ ∏ i, ‖A i‖ := by
  apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
  rw [NoiselessRegression.norm_gramSchmidt_eq_infDist]
  simpa only [dist_zero_right] using
    Metric.infDist_le_dist_of_mem (x := A i) (Submodule.zero_mem (Submodule.span ℝ (A '' Set.Iio i)))

lemma coordinateMap_rotateRows {m : ℕ} (O : Rotation E) (A : Fin m → E) (x : E) :
    coordinateMap (rotateRows O A) x =
      coordinateMap A ((Unitary.linearIsometryEquiv O).symm x) := by
  ext i
  simp only [coordinateMap_apply, rotateRows]
  calc
    _ = ⟪(Unitary.linearIsometryEquiv O) (A i), x⟫ := real_inner_comm _ _
    _ = ⟪A i, (Unitary.linearIsometryEquiv O).symm x⟫ :=
      LinearIsometryEquiv.inner_map_eq_flip _ _ _
    _ = _ := real_inner_comm _ _

end Triangular

section CoordinateDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

@[fun_prop] lemma measurable_coordinateDensity (ν : Measure E) [SFinite ν] (m : ℕ) :
    Measurable (coordinateDensity ν m) := by
  exact (measurable_lowerDensity ν m).comp (by fun_prop)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rowMap_eq_toLp_coordinateMap [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {m : ℕ} (A : Fin m → E) :
    (rowMap A : E → Label m) = (WithLp.toLp 2) ∘ coordinateMap A := rfl

lemma coordinateDensity_is_density (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ)
    (A : Fin m → E) (hA : ν.map (coordinateMap A) ≪ (volume : Measure (Fin m → ℝ))) :
    volume.withDensity (fun y => coordinateDensity ν m (A,y)) = ν.map (coordinateMap A) := by
  have hr : ν.map (rowMap A) ≪ (volume : Measure (Label m)) := by
    rw [rowMap_eq_toLp_coordinateMap, ← Measure.map_map (by fun_prop) (by fun_prop),
      ← (PiLp.volume_preserving_toLp (Fin m)).map_eq]
    exact hA.map (by fun_prop)
  have h := congrArg (fun μ : Measure (Label m) => μ.map (MeasurableEquiv.toLp 2 (Fin m → ℝ)).symm)
    (lowerDensity_is_density ν m A hr)
  rw [map_withDensity_equiv _ _ _ (by fun_prop),
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin m)).map_eq,
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  exact h

def labelMoment (ν : Measure E) (m n : ℕ) (A : Fin m → E) : ℝ≥0∞ :=
  ∫⁻ y, coordinateDensity ν m (A,y)^(n+1)

@[fun_prop] lemma measurable_labelMoment (ν : Measure E) [SFinite ν] (m n : ℕ) :
    Measurable (labelMoment ν m n) := by
  exact Measurable.lintegral_prod_right (by fun_prop)

lemma labelMoment_factor (ν : Measure E) [IsFiniteMeasure ν] {m n : ℕ}
    (A u : Fin m → E) (T : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ))
    (hf : ∀ x, coordinateMap A x = T (coordinateMap u x))
    (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ∞)
    (hT : (volume : Measure (Fin m → ℝ)).map T = c • volume)
    (hu : ν.map (coordinateMap u) ≪ (volume : Measure (Fin m → ℝ))) :
    labelMoment ν m n A = c^n * labelMoment ν m n u := by
  have he : ν.map (coordinateMap A) = (ν.map (coordinateMap u)).map T := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    exact funext hf
  have ha : ν.map (coordinateMap A) ≪ (volume : Measure (Fin m → ℝ)) := by
    rw [he]
    have h := hu.map T.continuous.measurable
    rw [hT] at h
    exact h.trans Measure.smul_absolutelyContinuous
  apply density_moment_equiv volume T.toHomeomorph.toMeasurableEquiv c hc0 hct hT
    (by fun_prop) (by fun_prop)
  rw [coordinateDensity_is_density ν m A ha, coordinateDensity_is_density ν m u hu, he]
  rfl

end CoordinateDensity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

instance frameLaw_probability {m : ℕ} (u : Fin m → E) : IsProbabilityMeasure (frameLaw u) :=
  inferInstanceAs (IsProbabilityMeasure ((rotationLaw E).map (fun O => rotateRows O u)))

lemma frameLaw_eq {m : ℕ} {u v : Fin m → E} (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v) :
    frameLaw u = frameLaw v := rotationLaw_orbit_eq hu hv

def orbitMoment (ν : Measure E) (m n : ℕ) (A : Fin m → E) : ℝ≥0∞ :=
  ∫⁻ O, labelMoment ν m n (rotateRows O A) ∂rotationLaw E

@[fun_prop] lemma measurable_orbitMoment (ν : Measure E) [SFinite ν] (m n : ℕ) :
    Measurable (orbitMoment ν m n) := by
  apply Measurable.lintegral_prod_right
  exact (measurable_labelMoment ν m n).comp (measurable_rotateRows.comp measurable_swap)

lemma orbitMoment_eq_frame (ν : Measure E) [SFinite ν] (m n : ℕ) (u : Fin m → E) :
    orbitMoment ν m n u = ∫⁻ A, labelMoment ν m n A ∂frameLaw u := by
  rw [frameLaw, lintegral_map (measurable_labelMoment ν m n) (measurable_rotateRows_left u)]
  rfl

lemma orbitMoment_factor (ν : Measure E) [IsFiniteMeasure ν] {m n : ℕ}
    (u : Fin m → E) (hu : Orthonormal ℝ u)
    (hac : ∀ᵐ A ∂frameLaw u, ν.map (coordinateMap A) ≪ (volume : Measure (Fin m → ℝ)))
    (A : Fin m → E) (hA : LinearIndependent ℝ A) :
    orbitMoment ν m n A = (ENNReal.ofReal (rowJacobian A))⁻¹ ^ n * orbitMoment ν m n u := by
  obtain ⟨v, hv, T, hT, hvol⟩ := rows_factor A hA
  have hacv : ∀ᵐ O ∂rotationLaw E,
      ν.map (coordinateMap (rotateRows O v)) ≪ (volume : Measure (Fin m → ℝ)) := by
    apply ae_of_ae_map (p := fun B : Fin m → E => ν.map (coordinateMap B) ≪ (volume : Measure (Fin m → ℝ)))
      (measurable_rotateRows_left v).aemeasurable
    change ∀ᵐ B ∂frameLaw v, _
    rwa [← frameLaw_eq hu hv]
  have hi : orbitMoment ν m n A =
      (ENNReal.ofReal (rowJacobian A))⁻¹ ^ n * orbitMoment ν m n v := by
    unfold orbitMoment
    rw [← lintegral_const_mul _ (by fun_prop)]
    apply lintegral_congr_ae
    filter_upwards [hacv] with O hO
    apply labelMoment_factor ν (rotateRows O A) (rotateRows O v) T
      (fun x => ?_) ((ENNReal.ofReal (rowJacobian A))⁻¹) (by simp)
      (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr (rowJacobian_pos hA))) hvol hO
    rw [coordinateMap_rotateRows, coordinateMap_rotateRows, hT]
  rw [hi, orbitMoment_eq_frame, ← frameLaw_eq hu hv, ← orbitMoment_eq_frame]

lemma gaussian_lintegral_orbitMoment (ν : Measure E) [SFinite ν] (m n : ℕ) :
    ∫⁻ A, orbitMoment ν m n A ∂Measure.pi (fun _ => stdGaussian E) =
      ∫⁻ A, labelMoment ν m n A ∂Measure.pi (fun _ => stdGaussian E) := by
  unfold orbitMoment
  rw [lintegral_lintegral_swap (by
    exact ((measurable_labelMoment ν m n).comp (measurable_rotateRows.comp measurable_swap)).aemeasurable)]
  have hi (O : Rotation E) :
      ∫⁻ A, labelMoment ν m n (rotateRows O A) ∂Measure.pi (fun _ => stdGaussian E) =
        ∫⁻ A, labelMoment ν m n A ∂Measure.pi (fun _ => stdGaussian E) := by
    rw [← lintegral_map (measurable_labelMoment ν m n) (measurable_rotateRows_right O),
      gaussianRows_rotation_invariant]
  simp_rw [hi]
  simp

lemma gaussian_labelMoment_bound {ν : Measure E} [IsFiniteMeasure ν]
    {a : ℝ} (hν : NoiselessRegression.HasLocalMassBound ν a)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1)
    (m n : ℕ) (hmargin : (n : ℝ) + m ≤ a) :
    ∫⁻ A, labelMoment ν m n A ∂Measure.pi (fun _ => stdGaussian E) ≤
      ν Set.univ * (NoiselessRegression.replicaConstant ν a m)^n := by
  have he (A : Fin m → E) : labelMoment ν m n A =
      ∫⁻ y : Label m, lowerDensity ν m (A,y)^(n+1) :=
    (PiLp.volume_preserving_toLp (Fin m)).lintegral_comp
      (show Measurable (fun y : Label m => lowerDensity ν m (A,y)^(n+1)) by fun_prop)
  simp_rw [he]
  rw [← lintegral_prod _ (show AEMeasurable (fun z : (Fin m → E) × Label m => lowerDensity ν m z^(n+1)) _ by fun_prop)]
  exact lowerDensity_integrated_moment hν hsupport m n hmargin

theorem frame_gaussian_comparison (ν : Measure E) [IsFiniteMeasure ν]
    {m n : ℕ} (hm : m ≤ Module.finrank ℝ E) (hd : 0 < Module.finrank ℝ E)
    (u : Fin m → E) (hu : Orthonormal ℝ u)
    (hac : ∀ᵐ A ∂frameLaw u, ν.map (coordinateMap A) ≪ (volume : Measure (Fin m → ℝ))) :
    orbitMoment ν m n u ≤
      (2 : ℝ≥0∞)^m * ENNReal.ofReal (Real.sqrt (2 * Module.finrank ℝ E))^(m*n) *
        ∫⁻ A, labelMoment ν m n A ∂Measure.pi (fun _ => stdGaussian E) := by
  let γ : Measure (Fin m → E) := Measure.pi (fun _ => stdGaussian E)
  let t : ℝ := Real.sqrt (2 * Module.finrank ℝ E)
  let G : Set (Fin m → E) := Set.univ.pi (fun _ => Metric.closedBall (0 : E) t)
  have ht : 0 < t := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < 2 * Module.finrank ℝ E by omega))
  have hG : MeasurableSet G := MeasurableSet.univ_pi (fun _ => measurableSet_closedBall)
  have hGmass : (2 : ℝ≥0∞)⁻¹^m ≤ γ G := by
    rw [show γ G = ∏ _ : Fin m, stdGaussian E (Metric.closedBall 0 t) from Measure.pi_pi _ _]
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      Finset.prod_le_prod (s := Finset.univ) (fun (_ : Fin m) _ => gaussian_norm_ball_mass (E := E) hd)
  let B : ℝ≥0∞ := ENNReal.ofReal t ^ m
  have hB0 : B ≠ 0 := pow_ne_zero _ (ENNReal.ofReal_ne_zero_iff.mpr ht)
  have hBt : B ≠ ∞ := by simp [B]
  have hJ (A : Fin m → E) (hA : A ∈ G) : ENNReal.ofReal (rowJacobian A) ≤ B := by
    have hnorm (i : Fin m) : ‖A i‖ ≤ t := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hA i (Set.mem_univ i)
    have h := (rowJacobian_le A).trans (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hnorm i))
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
    simpa only [B, ENNReal.ofReal_pow ht.le] using ENNReal.ofReal_le_ofReal h
  have hlow : B⁻¹^n * orbitMoment ν m n u * γ G ≤
      ∫⁻ A, orbitMoment ν m n A ∂γ := by
    calc
      _ = ∫⁻ A in G, B⁻¹^n * orbitMoment ν m n u ∂γ := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ A in G, orbitMoment ν m n A ∂γ := by
        apply setLIntegral_mono_ae' hG
        filter_upwards [gaussian_rows_ae_linearIndependent m hm] with A hA
        intro hAG
        rw [orbitMoment_factor ν u hu hac A hA]
        exact mul_le_mul' (pow_le_pow_left' (ENNReal.inv_le_inv.mpr (hJ A hAG)) n) le_rfl
      _ ≤ ∫⁻ A, orbitMoment ν m n A ∂γ := lintegral_mono' Measure.restrict_le_self (fun _ => le_rfl)
  have hlow' : ((2 : ℝ≥0∞)⁻¹^m * B⁻¹^n) * orbitMoment ν m n u ≤
      ∫⁻ A, labelMoment ν m n A ∂γ := by
    rw [← gaussian_lintegral_orbitMoment ν m n]
    exact (show ((2 : ℝ≥0∞)⁻¹^m * B⁻¹^n) * orbitMoment ν m n u ≤
        B⁻¹^n * orbitMoment ν m n u * γ G from by
      simpa only [mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul' hGmass (le_rfl : B⁻¹^n * orbitMoment ν m n u ≤ B⁻¹^n * orbitMoment ν m n u)).trans hlow
  have hc0 : (2 : ℝ≥0∞)⁻¹^m * B⁻¹^n ≠ 0 := by simp [hBt]
  have hct : (2 : ℝ≥0∞)⁻¹^m * B⁻¹^n ≠ ∞ :=
    ENNReal.mul_ne_top (by finiteness) (by finiteness)
  have h := mul_le_mul' (le_rfl : ((2 : ℝ≥0∞)⁻¹^m * B⁻¹^n)⁻¹ ≤ ((2 : ℝ≥0∞)⁻¹^m * B⁻¹^n)⁻¹) hlow'
  rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul] at h
  have he : ((2 : ℝ≥0∞)⁻¹^m * B⁻¹^n)⁻¹ = (2 : ℝ≥0∞)^m * ENNReal.ofReal t^(m*n) := by
    rw [ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by finiteness)),
      ← ENNReal.inv_pow, ← ENNReal.inv_pow, inv_inv, inv_inv]
    simp only [B, ← pow_mul]
  rw [he] at h
  exact h

end ProjectionMoments
end

end OAI
