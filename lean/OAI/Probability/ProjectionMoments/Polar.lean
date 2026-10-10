import OAI.Probability.ProjectionMoments.RieszPotential

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Matrix
open scoped ENNReal NNReal RealInnerProductSpace Topology MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

instance realMatrixMeasurableSpace (k : ℕ) : MeasurableSpace (Matrix (Fin k) (Fin k) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin k → Fin k → ℝ))
instance realMatrixBorelSpace (k : ℕ) : BorelSpace (Matrix (Fin k) (Fin k) ℝ) :=
  inferInstanceAs (BorelSpace (Fin k → Fin k → ℝ))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma mixRows_mul [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} (M N : Matrix (Fin k) (Fin k) ℝ) (X : Fin k → E) :
    mixRows (M*N) X = mixRows M (mixRows N X) := by
  ext i
  simp only [mixRows, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma mixRows_one [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} (X : Fin k → E) : mixRows 1 X = X := by
  ext i
  simp [mixRows, Matrix.one_apply]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma gram_mixRows [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (X : Fin k → E) :
    Matrix.gram ℝ (mixRows M X) = M * Matrix.gram ℝ X * M.transpose := by
  ext i j
  simp only [Matrix.gram_apply, mixRows, inner_sum, sum_inner, real_inner_smul_left,
    real_inner_smul_right, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma continuous_polarRadial [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} : Continuous (polarRadial (E := E) (k := k)) := by
  apply CFC.continuousOn_sqrt.comp_continuous
  · exact continuous_matrix (fun i j => by simp only [Matrix.gram_apply]; fun_prop)
  · intro X
    exact (Matrix.posSemidef_gram ℝ X).nonneg

lemma measurable_matrix_inverse {k : ℕ} :
    Measurable (fun M : Matrix (Fin k) (Fin k) ℝ => M⁻¹) := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv]
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_apply]
  fun_prop

lemma measurable_rawPolarRows {k : ℕ} : Measurable (rawPolarRows (E := E) (k := k)) := by
  have hH := measurable_matrix_inverse.comp (continuous_polarRadial (E := E) (k := k)).measurable
  apply Measurable.of_eval
  intro i
  change Measurable (fun X : Fin k → E => ∑ j, (polarRadial X)⁻¹ i j • X j)
  apply Finset.measurable_sum
  intro j hj
  have hh : Measurable (fun X : Fin k → E => (polarRadial X)⁻¹ i j) :=
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hH)
  exact hh.smul (measurable_pi_apply j)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma polarRadial_squared [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} (X : Fin k → E) :
    polarRadial X * polarRadial X = Matrix.gram ℝ X :=
  CFC.sqrt_mul_sqrt_self _ (Matrix.posSemidef_gram ℝ X).nonneg

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma polarRadial_pos [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} (X : Fin k → E) : 0 ≤ polarRadial X := CFC.sqrt_nonneg _

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma polarRadial_isUnit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {k : ℕ} {X : Fin k → E} (hX : LinearIndependent ℝ X) :
    IsUnit (polarRadial X) :=
  (CFC.isUnit_sqrt_iff _ (Matrix.posSemidef_gram ℝ X).nonneg).mpr
    (Matrix.posDef_gram_iff_linearIndependent.mpr hX).isUnit

lemma rawPolarRows_orthonormal {k : ℕ} {X : Fin k → E} (hX : LinearIndependent ℝ X) :
    Orthonormal ℝ (rawPolarRows X) := by
  have hH := polarRadial_isUnit hX
  have hdet : IsUnit (polarRadial X).det := (Matrix.isUnit_iff_isUnit_det _).mp hH
  have hsym : (polarRadial X)⁻¹.transpose = (polarRadial X)⁻¹ := by
    have hh : (polarRadial X).IsHermitian := (polarRadial_pos X).isSelfAdjoint
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hh.inv
  have hgram : Matrix.gram ℝ (rawPolarRows X) = 1 := by
    rw [rawPolarRows, gram_mixRows, hsym, ← polarRadial_squared,
      ← mul_assoc, Matrix.nonsing_inv_mul _ hdet, one_mul, Matrix.mul_nonsing_inv _ hdet]
  apply orthonormal_iff_ite.mpr
  intro i j
  simpa only [Matrix.gram_apply, Matrix.one_apply] using congrFun (congrFun hgram i) j

lemma polar_reconstruction {k : ℕ} {X : Fin k → E} (hX : LinearIndependent ℝ X) :
    mixRows (polarRadial X) (rawPolarRows X) = X := by
  rw [rawPolarRows, ← mixRows_mul, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp (polarRadial_isUnit hX)), mixRows_one]

omit [MeasurableSpace E] [BorelSpace E] in
lemma gram_rotateRows [MeasurableSpace E] [BorelSpace E] {k : ℕ} (X : Fin k → E) (O : Rotation E) :
    Matrix.gram ℝ (rotateRows O X) = Matrix.gram ℝ X := by
  ext i j
  exact (Unitary.linearIsometryEquiv O).inner_map_map (X i) (X j)

lemma polarRadial_rotateRows {k : ℕ} (X : Fin k → E) (O : Rotation E) :
    polarRadial (rotateRows O X) = polarRadial X := by
  simp only [polarRadial, gram_rotateRows]

lemma rawPolarRows_rotateRows {k : ℕ} (X : Fin k → E) (O : Rotation E) :
    rawPolarRows (rotateRows O X) = rotateRows O (rawPolarRows X) := by
  ext i
  simp only [rawPolarRows, polarRadial_rotateRows, mixRows, rotateRows, map_sum, map_smul]

lemma measurableSet_linearIndependent {k : ℕ} :
    MeasurableSet {X : Fin k → E | LinearIndependent ℝ X} := by
  simp only [← Matrix.det_gram_ne_zero_iff_linearIndependent]
  have hg : Continuous (fun X : Fin k → E => Matrix.gram ℝ X) :=
    continuous_matrix (fun i j => by simp only [Matrix.gram_apply]; fun_prop)
  exact (isClosed_eq hg.matrix_det continuous_const).measurableSet.compl

lemma measurable_polarRows {k : ℕ} (u : Fin k → E) : Measurable (polarRows u) := by
  classical
  exact Measurable.ite measurableSet_linearIndependent measurable_rawPolarRows measurable_const

lemma polarRows_orthonormal {k : ℕ} {u : Fin k → E} (hu : Orthonormal ℝ u)
    (X : Fin k → E) : Orthonormal ℝ (polarRows u X) := by
  by_cases hX : LinearIndependent ℝ X
  · simpa only [polarRows, ite_eq_left hX] using rawPolarRows_orthonormal hX
  · simpa only [polarRows, ite_eq_right hX] using hu

lemma polarRows_rotateRows {k : ℕ} (u : Fin k → E) {X : Fin k → E}
    (hX : LinearIndependent ℝ X) (O : Rotation E) :
    polarRows u (rotateRows O X) = rotateRows O (polarRows u X) := by
  have hXO : LinearIndependent ℝ (rotateRows O X) := by
    rw [← Matrix.det_gram_ne_zero_iff_linearIndependent, gram_rotateRows,
      Matrix.det_gram_ne_zero_iff_linearIndependent]
    exact hX
  simp only [polarRows, ite_eq_left hX, ite_eq_left hXO, rawPolarRows_rotateRows]

lemma lintegral_polarRows_eq_frame {k : ℕ} (hk : k ≤ Module.finrank ℝ E)
    {u : Fin k → E} (hu : Orthonormal ℝ u) (f : (Fin k → E) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ X, f (polarRows u X) ∂Measure.pi (fun _ => stdGaussian E)) = ∫⁻ A, f A ∂frameLaw u := by
  let γ := Measure.pi (fun _ : Fin k => stdGaussian E)
  have hrot (O : Rotation E) : (∫⁻ X, f (polarRows u X) ∂γ) =
      ∫⁻ X, f (rotateRows O (polarRows u X)) ∂γ := by
    calc
      _ = ∫⁻ X, f (polarRows u (rotateRows O X)) ∂γ := by
        have hm : Measurable (rotateRows O : (Fin k → E) → (Fin k → E)) :=
          measurable_rotateRows.comp (measurable_const.prodMk measurable_id)
        have hh := lintegral_map (μ := γ) (hf.comp (measurable_polarRows u)) hm
        rw [show γ.map (rotateRows O) = γ from gaussianRows_rotation_invariant k O] at hh
        exact hh
      _ = _ := lintegral_congr_ae (by
        filter_upwards [gaussian_rows_ae_linearIndependent k hk] with X hX
        rw [polarRows_rotateRows u hX])
  calc
    _ = ∫⁻ O, ∫⁻ X, f (rotateRows O (polarRows u X)) ∂γ ∂rotationLaw E := by
      simp_rw [← hrot]
      simp only [lintegral_const, measure_univ, mul_one]
      rfl
    _ = ∫⁻ X, ∫⁻ O, f (rotateRows O (polarRows u X)) ∂rotationLaw E ∂γ := by
      apply lintegral_lintegral_swap
      exact (hf.comp (measurable_rotateRows.comp
        (measurable_fst.prodMk ((measurable_polarRows u).comp measurable_snd)))).aemeasurable
    _ = ∫⁻ X, ∫⁻ A, f A ∂frameLaw u ∂γ := by
      apply lintegral_congr
      intro X
      rw [frameLaw_eq hu (polarRows_orthonormal hu X), frameLaw]
      have hm : Measurable (fun O : Rotation E => rotateRows O (polarRows u X)) :=
        measurable_rotateRows.comp (measurable_id.prodMk measurable_const)
      exact (lintegral_map hf hm).symm
    _ = _ := by simp [γ]

lemma polarRows_law {k : ℕ} (hk : k ≤ Module.finrank ℝ E)
    {u : Fin k → E} (hu : Orthonormal ℝ u) :
    (Measure.pi (fun _ : Fin k => stdGaussian E)).map (polarRows u) = frameLaw u := by
  apply Measure.ext
  intro s hs
  have hf : Measurable (s.indicator (1 : (Fin k → E) → ℝ≥0∞)) := measurable_const.indicator hs
  rw [← lintegral_indicator_one hs, lintegral_map hf (measurable_polarRows u),
    lintegral_polarRows_eq_frame hk hu _ hf, lintegral_indicator_one hs]

end

lemma euclidean_gaussian_integral (k : ℕ) :
    (∫⁻ x : Fin k → ℝ, ENNReal.ofReal (Real.exp (-‖WithLp.toLp 2 x‖^2)) ∂volume) =
      ENNReal.ofReal (Real.sqrt Real.pi ^ k) := by
  have hex (x : Fin k → ℝ) : Real.exp (-‖WithLp.toLp 2 x‖^2) =
      ∏ i, Real.exp (-(x i)^2) := by
    rw [EuclideanSpace.norm_sq_eq, ← Finset.sum_neg_distrib, Real.exp_sum]
    congr 1
    funext i
    simp only [Real.norm_eq_abs, sq_abs]
  have hscalar : (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-x^2)) ∂volume) =
      ENNReal.ofReal (Real.sqrt Real.pi) := by
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · simpa using congrArg ENNReal.ofReal (integral_gaussian 1)
    · simpa using integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1)
    · exact Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)
  simp_rw [hex, ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le)]
  rw [volume_pi, NoiselessRegression.lintegral_fin_prod (volume : Measure ℝ) k
    (fun _ x => ENNReal.ofReal (Real.exp (-x^2))) (fun _ => by fun_prop)]
  simp only [hscalar, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.ofReal_pow (Real.sqrt_nonneg _)]

lemma unit_ball_volume_bound (k : ℕ) (hk : 1 ≤ k) :
    (volume : Measure (EuclideanSpace ℝ (Fin k))) (Metric.ball 0 1) ≤
      ENNReal.ofReal ((6 / Real.sqrt k)^k) := by
  let r := Real.sqrt (k : ℝ)
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hr : 0 < r := Real.sqrt_pos.mpr hk0
  have hr2 : r^2 = k := Real.sq_sqrt hk0.le
  have hlower : ENNReal.ofReal (Real.exp (-(k:ℝ))) *
      (volume : Measure (EuclideanSpace ℝ (Fin k))) (Metric.ball 0 r) ≤
      ENNReal.ofReal (Real.sqrt Real.pi ^ k) := by
    calc
      _ = ∫⁻ _x in Metric.ball (0 : EuclideanSpace ℝ (Fin k)) r,
          ENNReal.ofReal (Real.exp (-(k:ℝ))) ∂volume := by simp
      _ ≤ ∫⁻ x in Metric.ball (0 : EuclideanSpace ℝ (Fin k)) r,
          ENNReal.ofReal (Real.exp (-‖x‖^2)) ∂volume := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        have hx' : ‖x‖ ≤ r := by simpa [Metric.mem_ball, dist_zero_right] using (Metric.mem_ball.mp hx).le
        nlinarith [norm_nonneg x]
      _ ≤ ∫⁻ x : EuclideanSpace ℝ (Fin k), ENNReal.ofReal (Real.exp (-‖x‖^2)) ∂volume :=
        setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (Real.sqrt Real.pi ^ k) := by
        rw [← (PiLp.volume_preserving_toLp (Fin k)).map_eq,
          lintegral_map (by fun_prop) (by fun_prop)]
        exact euclidean_gaussian_integral k
  rw [Measure.addHaar_ball_of_pos volume 0 hr, finrank_euclideanSpace_fin] at hlower
  have h := ENNReal.toReal_le_of_le_ofReal (by positivity) hlower
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    ENNReal.toReal_ofReal (pow_nonneg hr.le _)] at h
  have hexp : Real.exp (-(k:ℝ)) * Real.exp (k:ℝ) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos : 0 ≤ ((volume : Measure (EuclideanSpace ℝ (Fin k))) (Metric.ball 0 1)).toReal :=
    ENNReal.toReal_nonneg
  have hnum : Real.exp (k:ℝ) * Real.sqrt Real.pi ^ k ≤ (6:ℝ)^k := by
    rw [show (k:ℝ) = (k:ℝ)*1 by ring, Real.exp_nat_mul, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have hs : Real.sqrt Real.pi < 2 := (Real.sqrt_lt' (by norm_num)).mpr (by nlinarith [Real.pi_lt_four])
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1, Real.sqrt_nonneg Real.pi]
  have hv : ((volume : Measure (EuclideanSpace ℝ (Fin k))) (Metric.ball 0 1)).toReal ≤
      (6/r)^k := by
    rw [div_pow, le_div_iff₀ (pow_pos hr _)]
    calc
      _ = Real.exp (k:ℝ)*(Real.exp (-(k:ℝ))*r^k*
          ((volume : Measure (EuclideanSpace ℝ (Fin k))) (Metric.ball 0 1)).toReal) := by
          nlinarith [congrArg (fun t : ℝ => t * (r^k *
            ((volume : Measure (EuclideanSpace ℝ (Fin k))) (Metric.ball 0 1)).toReal)) hexp]
      _ ≤ Real.exp (k:ℝ)*Real.sqrt Real.pi^k := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (Real.exp_pos (k:ℝ)).le
      _ ≤ _ := hnum
  exact (ENNReal.le_ofReal_iff_toReal_le measure_ball_lt_top.ne (by positivity)).mpr hv

end ProjectionMoments

end

end OAI
