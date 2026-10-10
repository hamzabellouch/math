import OAI.Geometry.Riemannian.HarmonicCore.Sobolev

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix InnerProductSpace Matrix.Norms.Elementwise

namespace HarmonicCounterexample.Main.SmoothMetric3
lemma coefficient_memLp (A : E3 → E3 →L[ℝ] E3) (C : ℝ)
    (hA : AEStronglyMeasurable A (volume : Measure E3))
    (hbound : ∀ x, ‖A x‖ ≤ C) (u : DerivativeL2) :
    MemLp (fun x ↦ A x (u x)) 2 (volume : Measure E3) := by
  refine (Lp.memLp u).of_le_mul (c:=C)
    ((ContinuousLinearMap.id ℝ (E3 →L[ℝ] E3)).aestronglyMeasurable_comp₂ hA (Lp.aestronglyMeasurable u)) ?_
  exact Filter.Eventually.of_forall fun x ↦
    (A x).le_opNorm (u x) |>.trans (mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _))

noncomputable def coefficientLinear (A : E3 → E3 →L[ℝ] E3) (C : ℝ)
    (hA : AEStronglyMeasurable A (volume : Measure E3))
    (hbound : ∀ x, ‖A x‖ ≤ C) : DerivativeL2 →ₗ[ℝ] DerivativeL2 where
  toFun u := (coefficient_memLp A C hA hbound u).toLp (fun x ↦ A x (u x))
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(coefficient_memLp A C hA hbound (u+v)).coeFn_toLp,
      (coefficient_memLp A C hA hbound u).coeFn_toLp,
      (coefficient_memLp A C hA hbound v).coeFn_toLp,
      Lp.coeFn_add u v, Lp.coeFn_add
        ((coefficient_memLp A C hA hbound u).toLp _) ((coefficient_memLp A C hA hbound v).toLp _)] with x h1 h2 h3 h4 h5
    simp only [h1,h5,Pi.add_apply,h2,h3,h4,map_add]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [(coefficient_memLp A C hA hbound (c • u)).coeFn_toLp,
      (coefficient_memLp A C hA hbound u).coeFn_toLp,
      Lp.coeFn_smul c u, Lp.coeFn_smul c ((coefficient_memLp A C hA hbound u).toLp _)] with x h1 h2 h3 h4
    simp only [RingHom.id_apply,h1,h4,Pi.smul_apply,h2,h3,map_smul]

lemma coefficientLinear_norm (A : E3 → E3 →L[ℝ] E3) (C : ℝ)
    (hA : AEStronglyMeasurable A (volume : Measure E3))
    (hbound : ∀ x, ‖A x‖ ≤ C) (u : DerivativeL2) :
    ‖coefficientLinear A C hA hbound u‖ ≤ C * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(coefficient_memLp A C hA hbound u).coeFn_toLp] with x hx
  change ‖((coefficient_memLp A C hA hbound u).toLp _) x‖ ≤ C * ‖u x‖
  rw [hx]
  exact (A x).le_opNorm (u x) |>.trans (mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _))

noncomputable def coefficientCLM (A : E3 → E3 →L[ℝ] E3) (C : ℝ)
    (hA : AEStronglyMeasurable A (volume : Measure E3))
    (hbound : ∀ x, ‖A x‖ ≤ C) : DerivativeL2 →L[ℝ] DerivativeL2 :=
  (coefficientLinear A C hA hbound).mkContinuous C (coefficientLinear_norm A C hA hbound)

lemma coefficientCLM_coercive (A : E3 → E3 →L[ℝ] E3) (C c : ℝ)
    (hA : AEStronglyMeasurable A (volume : Measure E3))
    (hbound : ∀ x, ‖A x‖ ≤ C) (hpos : ∀ x v, c * ‖v‖^2 ≤ ⟪A x v, v⟫_ℝ)
    (u : DerivativeL2) : c * ‖u‖^2 ≤ ⟪coefficientCLM A C hA hbound u, u⟫_ℝ := by
  have hint := L2.integrable_inner u u (𝕜:=ℝ)
  have hint' := L2.integrable_inner (coefficientCLM A C hA hbound u) u (𝕜:=ℝ)
  have hle : (∫ x, c * ⟪u x, u x⟫_ℝ) ≤
      ∫ x, ⟪(coefficientCLM A C hA hbound u) x, u x⟫_ℝ := by
    apply integral_mono_ae (hint.const_mul c) hint'
    filter_upwards [(coefficient_memLp A C hA hbound u).coeFn_toLp] with x hx
    change c * ⟪u x, u x⟫_ℝ ≤ ⟪((coefficient_memLp A C hA hbound u).toLp _) x, u x⟫_ℝ
    rw [hx,real_inner_self_eq_norm_sq]
    exact hpos x (u x)
  rw [integral_const_mul,← L2.inner_def,real_inner_self_eq_norm_sq,← L2.inner_def] at hle
  exact hle

noncomputable def sobolevEnergy (R : ℝ) (A : E3 → E3 →L[ℝ] E3) (C : ℝ)
    (hA : AEStronglyMeasurable A (volume : Measure E3))
    (hbound : ∀ x, ‖A x‖ ≤ C) : ZeroSobolev R →L[ℝ] ZeroSobolev R →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp ((coefficientCLM A C hA hbound).comp (sobolevDerivative R))
    (sobolevDerivative R)

lemma sobolevEnergy_coercive (R : ℝ) (A : E3 → E3 →L[ℝ] E3) (C c : ℝ) (hc : 0 < c)
    (hA : AEStronglyMeasurable A (volume : Measure E3))
    (hbound : ∀ x, ‖A x‖ ≤ C) (hpos : ∀ x v, c * ‖v‖^2 ≤ ⟪A x v, v⟫_ℝ) :
    IsCoercive (sobolevEnergy R A C hA hbound) := by
  have hK : 0 < poincareConstant R ^ 2 + 1 := by positivity
  refine ⟨c/(poincareConstant R^2+1),div_pos hc hK,fun u ↦ ?_⟩
  have h1 := coefficientCLM_coercive A C c hA hbound hpos (sobolevDerivative R u)
  have h2 := mul_le_mul_of_nonneg_left (sobolev_norm_sq_le R u) (div_pos hc hK).le
  change _ ≤ ⟪coefficientCLM A C hA hbound (sobolevDerivative R u), sobolevDerivative R u⟫_ℝ
  calc
    c/(poincareConstant R^2+1)*‖u‖*‖u‖ =
        (c/(poincareConstant R^2+1))*‖u‖^2 := by ring
    _ ≤ (c/(poincareConstant R^2+1))*((poincareConstant R^2+1)*‖sobolevDerivative R u‖^2) := h2
    _ = c * ‖sobolevDerivative R u‖^2 := by field_simp
    _ ≤ _ := h1

theorem variational_dirichlet_unique (R : ℝ) (A : E3 → E3 →L[ℝ] E3) (C c : ℝ) (hc : 0 < c)
    (hA : AEStronglyMeasurable A (volume : Measure E3))
    (hbound : ∀ x, ‖A x‖ ≤ C) (hpos : ∀ x v, c * ‖v‖^2 ≤ ⟪A x v, v⟫_ℝ)
    (ℓ : ZeroSobolev R →L[ℝ] ℝ) :
    ∃! u : ZeroSobolev R, ∀ v, sobolevEnergy R A C hA hbound u v = ℓ v := by
  let hb := sobolevEnergy_coercive R A C c hc hA hbound hpos
  let f := (InnerProductSpace.toDual ℝ (ZeroSobolev R)).symm ℓ
  let u := hb.continuousLinearEquivOfBilin.symm f
  have hu : ∀ v, sobolevEnergy R A C hA hbound u v = ℓ v := by
    intro v
    rw [← hb.continuousLinearEquivOfBilin_apply]
    change ⟪hb.continuousLinearEquivOfBilin (hb.continuousLinearEquivOfBilin.symm f), v⟫_ℝ = ℓ v
    rw [hb.continuousLinearEquivOfBilin.apply_symm_apply,InnerProductSpace.toDual_symm_apply]
  refine ⟨u,hu,fun y hy ↦ ?_⟩
  apply hb.continuousLinearEquivOfBilin.injective
  have hy' : f = hb.continuousLinearEquivOfBilin y :=
    hb.unique_continuousLinearEquivOfBilin (fun v ↦ by
      rw [InnerProductSpace.toDual_symm_apply]
      exact (hy v).symm)
  simpa only [u,ContinuousLinearEquiv.apply_symm_apply] using hy'.symm

lemma coeff_contDiff (g : SmoothMetric3) : ContDiff ℝ ∞ g.coeff :=
  contDiff_pi.mpr (fun i ↦ contDiff_pi.mpr (g.smooth i))

lemma determinant_contDiff {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    {A : T → M3} (hA : ∀ i j, ContDiff ℝ ∞ (fun x ↦ A x i j)) :
    ContDiff ℝ ∞ (fun x ↦ (A x).det) := by
  simp only [Matrix.det_apply]
  apply ContDiff.sum
  intro p _
  simpa only [Units.smul_def, zsmul_eq_mul] using
    (contDiff_const.mul (contDiff_prod (fun i _ ↦ hA (p i) i)) :
      ContDiff ℝ ∞ (fun x ↦ (↑(Equiv.Perm.sign p) : ℝ) * ∏ i, A x (p i) i))

lemma inverse_contDiff (g : SmoothMetric3) (i j : Fin 3) :
    ContDiff ℝ ∞ (fun x ↦ (g.coeff x)⁻¹ i j) := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  apply ContDiff.mul
  · exact (determinant_contDiff g.smooth).inv (fun x ↦ (g.positive x).det_pos.ne')
  · simp only [Matrix.adjugate_apply]
    apply determinant_contDiff
    intro k l
    by_cases hk : k = j
    · subst k
      simp only [Matrix.updateRow_apply]
      exact contDiff_const
    · simpa only [Matrix.updateRow_apply, ite_eq_right hk] using g.smooth k l

def energyMatrix (g : SmoothMetric3) (x : E3) : M3 :=
  Real.sqrt (g.coeff x).det • (g.coeff x)⁻¹

noncomputable def matrixOperator : M3 →L[ℝ] (E3 →L[ℝ] E3) :=
  (LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toEuclideanLin.toLinearMap).toContinuousLinearMap

def energyOperator (g : SmoothMetric3) (x : E3) : E3 →L[ℝ] E3 :=
  matrixOperator (energyMatrix g x)

lemma energyMatrix_continuous (g : SmoothMetric3) : Continuous (energyMatrix g) :=
  ((determinant_contDiff g.smooth).continuous.sqrt).smul
    (continuous_pi fun i ↦ continuous_pi fun j ↦ (g.inverse_contDiff i j).continuous)

lemma energyOperator_continuous (g : SmoothMetric3) : Continuous (energyOperator g) :=
  matrixOperator.continuous.comp g.energyMatrix_continuous

lemma energyMatrix_positive (g : SmoothMetric3) (x : E3) : (energyMatrix g x).PosDef :=
  (g.positive x).inv.smul (Real.sqrt_pos.2 (g.positive x).det_pos)

lemma energyOperator_pos (g : SmoothMetric3) (x v : E3) (hv : v ≠ 0) :
    0 < ⟪g.energyOperator x v, v⟫_ℝ := by
  have hn : v.ofLp ≠ 0 := by
    intro h
    apply hv
    exact congrArg (WithLp.toLp 2) h
  have hp := (g.energyMatrix_positive x).dotProduct_mulVec_pos hn
  change 0 < ⟪WithLp.toLp 2 (g.energyMatrix x *ᵥ v.ofLp), v⟫_ℝ
  simpa only [PiLp.inner_apply,RCLike.inner_apply,WithLp.ofLp_toLp,
    starRingEnd_apply,star_trivial,Matrix.mulVec,dotProduct] using hp

lemma energyOperator_uniform (g : SmoothMetric3) (R : ℝ) (hR : 0 ≤ R) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      (∀ x ∈ Metric.closedBall (0:E3) R, ‖g.energyOperator x‖ ≤ C) ∧
      (∀ x ∈ Metric.closedBall (0:E3) R, ∀ v, c * ‖v‖^2 ≤ ⟪g.energyOperator x v, v⟫_ℝ) := by
  let S : Set (E3 × E3) := Metric.closedBall 0 R ×ˢ Metric.sphere 0 1
  have hS : IsCompact S := (isCompact_closedBall (0:E3) R).prod (isCompact_sphere (0:E3) 1)
  have hne : S.Nonempty := by
    refine ⟨(0,coordinateVector 0),?_,?_⟩
    · simpa using hR
    · simp [coordinateVector]
  have hcont : Continuous (fun z : E3 × E3 ↦ ⟪g.energyOperator z.1 z.2, z.2⟫_ℝ) :=
    ((g.energyOperator_continuous.comp continuous_fst).clm_apply continuous_snd).inner continuous_snd
  obtain ⟨z,hz,hm⟩ := hS.exists_isMinOn hne hcont.continuousOn
  have hz1 : ‖z.2‖ = 1 := by simpa [S,Metric.mem_sphere] using hz.2
  have hp : 0 < ⟪g.energyOperator z.1 z.2, z.2⟫_ℝ :=
    g.energyOperator_pos _ _ (by intro h; simp [h] at hz1)
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:E3) R).exists_bound_of_continuousOn
    g.energyOperator_continuous.continuousOn
  refine ⟨⟪g.energyOperator z.1 z.2, z.2⟫_ℝ,max C 0,hp,le_max_right _ _,
    fun x hx ↦ (hC x hx).trans (le_max_left _ _),?_⟩
  intro x hx v
  by_cases hv : v = 0
  · simp [hv]
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hvn : ‖‖v‖⁻¹ • v‖ = 1 := by simp [norm_smul,hvp.ne']
  have hm' := hm (show (x,‖v‖⁻¹ • v) ∈ S from ⟨hx,by simpa [Metric.mem_sphere] using hvn⟩)
  change ⟪g.energyOperator z.1 z.2, z.2⟫_ℝ ≤ ⟪g.energyOperator x (‖v‖⁻¹ • v), ‖v‖⁻¹ • v⟫_ℝ at hm'
  have hs : ⟪g.energyOperator x (‖v‖⁻¹ • v), ‖v‖⁻¹ • v⟫_ℝ =
      (‖v‖⁻¹)^2 * ⟪g.energyOperator x v, v⟫_ℝ := by
    rw [map_smul,real_inner_smul_left,real_inner_smul_right]
    ring
  rw [hs] at hm'
  have hh := mul_le_mul_of_nonneg_right hm' (sq_nonneg ‖v‖)
  calc
    ⟪g.energyOperator z.1 z.2, z.2⟫_ℝ * ‖v‖^2 ≤
      ((‖v‖⁻¹)^2 * ⟪g.energyOperator x v, v⟫_ℝ)*‖v‖^2 := hh
    _ = _ := by field_simp [hvp.ne']

def clippedEnergyOperator (g : SmoothMetric3) (R : ℝ) : E3 → E3 →L[ℝ] E3 :=
  by classical exact (Metric.closedBall (0:E3) R).piecewise g.energyOperator (fun _ ↦ ContinuousLinearMap.id ℝ E3)

lemma clippedEnergyOperator_measurable (g : SmoothMetric3) (R : ℝ) :
    AEStronglyMeasurable (g.clippedEnergyOperator R) (volume : Measure E3) := by
  classical
  exact (g.energyOperator_continuous.measurable.piecewise Metric.isClosed_closedBall.measurableSet
    measurable_const).aestronglyMeasurable

lemma clippedEnergyOperator_uniform (g : SmoothMetric3) (R : ℝ) (hR : 0 ≤ R) :
    ∃ c C : ℝ, 0 < c ∧ (∀ x, ‖g.clippedEnergyOperator R x‖ ≤ C) ∧
      (∀ x v, c * ‖v‖^2 ≤ ⟪g.clippedEnergyOperator R x v, v⟫_ℝ) := by
  classical
  obtain ⟨c,C,hc,hC,hbound,hpos⟩ := g.energyOperator_uniform R hR
  refine ⟨min c 1,max C 1,lt_min hc (by norm_num),?_,?_⟩
  · intro x
    by_cases hx : x ∈ Metric.closedBall (0:E3) R
    · simpa only [clippedEnergyOperator,Set.piecewise_eq_of_mem _ _ _ hx] using
        (hbound x hx).trans (le_max_left C 1)
    · simp [clippedEnergyOperator,Set.piecewise_eq_of_notMem _ _ _ hx]
  · intro x v
    by_cases hx : x ∈ Metric.closedBall (0:E3) R
    · simp only [clippedEnergyOperator,Set.piecewise_eq_of_mem _ _ _ hx]
      exact (mul_le_mul_of_nonneg_right (min_le_left c 1) (sq_nonneg ‖v‖)).trans (hpos x hx v)
    · simp only [clippedEnergyOperator,Set.piecewise_eq_of_notMem _ _ _ hx,
        ContinuousLinearMap.id_apply,real_inner_self_eq_norm_sq]
      exact mul_le_of_le_one_left (sq_nonneg _) (min_le_right _ _)

lemma sobolevEnergy_eq_integral (R : ℝ) (A : E3 → E3 →L[ℝ] E3) (C : ℝ)
    (hA : AEStronglyMeasurable A (volume : Measure E3)) (hbound : ∀ x, ‖A x‖ ≤ C)
    (u v : ZeroSobolev R) : sobolevEnergy R A C hA hbound u v =
      ∫ x, ⟪A x ((sobolevDerivative R u) x), (sobolevDerivative R v) x⟫_ℝ := by
  change ⟪coefficientCLM A C hA hbound (sobolevDerivative R u), sobolevDerivative R v⟫_ℝ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(coefficient_memLp A C hA hbound (sobolevDerivative R u)).coeFn_toLp] with x hx
  change ⟪((coefficient_memLp A C hA hbound (sobolevDerivative R u)).toLp _) x, (sobolevDerivative R v) x⟫_ℝ = _
  rw [hx]

theorem metric_variational_dirichlet_unique (g : SmoothMetric3) (R : ℝ) (hR : 0 ≤ R)
    (ℓ : ZeroSobolev R →L[ℝ] ℝ) :
    ∃! u : ZeroSobolev R, ∀ v : ZeroSobolev R,
      (∫ x, ⟪g.clippedEnergyOperator R x ((sobolevDerivative R u) x),
        (sobolevDerivative R v) x⟫_ℝ) = ℓ v := by
  obtain ⟨c,C,hc,hbound,hpos⟩ := g.clippedEnergyOperator_uniform R hR
  have hh := variational_dirichlet_unique R (g.clippedEnergyOperator R) C c hc
    (g.clippedEnergyOperator_measurable R) hbound hpos ℓ
  simpa only [sobolevEnergy_eq_integral] using hh

theorem metric_affine_dirichlet_unique (g : SmoothMetric3) (R : ℝ) (hR : 0 ≤ R)
    (D : DerivativeL2) :
    ∃! u : ZeroSobolev R, ∀ v : ZeroSobolev R,
      (∫ x, ⟪g.clippedEnergyOperator R x (D x + (sobolevDerivative R u) x),
        (sobolevDerivative R v) x⟫_ℝ) = 0 := by
  obtain ⟨c,C,hc,hbound,hpos⟩ := g.clippedEnergyOperator_uniform R hR
  let A := coefficientCLM (g.clippedEnergyOperator R) C
    (g.clippedEnergyOperator_measurable R) hbound
  let ℓ : ZeroSobolev R →L[ℝ] ℝ := -((innerSL ℝ (A D)).comp (sobolevDerivative R))
  have he (u v : ZeroSobolev R) :
      (∫ x, ⟪g.clippedEnergyOperator R x (D x + (sobolevDerivative R u) x),
        (sobolevDerivative R v) x⟫_ℝ) =
      ⟪A D,sobolevDerivative R v⟫_ℝ +
        sobolevEnergy R (g.clippedEnergyOperator R) C
          (g.clippedEnergyOperator_measurable R) hbound u v := by
    change _ = ⟪A D,sobolevDerivative R v⟫_ℝ + ⟪A (sobolevDerivative R u),sobolevDerivative R v⟫_ℝ
    rw [← inner_add_left,← map_add,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(coefficient_memLp (g.clippedEnergyOperator R) C
        (g.clippedEnergyOperator_measurable R) hbound (D + sobolevDerivative R u)).coeFn_toLp,
      Lp.coeFn_add D (sobolevDerivative R u)] with x hx hxx
    change _ = ⟪((coefficient_memLp (g.clippedEnergyOperator R) C
        (g.clippedEnergyOperator_measurable R) hbound (D + sobolevDerivative R u)).toLp _) x,
          (sobolevDerivative R v) x⟫_ℝ
    rw [hx,hxx]
    rfl
  obtain ⟨u,hu,hu_unique⟩ := variational_dirichlet_unique R (g.clippedEnergyOperator R)
    C c hc (g.clippedEnergyOperator_measurable R) hbound hpos ℓ
  refine ⟨u,?_,?_⟩
  · intro v
    rw [he,hu]
    change _ + -_ = 0
    exact add_neg_cancel _
  · intro y hy
    apply hu_unique y
    intro v
    have hv := hy v
    rw [he] at hv
    change sobolevEnergy R (g.clippedEnergyOperator R) C
      (g.clippedEnergyOperator_measurable R) hbound y v = -⟪A D,sobolevDerivative R v⟫_ℝ
    linarith

end HarmonicCounterexample.Main.SmoothMetric3

end

end OAI
