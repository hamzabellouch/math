import Mathlib

namespace OAI

/-! Schwartz lattice periodization and coordinate Poisson summation. -/

section

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap
open Set Filter MeasureTheory Topology

namespace CubicPoisson

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma schwartz_summable_lattice (L : Submodule ℤ E) [DiscreteTopology L]
    (f : 𝓢(E, ℂ)) : Summable (fun z : L => f z) := by
  let k := Module.finrank ℤ L + 1
  obtain ⟨C, hC, hbound⟩ := f.decay k 0
  have hsum := (ZLattice.summable_norm_pow_inv L k (by dsimp [k]; omega)).mul_left C
  apply Summable.of_norm_bounded_eventually hsum
  filter_upwards [Filter.eventually_cofinite_ne (0 : L)] with z hz
  have hz' : 0 < ‖(z : E)‖ := norm_pos_iff.mpr (by simpa using hz)
  have hb : ‖(z : E)‖ ^ k * ‖f z‖ ≤ C := by simpa using hbound z
  rw [inv_pow]
  change ‖f z‖ ≤ C * (‖(z : E)‖ ^ k)⁻¹
  exact (le_mul_inv_iff₀ (pow_pos hz' k)).mpr (by simpa [mul_comm] using hb)

lemma schwartz_locally_summable_lattice (L : Submodule ℤ E) [DiscreteTopology L]
    (f : 𝓢(E, ℂ)) (K : TopologicalSpace.Compacts E) :
    Summable (fun z : L =>
      ‖((⟨f, f.continuous⟩ : C(E, ℂ)).comp
        (ContinuousMap.addRight (z : E))).restrict K‖) := by
  let k := Module.finrank ℤ L + 1
  obtain ⟨C, hC, hbound⟩ := f.decay k 0
  obtain ⟨R₀, hR₀⟩ := K.isCompact.isBounded.subset_closedBall (0 : E)
  let R := max R₀ 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hKR : ∀ x ∈ K, ‖x‖ ≤ R := by
    intro x hx
    have h : ‖x‖ ≤ R₀ := by simpa using hR₀ hx
    exact h.trans (le_max_left R₀ 1)
  have hclosed : IsClosed (L : Set E) :=
    @AddSubgroup.isClosed_of_discreteTopology _ _ _ _ _ L.toAddSubgroup
      (inferInstanceAs (DiscreteTopology L))
  have hfin : {z : L | ‖(z : E)‖ ≤ 2 * R}.Finite := by
    have h := (Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      (Metric.isBounded_closedBall (x := (0 : E)) (r := 2 * R)) hclosed).preimage_embedding
        (Function.Embedding.subtype (fun x : E => x ∈ L))
    convert h using 1
    ext z
    simp [Metric.mem_closedBall]
  have hsum := (ZLattice.summable_norm_pow_inv L k (by dsimp [k]; omega)).mul_left (2 ^ k * C)
  apply Summable.of_norm_bounded_eventually hsum
  filter_upwards [hfin.eventually_cofinite_notMem] with z hz
  have hz : 2 * R < ‖(z : E)‖ := by simpa only [Set.mem_ofPred_eq, not_le] using hz
  rw [norm_norm]
  refine (ContinuousMap.norm_le _ (by positivity)).mpr ?_
  intro x
  have hxR := hKR x.1 x.2
  have hzpos : 0 < ‖(z : E)‖ := by linarith
  have hxlow : ‖(z : E)‖ / 2 ≤ ‖x.1 + (z : E)‖ := by
    have hn := norm_sub_norm_le (z : E) (-x.1)
    simp only [norm_neg, sub_neg_eq_add] at hn
    rw [add_comm (z : E) x.1] at hn
    linarith
  have hxpos : 0 < ‖x.1 + (z : E)‖ := lt_of_lt_of_le (by positivity) hxlow
  have hb : ‖x.1 + (z : E)‖ ^ k * ‖f (x.1 + (z : E))‖ ≤ C :=
    by simpa using hbound (x.1 + (z : E))
  change ‖f (x.1 + (z : E))‖ ≤ 2 ^ k * C * ‖(z : E)‖⁻¹ ^ k
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ ‖(z : E)‖ / 2) hxlow k
  have hb' : (‖(z : E)‖ / 2) ^ k * ‖f (x.1 + (z : E))‖ ≤ C :=
    (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans hb
  rw [div_pow] at hb'
  rw [inv_pow]
  apply (le_mul_inv_iff₀ (pow_pos hzpos k)).mpr
  calc
    _ = (‖(z : E)‖ ^ k / 2 ^ k * ‖f (x.1 + (z : E))‖) * 2 ^ k := by
      field_simp
    _ ≤ C * 2 ^ k := mul_le_mul_of_nonneg_right hb' (by positivity)
    _ = _ := by ring

def periodization (L : Submodule ℤ E) (f : 𝓢(E, ℂ)) : C(E, ℂ) :=
  ∑' z : L, (⟨f, f.continuous⟩ : C(E, ℂ)).comp (ContinuousMap.addRight (z : E))

lemma periodization_apply (L : Submodule ℤ E) [DiscreteTopology L]
    (f : 𝓢(E, ℂ)) (x : E) :
    periodization L f x = ∑' z : L, f (x + (z : E)) := by
  have hs := ContinuousMap.summable_of_locally_summable_norm
    (schwartz_locally_summable_lattice L f)
  exact (ContinuousMap.tsum_apply hs x).symm

lemma periodization_add (L : Submodule ℤ E) [DiscreteTopology L]
    (f : 𝓢(E, ℂ)) (x : E) (z : L) :
    periodization L f (x + (z : E)) = periodization L f x := by
  simp only [periodization_apply]
  simpa [add_assoc] using (Equiv.addLeft z).tsum_eq (fun w : L => f (x + (w : E)))

section Coordinates
variable {d : Type*} [Fintype d] [DecidableEq d]

abbrev stdLattice (d : Type*) [Fintype d] [DecidableEq d] : Submodule ℤ (d → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ d))

def torusProjection (x : d → ℝ) : UnitAddTorus d := fun i => (x i : UnitAddCircle)

omit [Fintype d] [DecidableEq d] in
lemma torusProjection_openQuotient : IsOpenQuotientMap (torusProjection (d := d)) :=
  IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)

lemma mem_stdLattice_iff (x : d → ℝ) :
    x ∈ stdLattice d ↔ ∀ i, ∃ n : ℤ, (n : ℝ) = x i := by
  simpa using (Pi.basisFun ℝ d).mem_span_iff_repr_mem ℤ x

lemma torusProjection_eq_iff (x y : d → ℝ) :
    torusProjection x = torusProjection y ↔ x - y ∈ stdLattice d := by
  rw [mem_stdLattice_iff, funext_iff]
  change (∀ i, (x i : UnitAddCircle) = (y i : UnitAddCircle)) ↔ _
  apply forall_congr'
  intro i
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  simp only [zsmul_eq_mul, mul_one, Pi.sub_apply]

def torusRepresentative (x : UnitAddTorus d) : d → ℝ :=
  fun i => (AddCircle.equivIoc 1 0 (x i)).1

omit [Fintype d] [DecidableEq d] in
lemma torusProjection_representative (x : UnitAddTorus d) :
    torusProjection (torusRepresentative x) = x := by
  ext i
  exact AddCircle.coe_equivIoc

lemma periodization_eq_of_projection_eq (f : 𝓢(d → ℝ, ℂ)) (x y : d → ℝ)
    (h : torusProjection x = torusProjection y) :
    periodization (stdLattice d) f x = periodization (stdLattice d) f y := by
  have hz := (torusProjection_eq_iff x y).mp h
  simpa using periodization_add (stdLattice d) f y ⟨x - y, hz⟩

def torusPeriodization (f : 𝓢(d → ℝ, ℂ)) : C(UnitAddTorus d, ℂ) where
  toFun x := periodization (stdLattice d) f (torusRepresentative x)
  continuous_toFun := by
    apply torusProjection_openQuotient.isQuotientMap.continuous_iff.mpr
    have he : (fun x : d → ℝ =>
        periodization (stdLattice d) f (torusRepresentative (torusProjection x))) =
        periodization (stdLattice d) f := by
      funext x
      exact periodization_eq_of_projection_eq f _ _ (torusProjection_representative _)
    simpa only [Function.comp_def, he] using (periodization (stdLattice d) f).continuous

lemma torusPeriodization_projection (f : 𝓢(d → ℝ, ℂ)) (x : d → ℝ) :
    torusPeriodization f (torusProjection x) = periodization (stdLattice d) f x :=
  periodization_eq_of_projection_eq f _ _ (torusProjection_representative _)

lemma torusProjection_lattice_add (z : stdLattice d) (x : d → ℝ) :
    torusProjection ((z : d → ℝ) + x) = torusProjection x := by
  rw [torusProjection_eq_iff]
  simp only [add_sub_cancel_right, SetLike.coe_mem]

omit [DecidableEq d] in
lemma stdFundamental_restrict :
    (volume : Measure (d → ℝ)).restrict (ZSpan.fundamentalDomain (Pi.basisFun ℝ d)) =
    volume.restrict {x : d → ℝ | ∀ i, x i ∈ Ioc 0 1} := by
  have hco : ZSpan.fundamentalDomain (Pi.basisFun ℝ d) =
      Set.univ.pi (fun _ : d => Ico (0 : ℝ) 1) := by
    ext x
    simp [ZSpan.fundamentalDomain, Set.mem_pi]
  have hoc : {x : d → ℝ | ∀ i, x i ∈ Ioc 0 1} =
      Set.univ.pi (fun _ : d => Ioc (0 : ℝ) 1) := by
    ext x
    simp [Set.mem_pi]
  rw [hco, hoc, volume_pi, Measure.restrict_pi_pi, Measure.restrict_pi_pi]
  congr 1
  funext i
  exact restrict_Ico_eq_restrict_Ioc

omit [DecidableEq d] in
lemma mFourier_point_norm (n : d → ℤ) (x : UnitAddTorus d) :
    ‖UnitAddTorus.mFourier n x‖ = 1 := by
  simp [UnitAddTorus.mFourier, fourier_apply, Circle.norm_coe]

lemma torusPeriodization_coefficient (f : 𝓢(d → ℝ, ℂ)) (n : d → ℤ) :
    UnitAddTorus.mFourierCoeff (torusPeriodization f) n =
      ∫ x : d → ℝ, UnitAddTorus.mFourier (-n) (torusProjection x) * f x := by
  let : VAddInvariantMeasure (stdLattice d) (d → ℝ) volume :=
    inferInstanceAs (VAddInvariantMeasure (stdLattice d).toAddSubgroup (d → ℝ) volume)
  let g : (d → ℝ) → ℂ := fun x => UnitAddTorus.mFourier (-n) (torusProjection x) * f x
  have hc : Continuous (fun x : d → ℝ => UnitAddTorus.mFourier (-n) (torusProjection x)) :=
    (UnitAddTorus.mFourier (-n)).continuous.comp torusProjection_openQuotient.continuous
  have hg : Integrable g := f.integrable.bdd_mul hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => le_of_eq (mFourier_point_norm (-n) (torusProjection x))))
  have hgc : Continuous g := hc.mul f.continuous
  have hdom := ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ d) (volume : Measure (d → ℝ))
  have hseries : (∑' z : stdLattice d, ∫⁻ x in ZSpan.fundamentalDomain (Pi.basisFun ℝ d),
      ‖g ((z : d → ℝ) + x)‖ₑ) ≠ ⊤ := by
    have hs := hdom.lintegral_eq_tsum'' (fun x => ‖g x‖ₑ)
    change (∫⁻ x : d → ℝ, ‖g x‖ₑ) =
      (∑' z : stdLattice d, ∫⁻ x in ZSpan.fundamentalDomain (Pi.basisFun ℝ d),
        ‖g ((z : d → ℝ) + x)‖ₑ) at hs
    rw [← hs]
    exact (hasFiniteIntegral_iff_enorm.mp hg.hasFiniteIntegral).ne
  calc
    UnitAddTorus.mFourierCoeff (torusPeriodization f) n =
        ∫ x in {x : d → ℝ | ∀ i, x i ∈ Ioc 0 1},
          UnitAddTorus.mFourier (-n) (torusProjection x) *
            periodization (stdLattice d) f x := by
      rw [UnitAddTorus.mFourierCoeff_eq_integral _ _ (0 : d → ℝ)]
      simp only [Pi.zero_apply, zero_add, smul_eq_mul]
      apply integral_congr_ae
      filter_upwards with x
      change _ * torusPeriodization f (torusProjection x) = _
      rw [torusPeriodization_projection]
      rfl
    _ = ∫ x in ZSpan.fundamentalDomain (Pi.basisFun ℝ d),
          UnitAddTorus.mFourier (-n) (torusProjection x) *
            periodization (stdLattice d) f x := by rw [stdFundamental_restrict]
    _ = ∫ x in ZSpan.fundamentalDomain (Pi.basisFun ℝ d),
          ∑' z : stdLattice d, g ((z : d → ℝ) + x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [periodization_apply, ← tsum_mul_left]
      apply tsum_congr
      intro z
      dsimp only [g]
      rw [torusProjection_lattice_add, add_comm (z : d → ℝ) x]
    _ = ∑' z : stdLattice d, ∫ x in ZSpan.fundamentalDomain (Pi.basisFun ℝ d),
          g ((z : d → ℝ) + x) := by
      exact integral_tsum (fun z => (hgc.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
        hseries
    _ = ∫ x : d → ℝ, g x := (hdom.integral_eq_tsum'' g hg).symm

def coordinateFourier (f : 𝓢(d → ℝ, ℂ)) : 𝓢(d → ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : d => ℝ)).symm
    (𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : d => ℝ)) f))

omit [DecidableEq d] in
lemma coordinateFourier_apply (f : 𝓢(d → ℝ, ℂ)) (w : d → ℝ) :
    coordinateFourier f w =
      ∫ x : d → ℝ, (Real.fourierChar (-∑ i, x i * w i) : ℂ) * f x := by
  change (𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : d => ℝ)) f)) (WithLp.toLp 2 w) = _
  rw [SchwartzMap.fourier_coe, Real.fourier_eq]
  have he := (PiLp.volume_preserving_ofLp d).integral_comp
    (MeasurableEquiv.toLp 2 (d → ℝ)).symm.measurableEmbedding
    (fun x : d → ℝ => (Real.fourierChar (-∑ i, x i * w i) : ℂ) * f x)
  convert he using 1
  apply integral_congr_ae
  filter_upwards with x
  simp [PiLp.inner_apply, Circle.smul_def, smul_eq_mul,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, PiLp.coe_continuousLinearEquiv,
    mul_comm]

omit [DecidableEq d] in
lemma mFourier_projection (n : d → ℤ) (x : d → ℝ) :
    UnitAddTorus.mFourier n (torusProjection x) =
      (Real.fourierChar (∑ i, x i * (n i : ℝ)) : ℂ) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, torusProjection,
    fourier_coe_apply, Complex.ofReal_one, div_one, Real.fourierChar_apply,
    Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_sum, Complex.ofReal_intCast]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma torusPeriodization_coefficient_fourier (f : 𝓢(d → ℝ, ℂ)) (n : d → ℤ) :
    UnitAddTorus.mFourierCoeff (torusPeriodization f) n =
      coordinateFourier f (fun i => (n i : ℝ)) := by
  rw [torusPeriodization_coefficient, coordinateFourier_apply]
  apply integral_congr_ae
  filter_upwards with x
  simp only [mFourier_projection, Pi.neg_apply, Int.cast_neg, mul_neg, Finset.sum_neg_distrib]

lemma stdLattice_coordinates (z : stdLattice d) :
    (fun i => ((((Pi.basisFun ℝ d).restrictScalars ℤ).equivFun z i : ℤ) : ℝ)) =
      (z : d → ℝ) := by
  ext i
  exact (Pi.basisFun ℝ d).restrictScalars_repr_apply ℤ z i

lemma schwartz_summable_integerCoordinates (f : 𝓢(d → ℝ, ℂ)) :
    Summable (fun n : d → ℤ => f (fun i => (n i : ℝ))) := by
  apply ((Pi.basisFun ℝ d).restrictScalars ℤ).equivFun.toEquiv.summable_iff.mp
  change Summable (fun z : stdLattice d =>
    f (fun i => ((((Pi.basisFun ℝ d).restrictScalars ℤ).equivFun z i : ℤ) : ℝ)))
  simpa only [stdLattice_coordinates] using schwartz_summable_lattice (stdLattice d) f

lemma torusPeriodization_summable_coefficients (f : 𝓢(d → ℝ, ℂ)) :
    Summable (UnitAddTorus.mFourierCoeff (torusPeriodization f)) := by
  have he : UnitAddTorus.mFourierCoeff (torusPeriodization f) =
      (fun n : d → ℤ => coordinateFourier f (fun i => (n i : ℝ))) := by
    funext n
    exact torusPeriodization_coefficient_fourier f n
  rw [he]
  exact schwartz_summable_integerCoordinates (coordinateFourier f)

lemma periodization_integerCoordinates (f : 𝓢(d → ℝ, ℂ)) (x : d → ℝ) :
    periodization (stdLattice d) f x = ∑' n : d → ℤ, f (x + fun i => (n i : ℝ)) := by
  rw [periodization_apply]
  have he := ((Pi.basisFun ℝ d).restrictScalars ℤ).equivFun.toEquiv.tsum_eq
    (fun n : d → ℤ => f (x + fun i => (n i : ℝ)))
  change (∑' z : stdLattice d,
    f (x + fun i => ((((Pi.basisFun ℝ d).restrictScalars ℤ).equivFun z i : ℤ) : ℝ))) = _ at he
  simpa only [stdLattice_coordinates] using he

theorem poisson_coordinates (f : 𝓢(d → ℝ, ℂ)) (x : d → ℝ) :
    HasSum (fun n : d → ℤ => coordinateFourier f (fun i => (n i : ℝ)) *
      (Real.fourierChar (∑ i, x i * (n i : ℝ)) : ℂ))
      (∑' n : d → ℤ, f (x + fun i => (n i : ℝ))) := by
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable
    (torusPeriodization_summable_coefficients f) (torusProjection x)
  simpa only [torusPeriodization_coefficient_fourier, smul_eq_mul, mFourier_projection,
    torusPeriodization_projection, periodization_integerCoordinates, mul_comm] using h

theorem poisson_coordinates_zero (f : 𝓢(d → ℝ, ℂ)) :
    ∑' n : d → ℤ, f (fun i => (n i : ℝ)) =
      ∑' n : d → ℤ, coordinateFourier f (fun i => (n i : ℝ)) := by
  have h := (poisson_coordinates f 0).tsum_eq
  simpa using h.symm

end Coordinates
end CubicPoisson

end
end

end OAI
