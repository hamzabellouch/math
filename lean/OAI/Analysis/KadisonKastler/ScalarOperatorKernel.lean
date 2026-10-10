import OAI.Analysis.KadisonKastler.ScalarMeanCoefficients
import OAI.Analysis.KadisonKastler.RationalComplexCore

namespace OAI

/-! # Simultaneous scalar representatives on a countable complex core

An L-infinity-valued bounded sesquilinear kernel has, almost everywhere,
a genuinely sesquilinear bounded scalar kernel on the rational core.
No uncountable intersection of conull sets is used.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {D H : Type*} [MeasurableSpace D] {μ : Measure D}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The bounded sesquilinear coefficient data from which an operator
field is reconstructed. The first vector is the input to the operator. -/
structure ScalarOperatorKernel (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (μ : Measure D) where
  coeff : H → H → ScalarLInfinity μ
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_le : ∀ ξ η, ‖coeff ξ η‖ ≤ bound * ‖ξ‖ * ‖η‖
  add_left : ∀ ξ ζ η, coeff (ξ + ζ) η = coeff ξ η + coeff ζ η
  add_right : ∀ ξ η ζ, coeff ξ (η + ζ) = coeff ξ η + coeff ξ ζ
  smul_left : ∀ (c : ℂ) ξ η, coeff (c • ξ) η = c • coeff ξ η
  smul_right : ∀ (c : ℂ) ξ η, coeff ξ (c • η) = star c • coeff ξ η

namespace ScalarOperatorKernel

variable (K : ScalarOperatorKernel H μ)

theorem add_left_ae (ξ ζ η : H) :
    ∀ᵐ x ∂μ, K.coeff (ξ + ζ) η x = K.coeff ξ η x + K.coeff ζ η x := by
  rw [K.add_left]
  exact (Lp.coeFn_add (K.coeff ξ η) (K.coeff ζ η)).mono fun x hx => by
    simpa only [Pi.add_apply] using hx

theorem add_right_ae (ξ η ζ : H) :
    ∀ᵐ x ∂μ, K.coeff ξ (η + ζ) x = K.coeff ξ η x + K.coeff ξ ζ x := by
  rw [K.add_right]
  exact (Lp.coeFn_add (K.coeff ξ η) (K.coeff ξ ζ)).mono fun x hx => by
    simpa only [Pi.add_apply] using hx

theorem smul_left_ae (c : ℂ) (ξ η : H) :
    ∀ᵐ x ∂μ, K.coeff (c • ξ) η x = c * K.coeff ξ η x := by
  rw [K.smul_left]
  exact (Lp.coeFn_smul c (K.coeff ξ η)).mono fun x hx => by
    simpa only [Pi.smul_apply, smul_eq_mul] using hx

theorem smul_right_ae (c : ℂ) (ξ η : H) :
    ∀ᵐ x ∂μ, K.coeff ξ (c • η) x = star c * K.coeff ξ η x := by
  rw [K.smul_right]
  exact (Lp.coeFn_smul (star c) (K.coeff ξ η)).mono fun x hx => by
    simpa only [Pi.smul_apply, smul_eq_mul] using hx

theorem bound_ae (ξ η : H) :
    ∀ᵐ x ∂μ, ‖K.coeff ξ η x‖ ≤ K.bound * ‖ξ‖ * ‖η‖ :=
  (scalarInfinity_ae_norm_le _).mono fun _ hx => hx.trans (K.norm_le ξ η)


/-- Bundle the coefficient identities as a sesquilinear map. -/
def toLinear : H →ₗ[ℂ] H →ₗ⋆[ℂ] ScalarLInfinity μ where
  toFun ξ :=
    { toFun := K.coeff ξ
      map_add' := K.add_right ξ
      map_smul' := fun c η => K.smul_right c ξ η }
  map_add' ξ ζ := by
    apply LinearMap.ext
    intro η
    exact K.add_left ξ ζ η
  map_smul' c ξ := by
    apply LinearMap.ext
    intro η
    exact K.smul_left c ξ η

/-- The L-infinity coefficient map is jointly continuous. -/
def toContinuous : H →L[ℂ] H →L⋆[ℂ] ScalarLInfinity μ :=
  K.toLinear.mkContinuous₂ K.bound K.norm_le

@[simp]
theorem toContinuous_apply (ξ η : H) : K.toContinuous ξ η = K.coeff ξ η := rfl

/-- Agreement on the dense core determines the whole kernel. -/
theorem coeff_eq_of_core (L : ScalarOperatorKernel H μ) (C : RationalComplexCore H)
    (h : ∀ ξ η : C.space, K.coeff ξ η = L.coeff ξ η) :
    ∀ ξ η : H, K.coeff ξ η = L.coeff ξ η := by
  have hd : DenseRange ((↑) : C.space → H) := C.dense.denseRange_val
  have hout : K.toContinuous = L.toContinuous := by
    apply ContinuousLinearMap.ext
    have he : (fun ξ : H => K.toContinuous ξ) = (fun ξ : H => L.toContinuous ξ) := by
      apply hd.equalizer K.toContinuous.continuous L.toContinuous.continuous
      funext ξ
      apply ContinuousLinearMap.ext
      have hi := hd.equalizer (K.toContinuous ξ).continuous (L.toContinuous ξ).continuous
        (funext fun η => h ξ η)
      exact congrFun hi
    exact congrFun he
  intro ξ η
  exact congrArg (fun F : H →L[ℂ] H →L⋆[ℂ] ScalarLInfinity μ => F ξ η) hout

/-- Pointwise bounded rational sesquilinearity, including the two tests
with multiplication by i that force complex sesquilinearity by continuity. -/
structure CoherentCore (C : RationalComplexCore H) (k : C.space → C.space → ℂ) : Prop where
  add_left : ∀ ξ ζ η, k (ξ + ζ) η = k ξ η + k ζ η
  add_right : ∀ ξ η ζ, k ξ (η + ζ) = k ξ η + k ξ ζ
  rat_left : ∀ (r : ℚ) ξ η, k (r • ξ) η = (r : ℂ) * k ξ η
  rat_right : ∀ (r : ℚ) ξ η, k ξ (r • η) = (r : ℂ) * k ξ η
  I_left : ∀ ξ η, k (C.mulI ξ) η = Complex.I * k ξ η
  I_right : ∀ ξ η, k ξ (C.mulI η) = -Complex.I * k ξ η
  bound : ∀ ξ η, ‖k ξ η‖ ≤ K.bound * ‖ξ‖ * ‖η‖

/-- Countability gives one conull set on which every core identity and
bound holds at once. -/
theorem coherentCore_ae (C : RationalComplexCore H) :
    ∀ᵐ x ∂μ, K.CoherentCore C (fun ξ η => K.coeff (ξ : H) (η : H) x) := by
  let : Countable C.space := C.countable
  have h1 : ∀ᵐ x ∂μ, ∀ ξ ζ η : C.space,
      K.coeff (↑(ξ + ζ)) η x = K.coeff ξ η x + K.coeff ζ η x :=
    ae_all_iff.mpr fun ξ => ae_all_iff.mpr fun ζ => ae_all_iff.mpr fun η =>
      K.add_left_ae ξ ζ η
  have h2 : ∀ᵐ x ∂μ, ∀ ξ η ζ : C.space,
      K.coeff ξ (↑(η + ζ)) x = K.coeff ξ η x + K.coeff ξ ζ x :=
    ae_all_iff.mpr fun ξ => ae_all_iff.mpr fun η => ae_all_iff.mpr fun ζ =>
      K.add_right_ae ξ η ζ
  have h3 : ∀ᵐ x ∂μ, ∀ (r : ℚ) (ξ η : C.space),
      K.coeff (↑(r • ξ)) η x = (r : ℂ) * K.coeff ξ η x := by
    apply ae_all_iff.mpr
    intro r
    apply ae_all_iff.mpr
    intro ξ
    apply ae_all_iff.mpr
    intro η
    simpa only [Submodule.coe_smul, ← Rat.cast_smul_eq_qsmul ℂ] using
      K.smul_left_ae (r : ℂ) ξ η
  have h4 : ∀ᵐ x ∂μ, ∀ (r : ℚ) (ξ η : C.space),
      K.coeff ξ (↑(r • η)) x = (r : ℂ) * K.coeff ξ η x := by
    apply ae_all_iff.mpr
    intro r
    apply ae_all_iff.mpr
    intro ξ
    apply ae_all_iff.mpr
    intro η
    simpa only [Submodule.coe_smul, ← Rat.cast_smul_eq_qsmul ℂ, star_ratCast] using
      K.smul_right_ae (r : ℂ) ξ η
  have h5 : ∀ᵐ x ∂μ, ∀ ξ η : C.space,
      K.coeff (C.mulI ξ) η x = Complex.I * K.coeff ξ η x :=
    ae_all_iff.mpr fun ξ => ae_all_iff.mpr fun η => K.smul_left_ae Complex.I ξ η
  have h6 : ∀ᵐ x ∂μ, ∀ ξ η : C.space,
      K.coeff ξ (C.mulI η) x = -Complex.I * K.coeff ξ η x := by
    apply ae_all_iff.mpr
    intro ξ
    apply ae_all_iff.mpr
    intro η
    simpa only [RationalComplexCore.coe_mulI, Complex.star_def, Complex.conj_I] using
      K.smul_right_ae Complex.I ξ η
  have h7 : ∀ᵐ x ∂μ, ∀ ξ η : C.space,
      ‖K.coeff ξ η x‖ ≤ K.bound * ‖ξ‖ * ‖η‖ :=
    ae_all_iff.mpr fun ξ => ae_all_iff.mpr fun η => K.bound_ae ξ η
  filter_upwards [h1, h2, h3, h4, h5, h6, h7] with x h1 h2 h3 h4 h5 h6 h7
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

end ScalarOperatorKernel

variable [CompleteSpace H] {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G] [IsFiniteMeasure μ]

/-- The scalar boundary mean supplies all data of the bounded operator kernel. -/
def UniformMeasurableOperators.meanKernel (T : UniformMeasurableOperators G D H μ)
    {α : NonsingularAction G D μ} (m : ScalarBoundaryMean α) : ScalarOperatorKernel H μ where
  coeff := T.meanCoefficient m
  bound := T.bound
  bound_nonneg := T.bound_nonneg
  norm_le := T.norm_meanCoefficient_le m
  add_left := T.meanCoefficient_add_left m
  add_right := T.meanCoefficient_add_right m
  smul_left := T.meanCoefficient_smul_left m
  smul_right := T.meanCoefficient_smul_right m

end

end KadisonKastler

end OAI
