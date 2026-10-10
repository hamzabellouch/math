import OAI.Analysis.IrrationalRotation.Model.Product
import OAI.Analysis.IrrationalRotation.Rotation.FieldDiagonal
import OAI.Analysis.IrrationalRotation.Spectral.RotationDeterminant
import OAI.Analysis.IrrationalRotation.Product.ProductWeightBridge

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.ProductModel

theorem multiplier_coordinates_ae (θ : ℕ → ℝ) (g : Base → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) (ξ : Hilbert) :
    ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      multiplier θ g C hC hg hb ξ x k = g (rotationIterate θ k x) * ξ x k := by
  unfold multiplier
  exact WeightedShift.fieldDiagonal_coordinate_ae _ _ _ _ _ ξ

theorem multiplier_operator_ext {A B : Hilbert →L[ℂ] Hilbert}
    (h : ∀ ξ : Hilbert, ∀ᵐ x ∂baseMeasure, ∀ k : ℤ, A ξ x k = B ξ x k) :
    A = B := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [h ξ] with x hx
  exact lp.ext (funext hx)

theorem vectorTrace_multiplier (θ : ℕ → ℝ) (g : Base → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) :
    vectorTrace traceVector (multiplier θ g C hC hg hb) = ∫ x, g x ∂baseMeasure := by
  change inner ℂ traceVector (multiplier θ g C hC hg hb traceVector) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  have hv : traceVector =ᵐ[baseMeasure]
      fun _ => lp.single 2 (0 : ℤ) (1 : ℂ) := Lp.coeFn_const 2 baseMeasure _
  filter_upwards [hv, multiplier_coordinates_ae θ g C hC hg hb traceVector] with x hv hm
  rw [hv, lp.inner_single_left]
  rw [hm 0, hv]
  simp
  congr 1
  funext i
  simp [Invariant233.ProductModel.rotationIterate]

section ContinuousValues
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]

def continuousValueMultiplier (θ : ℕ → ℝ) (a : Base → Y) (ha : Measurable a)
    (f : C(Y, ℂ)) : Hilbert →L[ℂ] Hilbert :=
  multiplier θ (fun x => f (a x)) ‖f‖ (norm_nonneg f)
    (f.continuous.measurable.comp ha) (fun x => f.norm_coe_le_norm (a x))

theorem continuousValueMultiplier_coordinates_ae (θ : ℕ → ℝ)
    (a : Base → Y) (ha : Measurable a) (f : C(Y, ℂ)) (ξ : Hilbert) :
    ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      continuousValueMultiplier θ a ha f ξ x k =
        f (a (rotationIterate θ k x)) * ξ x k :=
  multiplier_coordinates_ae θ _ _ _ _ _ ξ

@[simp] theorem continuousValueMultiplier_one (θ : ℕ → ℝ)
    (a : Base → Y) (ha : Measurable a) :
    continuousValueMultiplier θ a ha 1 = 1 := by
  apply multiplier_operator_ext
  intro ξ
  filter_upwards [continuousValueMultiplier_coordinates_ae θ a ha 1 ξ] with x hx
  intro k
  simpa only [ContinuousMap.one_apply, one_mul, one_apply_eq_self] using hx k

@[simp] theorem continuousValueMultiplier_mul (θ : ℕ → ℝ)
    (a : Base → Y) (ha : Measurable a) (f g : C(Y, ℂ)) :
    continuousValueMultiplier θ a ha (f * g) =
      continuousValueMultiplier θ a ha f * continuousValueMultiplier θ a ha g := by
  apply multiplier_operator_ext
  intro ξ
  filter_upwards [continuousValueMultiplier_coordinates_ae θ a ha (f * g) ξ,
    continuousValueMultiplier_coordinates_ae θ a ha f (continuousValueMultiplier θ a ha g ξ),
    continuousValueMultiplier_coordinates_ae θ a ha g ξ] with x hfg hf hg
  intro k
  change continuousValueMultiplier θ a ha (f * g) ξ x k =
    continuousValueMultiplier θ a ha f (continuousValueMultiplier θ a ha g ξ) x k
  rw [hfg k, hf k, hg k, ContinuousMap.mul_apply, mul_assoc]

@[simp] theorem continuousValueMultiplier_add (θ : ℕ → ℝ)
    (a : Base → Y) (ha : Measurable a) (f g : C(Y, ℂ)) :
    continuousValueMultiplier θ a ha (f + g) =
      continuousValueMultiplier θ a ha f + continuousValueMultiplier θ a ha g := by
  apply multiplier_operator_ext
  intro ξ
  filter_upwards [continuousValueMultiplier_coordinates_ae θ a ha (f + g) ξ,
    continuousValueMultiplier_coordinates_ae θ a ha f ξ,
    continuousValueMultiplier_coordinates_ae θ a ha g ξ,
    Lp.coeFn_add (continuousValueMultiplier θ a ha f ξ)
      (continuousValueMultiplier θ a ha g ξ)] with x hfg hf hg hs
  intro k
  change continuousValueMultiplier θ a ha (f + g) ξ x k =
    ((continuousValueMultiplier θ a ha f ξ + continuousValueMultiplier θ a ha g ξ) x) k
  rw [hs]
  change continuousValueMultiplier θ a ha (f + g) ξ x k =
    continuousValueMultiplier θ a ha f ξ x k + continuousValueMultiplier θ a ha g ξ x k
  rw [hfg k, hf k, hg k, ContinuousMap.add_apply, add_mul]

@[simp] theorem continuousValueMultiplier_smul (θ : ℕ → ℝ)
    (a : Base → Y) (ha : Measurable a) (z : ℂ) (f : C(Y, ℂ)) :
    continuousValueMultiplier θ a ha (z • f) = z • continuousValueMultiplier θ a ha f := by
  apply multiplier_operator_ext
  intro ξ
  filter_upwards [continuousValueMultiplier_coordinates_ae θ a ha (z • f) ξ,
    continuousValueMultiplier_coordinates_ae θ a ha f ξ,
    Lp.coeFn_smul z (continuousValueMultiplier θ a ha f ξ)] with x hzf hf hs
  intro k
  change continuousValueMultiplier θ a ha (z • f) ξ x k =
    ((z • continuousValueMultiplier θ a ha f ξ) x) k
  rw [hs]
  change continuousValueMultiplier θ a ha (z • f) ξ x k =
    z * continuousValueMultiplier θ a ha f ξ x k
  rw [hzf k, hf k]
  simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_assoc]

@[simp] theorem continuousValueMultiplier_star (θ : ℕ → ℝ)
    (a : Base → Y) (ha : Measurable a) (f : C(Y, ℂ)) :
    continuousValueMultiplier θ a ha (star f) = star (continuousValueMultiplier θ a ha f) := by
  unfold continuousValueMultiplier multiplier
  apply WeightedShift.fieldDiagonal_star_of_eq
  exact Filter.Eventually.of_forall fun x => lp.ext (funext fun k => rfl)

@[simp] theorem continuousValueMultiplier_zero (θ : ℕ → ℝ)
    (a : Base → Y) (ha : Measurable a) : continuousValueMultiplier θ a ha 0 = 0 := by
  have h := continuousValueMultiplier_smul θ a ha (0 : ℂ) (1 : C(Y, ℂ))
  apply ContinuousLinearMap.ext
  intro vector
  simpa only [zero_smul, smul_apply, zero_apply]
    using congrArg (fun operator : Hilbert →L[ℂ] Hilbert => operator vector) h

def continuousValueRepresentation (θ : ℕ → ℝ) (a : Base → Y) (ha : Measurable a) :
    C(Y, ℂ) →⋆ₐ[ℂ] (Hilbert →L[ℂ] Hilbert) where
  toFun := continuousValueMultiplier θ a ha
  map_one' := continuousValueMultiplier_one θ a ha
  map_mul' := continuousValueMultiplier_mul θ a ha
  map_zero' := continuousValueMultiplier_zero θ a ha
  map_add' := continuousValueMultiplier_add θ a ha
  commutes' z := by
    simp only [Algebra.algebraMap_eq_smul_one, continuousValueMultiplier_smul,
      continuousValueMultiplier_one]
  map_star' := continuousValueMultiplier_star θ a ha

theorem vectorTrace_continuousValueRepresentation (θ : ℕ → ℝ)
    (a : Base → Y) (ha : Measurable a) (f : C(Y, ℂ)) :
    vectorTrace traceVector (continuousValueRepresentation θ a ha f) =
      ∫ x, f (a x) ∂baseMeasure :=
  vectorTrace_multiplier θ (fun x => f (a x)) ‖f‖ (norm_nonneg f)
    (f.continuous.measurable.comp ha) (fun x => f.norm_coe_le_norm (a x))

end ContinuousValues
end Invariant233.ProductModel

namespace Invariant233

theorem vectorFugledeKadisonDeterminant_composed_representation
    {H X Y : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace X] [TopologicalSpace Y] [CompactSpace Y]
    (μ : Measure X) (a : X → Y)
    (π : C(Y, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hξ : ∀ g : C(Y, ℂ), vectorTrace ξ (π g) = ∫ x, g (a x) ∂μ)
    (f : C(Y, ℂ)) :
    vectorFugledeKadisonDeterminant ξ (π f) =
      ⨅ ε : {r : ℝ // 0 < r}, ENNReal.ofReal
        (Real.exp ((∫ x, Real.log (‖f (a x)‖ ^ 2 + ε.val) ∂μ) / 2)) := by
  let : NormedAlgebra ℝ C(Y, ℂ) := NormedAlgebra.restrictScalars ℝ ℂ C(Y, ℂ)
  unfold vectorFugledeKadisonDeterminant
  apply iInf_congr
  intro ε
  rw [← regularizedLog_map π f ε.val ε.property, hξ]
  have hpoint : ∀ y, (CFC.log (star f * f + ε.val • (1 : C(Y, ℂ)))) y =
      (Real.log (‖f y‖ ^ 2 + ε.val) : ℂ) := by
    intro y
    have h := regularizedLog_map (ContinuousMap.evalStarAlgHom ℂ ℂ y) f ε.val ε.property
    simpa only [ContinuousMap.evalStarAlgHom_apply] using
      h.trans (regularizedLog_complex (f y) ε.val)
  simp_rw [hpoint]
  rw [integral_complex_ofReal]
  rfl

end Invariant233

end

end OAI
