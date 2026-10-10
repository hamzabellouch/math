import OAI.Analysis.KadisonKastler.SpatialProduct
import OAI.Analysis.KadisonKastler.RegularCoreDensePeriods

namespace OAI

/-! # Tensor coefficients turn central commutation into frequency periods

In Fourier coordinates a site eigenoperator is a constant second-leg
operator followed by a frequency translation. Commuting with it forces
an actual first-leg coefficient field to have that period. Two
incommensurable site frequencies therefore make the field constant.
-/

namespace KadisonKastler

open MeasureTheory UnitalTomsWinter
open scoped TensorProduct InnerProductSpace

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
/-- A nonzero site operator detects its first tensor coefficient. -/
theorem spatialTensorOp_left_injective (b : K →L[ℂ] K) (hb : b ≠ 0) :
    Function.Injective (fun a : H →L[ℂ] H => spatialTensorOp a b) := by
  obtain ⟨η, hη⟩ : ∃ η : K, b η ≠ 0 := by
    by_contra h
    apply hb
    ext η
    exact not_exists_not.mp h η
  intro a c hac
  apply ContinuousLinearMap.ext
  intro ξ
  have he := congrArg (fun T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K =>
    T ((ξ ⊗ₜ[ℂ] η : H ⊗[ℂ] K) : SpatialHilbert H K)) hac
  have hz : ‖a ξ - c ξ‖ * ‖b η‖ = 0 := by
    have he' : (((a ξ - c ξ) ⊗ₜ[ℂ] b η : H ⊗[ℂ] K) : SpatialHilbert H K) = 0 := by
      simpa only [spatialTensorOp_coe, TensorProduct.mapL_tmul,
        TensorProduct.sub_tmul, UniformSpace.Completion.coe_sub, sub_eq_zero] using he
    simpa only [UniformSpace.Completion.norm_coe, TensorProduct.norm_tmul,
      norm_zero] using congrArg norm he'
  exact sub_eq_zero.mp (norm_eq_zero.mp
    ((mul_eq_zero.mp hz).resolve_right (norm_ne_zero_iff.mpr hη)))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Commutation with a constant coefficient followed by translation gives
an almost-everywhere field intertwining identity. -/
theorem RepresentsOperatorField.intertwine_translation
    [TopologicalSpace.SeparableSpace E]
    {F : ℝ → E →L[ℂ] E}
    {T : RegularCoreHilbert E →L[ℂ] RegularCoreHilbert E}
    (hF : RepresentsOperatorField volume F T) (b : E →L[ℂ] E) (s : ℝ)
    (hcomm : Commute T (regularConstantHom volume b *
      (regularRightTranslation (H := E) (Multiplicative.ofAdd s) :
        RegularCoreHilbert E →L[ℂ] RegularCoreHilbert E))) :
    ∀ᵐ t ∂volume, F t * b = b * F (t + s) := by
  let R := regularRightTranslation (H := E) (Multiplicative.ofAdd s)
  change Commute T (regularConstantHom volume b *
    (R : RegularCoreHilbert E →L[ℂ] RegularCoreHilbert E)) at hcomm
  have he : T * regularConstantHom volume b = regularConstantHom volume b *
      unitaryConj R T := by
    have h := congrArg (fun S : RegularCoreHilbert E →L[ℂ] RegularCoreHilbert E =>
      S * (star R : RegularCoreHilbert E →L[ℂ] RegularCoreHilbert E)) hcomm.eq
    simpa only [mul_assoc, Unitary.mul_star_self_of_mem R.property, mul_one,
      unitaryConj] using h
  have hl : RepresentsOperatorField volume (fun t => F t * b)
      (T * regularConstantHom volume b) := by
    intro f
    filter_upwards [hF (regularConstantHom volume b f),
      regularConstantHom_apply_ae volume b f] with t ht hb
    change T (regularConstantHom volume b f) t = _
    rw [ht, hb]
    rfl
  have hr : RepresentsOperatorField volume (fun t => b * F (t + s))
      (T * regularConstantHom volume b) := by
    rw [he]
    intro f
    filter_upwards [regularConstantHom_apply_ae volume b (unitaryConj R T f),
      hF.real_translate (Multiplicative.ofAdd s) f] with t hb ht
    change regularConstantHom volume b (unitaryConj R T f) t = _
    rw [hb, ht]
    rfl
  exact hl.field_eq_ae_real hr

/-- A nonzero site eigenoperator forces its frequency to be a period of
the first-leg coefficient field. -/
theorem spatialField_period_of_commute
    [TopologicalSpace.SeparableSpace (SpatialHilbert H K)]
    {F : ℝ → H →L[ℂ] H}
    {T : RegularCoreHilbert (SpatialHilbert H K) →L[ℂ]
      RegularCoreHilbert (SpatialHilbert H K)}
    (hF : RepresentsOperatorField volume (fun t => spatialLeft (K := K) (F t)) T)
    (b : K →L[ℂ] K) (hb : b ≠ 0) (s : ℝ)
    (hcomm : Commute T (regularConstantHom volume (spatialRight (H := H) b) *
      (regularRightTranslation (H := SpatialHilbert H K) (Multiplicative.ofAdd s) :
        RegularCoreHilbert (SpatialHilbert H K) →L[ℂ]
          RegularCoreHilbert (SpatialHilbert H K)))) :
    (fun t => F (t + s)) =ᵐ[volume] F := by
  have h := hF.intertwine_translation (spatialRight (H := H) b) s hcomm
  filter_upwards [h] with t ht
  apply (spatialTensorOp_left_injective b hb)
  have ht' := ht.symm
  change spatialTensorOp 1 b * spatialTensorOp (F (t + s)) 1 =
    spatialTensorOp (F t) 1 * spatialTensorOp 1 b at ht'
  simpa only [← spatialTensorOp_mul, one_mul, mul_one] using ht'

/-- The two site frequencies make a represented spatial coefficient field
constant. No factoriality or core classification is assumed. -/
theorem spatialField_constant_of_two_shifts
    [TopologicalSpace.SeparableSpace H]
    [TopologicalSpace.SeparableSpace (SpatialHilbert H K)]
    {F : ℝ → H →L[ℂ] H}
    {T : RegularCoreHilbert (SpatialHilbert H K) →L[ℂ]
      RegularCoreHilbert (SpatialHilbert H K)}
    (hF : RepresentsOperatorField volume (fun t => spatialLeft (K := K) (F t)) T)
    (hmeas : ∀ ξ, AEStronglyMeasurable (fun t => F t ξ) volume)
    (C : ℝ) (hbound : ∀ᵐ t ∂volume, ‖F t‖ ≤ C)
    (b₁ b₂ : K →L[ℂ] K) (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0)
    (s₁ s₂ : ℝ) (hirr : Irrational (s₁ / s₂))
    (hcomm : ∀ (b : K →L[ℂ] K) (s : ℝ),
      (b = b₁ ∧ s = s₁) ∨ (b = b₂ ∧ s = s₂) →
      Commute T (regularConstantHom volume (spatialRight (H := H) b) *
        (regularRightTranslation (H := SpatialHilbert H K) (Multiplicative.ofAdd s) :
          RegularCoreHilbert (SpatialHilbert H K) →L[ℂ]
            RegularCoreHilbert (SpatialHilbert H K)))) :
    ∃ A : H →L[ℂ] H, F =ᵐ[volume] (fun _ => A) ∧
      T = regularConstantHom volume (spatialLeft (K := K) A) := by
  have h₁ := spatialField_period_of_commute hF b₁ hb₁ s₁
    (hcomm b₁ s₁ (Or.inl ⟨rfl, rfl⟩))
  have h₂ := spatialField_period_of_commute hF b₂ hb₂ s₂
    (hcomm b₂ s₂ (Or.inr ⟨rfl, rfl⟩))
  obtain ⟨A, hA⟩ := bounded_operatorField_two_periods_const F hmeas C hbound hirr h₁ h₂
  refine ⟨A, hA, hF.unique ?_⟩
  intro f
  filter_upwards [regularConstantHom_apply_ae volume (spatialLeft (K := K) A) f,
    hA] with t ht hAt
  rw [ht, hAt]

end

end KadisonKastler

end OAI
