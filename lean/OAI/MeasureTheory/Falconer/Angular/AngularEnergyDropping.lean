import OAI.MeasureTheory.Falconer.Angular.AngularTransform
import OAI.MeasureTheory.Falconer.Fourier.AnchorSymbolDropping

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

 theorem sourceAngularTransform_factor (ρ : Measure Plane) (X : Set Plane)
    (hX : MeasurableSet X) (M : ℝ) (b c : Plane → UnitCircle → ℂ) (a : UnitCircle → ℂ)
    (he : ∀ x ∈ X, ∀ ω, b x ω = a ω * c x ω) (r : ℝ) (ω : UnitCircle) :
    sourceAngularTransform ρ X M b r ω = a ω * sourceAngularTransform ρ X M c r ω := by
  unfold sourceAngularTransform
  have hh : (∫ x in X, Complex.exp (Complex.I*(r:ℂ)*(inner ℝ (ω:Plane) x:ℂ))*b x ω ∂ρ) =
      ∫ x in X, a ω*(Complex.exp (Complex.I*(r:ℂ)*(inner ℝ (ω:Plane) x:ℂ))*c x ω) ∂ρ := by
    apply setIntegral_congr_fun hX
    intro x hx
    dsimp only
    rw [he x hx ω]
    ring
  rw [hh,integral_const_mul]
  simp only [Complex.real_smul]
  ring

 theorem sourceAngularMoment_le_of_enorm (U V : ℝ × UnitCircle → ℂ)
    (C : ℝ≥0∞) (hC : C ≠ ∞) (h : ∀ z, ‖U z‖ₑ ≤ C*‖V z‖ₑ) (r : ℝ) :
    sourceAngularMoment U r ≤ C^2 * sourceAngularMoment V r := by
  unfold sourceAngularMoment
  calc
    _ ≤ ∫⁻ ω, (C*‖V (r,ω)‖ₑ)^2 ∂sourceArcLength :=
      lintegral_mono (fun ω => pow_le_pow_left' (h (r,ω)) 2)
    _ = _ := by simp_rw [mul_pow]; exact lintegral_const_mul' _ _ (ENNReal.pow_ne_top hC)

 theorem sourceAngularH_le_of_enorm (a v : ℝ) (Ψ : ℝ → ℝ)
    (U₁ U₂ V₁ V₂ : ℝ × UnitCircle → ℂ) (C₁ C₂ : ℝ≥0∞)
    (hC₁ : C₁ ≠ ∞) (hC₂ : C₂ ≠ ∞)
    (h₁ : ∀ z, ‖U₁ z‖ₑ ≤ C₁*‖V₁ z‖ₑ) (h₂ : ∀ z, ‖U₂ z‖ₑ ≤ C₂*‖V₂ z‖ₑ) :
    sourceAngularH a v Ψ U₁ U₂ ≤ (C₁^2*C₂^2)*sourceAngularH a v Ψ V₁ V₂ := by
  unfold sourceAngularH
  calc
    _ ≤ ENNReal.ofReal ((2:ℝ)^(2*(v-a))) * ∫⁻ r,
        (C₁^2*sourceAngularMoment V₁ r)*(C₂^2*sourceAngularMoment V₂ r)
          ∂sourceAngularShellMeasure v Ψ := by
      apply mul_le_mul_right
      apply lintegral_mono
      intro r
      exact mul_le_mul' (sourceAngularMoment_le_of_enorm U₁ V₁ C₁ hC₁ h₁ r)
        (sourceAngularMoment_le_of_enorm U₂ V₂ C₂ hC₂ h₂ r)
    _ = _ := by
      simp_rw [show ∀ r, (C₁^2*sourceAngularMoment V₁ r)*(C₂^2*sourceAngularMoment V₂ r) =
        (C₁^2*C₂^2)*(sourceAngularMoment V₁ r*sourceAngularMoment V₂ r) from fun r => by ring]
      rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top (ENNReal.pow_ne_top hC₁) (ENNReal.pow_ne_top hC₂))]
      ring

noncomputable def inheritedCircleSymbol {ι : Type*} (S : Finset ι) (b : ι → PolicyDescriptor)
    (k : ι → ℕ) (Q : DyadicSquare) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (h : Plane → ℂ) (x : Plane) (ω : UnitCircle) : ℂ :=
  h x * (inheritedMaskProduct S b k Q ρ m N lam sig J i (fun _ => x) (sourceAngle ω):ℂ)

 theorem inherited_transform_drop {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (P : CellPath) (h : Plane → ℂ)
    {z : Plane} (hz : z ∈ (Q.descendant P).carrier) (M r : ℝ) (ω : UnitCircle) :
    sourceAngularTransform ρ (Q.descendant P).carrier M
      (inheritedCircleSymbol S b k Q ρ m N lam sig J i h) r ω =
      (inheritedMaskProduct (S.filter fun a => descriptorAnchor (b a) ≤ P.length)
        b k Q ρ m N lam sig J i (fun _ => z) (sourceAngle ω):ℂ) *
      sourceAngularTransform ρ (Q.descendant P).carrier M
        (inheritedCircleSymbol (S.filter fun a => P.length < descriptorAnchor (b a))
          b k Q ρ m N lam sig J i h) r ω := by
  apply sourceAngularTransform_factor ρ _ (Q.descendant P).measurable
  intro x hx ω
  unfold inheritedCircleSymbol
  rw [inheritedMaskProduct_split S b k Q hQ ρ m N lam sig J i P hx hz]
  simp only [Complex.ofReal_mul]
  ring

 theorem inherited_transform_drop_enorm {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (P : CellPath) (h : Plane → ℂ)
    (K : ℕ) (hK : ∑ a ∈ S, k a ≤ K) {z : Plane} (hz : z ∈ (Q.descendant P).carrier)
    (M r : ℝ) (ω : UnitCircle) :
    ‖sourceAngularTransform ρ (Q.descendant P).carrier M
      (inheritedCircleSymbol S b k Q ρ m N lam sig J i h) r ω‖ₑ ≤
      ENNReal.ofReal (symbolDerivativeConstant K^K) *
      ‖sourceAngularTransform ρ (Q.descendant P).carrier M
        (inheritedCircleSymbol (S.filter fun a => P.length < descriptorAnchor (b a))
          b k Q ρ m N lam sig J i h) r ω‖ₑ := by
  rw [inherited_transform_drop S b k Q hQ ρ m N lam sig J i P h hz, enorm_mul]
  apply mul_le_mul_left
  rw [← ofReal_norm]
  apply ENNReal.ofReal_le_ofReal
  simpa only [Complex.norm_real] using
    inheritedMaskProduct_removed_bound S b k Q hQ ρ m N lam sig J i P z K hK (sourceAngle ω)

end PlanarFalconer

end OAI
