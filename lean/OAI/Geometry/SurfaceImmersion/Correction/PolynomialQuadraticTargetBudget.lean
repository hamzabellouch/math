import OAI.Geometry.SurfaceImmersion.Atlas.CutoffQuadraticBounds
import OAI.Geometry.SurfaceImmersion.Correction.PolynomialBudgetAlgebra

namespace OAI

/-! The quadratic target constant is polynomial in the amplitude and phase
budgets, with the fixed cutoff constant kept explicit. -/
noncomputable section
open Set
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

def quadraticTargetBudget (m : ℕ) (D A P : ℝ) : ℝ :=
  2^m*D*(4*2^m*((1+2^m*P)*A)^2)

theorem cutoff_quadratic_bound_explicit {ι : Type*} {K : TopologicalSpace.Compacts SmallModes.Base}
    (χ : SupportedField (F := ℝ) K) (m : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hd : ∀ s : ℝ, 0 < s → s ≤ 1 →
      WeightedBound univ s m D (fun x => ((χ x * χ x : ℝ) : ℂ)))
    (A P : ℝ) :
    ∀ (τ s δ : ℝ)
      (φ : ι → SmallModes.Base → ℝ) (Z : ι → SmallModes.Field 4),
      (∀ a, ContDiff ℝ ∞ (φ a)) → (∀ a, ContDiff ℝ ∞ (Z a)) →
      0 < τ → 0 < s → τ ≤ s → s ≤ 1 → 0 ≤ δ → 0 ≤ A → 0 ≤ P →
      (∀ a, WeightedBound univ s (m+1) (A*(δ*τ)) (Z a)) →
      (∀ a v, ‖v‖ ≤ 1 → WeightedBound univ s m P (SmallModes.coordDeriv v (φ a))) →
      ∀ l : RealModes.QuadraticLabel ι,
      WeightedBound univ s m (quadraticTargetBudget m D A P*δ^2)
        (fun x => (χ x)^2 • RealModes.quadraticAmplitude τ φ Z l x) := by
  let C := 4 * 2^m * ((1+2^m*P)*A)^2
  intro τ s δ φ Z hφ hZ hτ hs hτs hs1 hδ hA hP hb hp l
  have hquad : WeightedBound univ s m (δ^2*C) (RealModes.quadraticAmplitude τ φ Z l) :=
    RealModes.scaled_quadraticAmplitude_bound isOpen_univ (fun a => (hφ a).contDiffOn)
      (fun a => (hZ a).contDiffOn) hτ hs hτs hδ hA hP m hb hp l
  have hcs : ContDiffOn ℝ ∞ (fun x => ((χ x * χ x : ℝ) : ℂ)) univ :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (χ.contDiff.contDiffOn.mul χ.contDiff.contDiffOn)
  have hqs : ContDiffOn ℝ ∞ (RealModes.quadraticAmplitude τ φ Z l) univ :=
    (RealModes.quadraticAmplitude_smooth hφ hZ τ l).contDiffOn
  have hout : WeightedBound univ s m (2^m*D*(δ^2*C))
      (fun x => ((χ x * χ x : ℝ) : ℂ) • RealModes.quadraticAmplitude τ φ Z l x) :=
    SmallModes.weighted_smul_field isOpen_univ.uniqueDiffOn hs hD
      (by dsimp [C]; positivity) hcs hqs (hd s hs hs1) hquad
  have he : (fun x => (χ x)^2 • RealModes.quadraticAmplitude τ φ Z l x) =
      (fun x => ((χ x * χ x : ℝ) : ℂ) • RealModes.quadraticAmplitude τ φ Z l x) := by
    funext x j
    rw [Pi.smul_apply,Pi.smul_apply,pow_two]
    rfl
  rw [he]
  convert hout using 1
  dsimp [quadraticTargetBudget,C]
  ring

lemma quadraticTargetBudget_polynomial (m : ℕ) (D A P : ℝ → ℝ)
    (hD : RealModes.HasPolynomialBound D) (hA : RealModes.HasPolynomialBound A)
    (hP : RealModes.HasPolynomialBound P) :
    RealModes.HasPolynomialBound (fun x => quadraticTargetBudget m (D x) (A x) (P x)) := by
  unfold quadraticTargetBudget
  repeat first
    | exact hD
    | exact hA
    | exact hP
    | apply RealModes.HasPolynomialBound.add
    | apply RealModes.HasPolynomialBound.mul
    | apply RealModes.HasPolynomialBound.pow
    | (apply RealModes.polynomialBound_const; positivity)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
