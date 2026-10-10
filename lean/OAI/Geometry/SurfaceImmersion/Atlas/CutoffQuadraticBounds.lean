import OAI.Geometry.SurfaceImmersion.Geometry.ScaledMetricQuadraticTargets
import OAI.Geometry.SurfaceImmersion.Atlas.SupportedWeightedSeminorm

namespace OAI

/-! Fixed cutoff multiplication preserves the delta-squared quadratic estimate. -/
noncomputable section
open Set
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma cutoff_square_complex_bound {K : TopologicalSpace.Compacts SmallModes.Base}
    (χ : SupportedField (F := ℝ) K) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s : ℝ, 0 < s → s ≤ 1 →
      WeightedBound univ s m D (fun x => ((χ x * χ x : ℝ) : ℂ)) := by
  let C := supportedWeightedSeminorm K 1 m χ
  have hC : 0 ≤ C := apply_nonneg _ _
  refine ⟨2^m*C*C,by positivity,?_⟩
  intro s hs hs1
  have hb : WeightedBound univ s m C χ :=
    (weightedBound_of_supportedSeminorm 1 m χ).shrink_scale hs.le hs1
  have hχc : ContDiffOn ℝ ∞ (fun x => (χ x : ℂ)) univ :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn χ.contDiff.contDiffOn
  have hbc := QuadraticMean.weighted_real_complex isOpen_univ.uniqueDiffOn hs.le hC χ.contDiff.contDiffOn hb
  have hm : WeightedBound univ s m (2^m*C*C) (fun x => (χ x : ℂ)*(χ x : ℂ)) :=
    WeightedBound.mul isOpen_univ.uniqueDiffOn hs.le hC hC hχc hχc hbc hbc
  simpa only [Complex.ofReal_mul] using hm

theorem cutoff_quadratic_bound {ι : Type*} {K : TopologicalSpace.Compacts SmallModes.Base}
    (χ : SupportedField (F := ℝ) K) (m : ℕ) (A P : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (τ s δ : ℝ)
      (φ : ι → SmallModes.Base → ℝ) (Z : ι → SmallModes.Field 4),
      (∀ a, ContDiff ℝ ∞ (φ a)) → (∀ a, ContDiff ℝ ∞ (Z a)) →
      0 < τ → 0 < s → τ ≤ s → s ≤ 1 → 0 ≤ δ → 0 ≤ A → 0 ≤ P →
      (∀ a, WeightedBound univ s (m+1) (A*(δ*τ)) (Z a)) →
      (∀ a v, ‖v‖ ≤ 1 → WeightedBound univ s m P (SmallModes.coordDeriv v (φ a))) →
      ∀ l : RealModes.QuadraticLabel ι,
      WeightedBound univ s m (B*δ^2)
        (fun x => (χ x)^2 • RealModes.quadraticAmplitude τ φ Z l x) := by
  obtain ⟨D,hD,hd⟩ := cutoff_square_complex_bound χ m
  let C := 4 * 2^m * ((1+2^m*P)*A)^2
  refine ⟨2^m*D*C,by dsimp [C]; positivity,?_⟩
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
  ring

end ClosedSurfaceR4.JetPolynomial

end

end OAI
