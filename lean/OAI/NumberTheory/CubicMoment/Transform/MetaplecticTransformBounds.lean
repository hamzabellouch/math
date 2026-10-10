import OAI.NumberTheory.CubicMoment.Transform.MetaplecticVoronoi
import OAI.NumberTheory.CubicMoment.Angular.AngularDualContour
import OAI.NumberTheory.CubicMoment.Estimates.MellinWeightFamily

namespace OAI

/-! Bounds for the literal angular Voronoi transform. Its Gamma quotient
is a product of two ordinary shifted Hecke quotients, so the only
special-function input is the same precise DLMF bounded-strip estimate. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

def metaplecticAngularShift (ℓ : ℤ) : ℝ := (|ℓ|:ℤ)/2

lemma metaplecticAngularShift_nonneg (ℓ : ℤ) : 0 ≤ metaplecticAngularShift ℓ := by
  unfold metaplecticAngularShift
  positivity

lemma metaplecticGammaQuotient_factor (ℓ : ℤ) (s : ℂ) :
    metaplecticGammaQuotient ℓ s =
      angularGammaFEQuotient (metaplecticAngularShift ℓ) (s+1/6)*
      angularGammaFEQuotient (metaplecticAngularShift ℓ) (s-1/6) := by
  have hk : (metaplecticAngularShift ℓ:ℂ) = (|ℓ|:ℤ)/2 := by
    simp only [metaplecticAngularShift,Complex.ofReal_div,Complex.ofReal_intCast,
      Complex.ofReal_ofNat]
  have h1 : 1-(s+1/6)+(metaplecticAngularShift ℓ:ℂ) = 5/6+(|ℓ|:ℤ)/2-s := by
    rw [hk]
    ring
  have h2 : 1-(s-1/6)+(metaplecticAngularShift ℓ:ℂ) = 7/6+(|ℓ|:ℤ)/2-s := by
    rw [hk]
    ring
  have h3 : s+1/6+(metaplecticAngularShift ℓ:ℂ) = s+(|ℓ|:ℤ)/2+1/6 := by
    rw [hk]
    ring
  have h4 : s-1/6+(metaplecticAngularShift ℓ:ℂ) = s+(|ℓ|:ℤ)/2-1/6 := by
    rw [hk]
    ring
  unfold metaplecticGammaQuotient angularGammaFEQuotient
  rw [h1,h2,h3,h4]
  ring

theorem metaplecticGamma_vertical_bound (ℓ : ℤ) {σ : ℝ} (hσ : 0 < σ)
    (hGamma : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6)) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ t : ℝ,
      ‖metaplecticGammaQuotient ℓ ((-σ:ℝ)+(t:ℂ)*Complex.I)‖ ≤ C*(1+|t|)^N := by
  obtain ⟨C,N,hC,hG⟩ := hGamma
  refine ⟨C^2,2*N,by positivity,?_⟩
  intro t
  have hplus : (-σ:ℂ)+(t:ℂ)*Complex.I+1/6 =
      ((-σ+1/6:ℝ):ℂ)+(t:ℂ)*Complex.I := by push_cast; ring
  have hminus : (-σ:ℂ)+(t:ℂ)*Complex.I-1/6 =
      ((-σ-1/6:ℝ):ℂ)+(t:ℂ)*Complex.I := by push_cast; ring
  rw [metaplecticGammaQuotient_factor]
  simp only [Complex.ofReal_neg]
  rw [hplus,hminus,norm_mul]
  have hp := hG (-σ+1/6) ⟨by linarith,by linarith⟩ t
  have hm := hG (-σ-1/6) ⟨le_rfl,by linarith⟩ t
  calc
    _ ≤ (C*(1+|t|)^N)*(C*(1+|t|)^N) := mul_le_mul hp hm (_root_.norm_nonneg _) (by positivity)
    _ = _ := by rw [two_mul,pow_add]; ring

/-- A uniform weighted Mellin bound gives a uniform transform bound.
This form permits the actual common-support smooth weight families. -/
lemma metaplecticTransform_bound_of_majorant (ℓ : ℤ) (W : ℝ → ℂ) {σ C B : ℝ}
    (hC : 0 ≤ C) (_hB : 0 ≤ B) (N : ℕ)
    (hQ : ∀ t : ℝ, ‖metaplecticGammaQuotient ℓ ((-σ:ℝ)+(t:ℂ)*Complex.I)‖ ≤
      C*(1+|t|)^N)
    (hW : ∀ t : ℝ, ‖mellin W ((-σ:ℝ)+(t:ℂ)*Complex.I)‖*(1+|t|)^N ≤
      mellinEdgeMajorant B t) {v : ℝ} (hv : 0 < v) :
    ‖metaplecticTransform ℓ W σ v‖ ≤
      (‖((1/(2*Real.pi):ℝ):ℂ)‖*C*B*(∫ t : ℝ, mellinEdgeMajorant 1 t))*v^(-σ) := by
  have hI : 0 ≤ ∫ t : ℝ, mellinEdgeMajorant 1 t := integral_nonneg (fun t => by
    unfold mellinEdgeMajorant
    positivity)
  have hb (t : ℝ) :
      ‖(v:ℂ)^(((-σ:ℝ):ℂ)+(t:ℂ)*Complex.I)*
        metaplecticGammaQuotient ℓ (((-σ:ℝ):ℂ)+(t:ℂ)*Complex.I)*
        mellin W (((-σ:ℝ):ℂ)+(t:ℂ)*Complex.I)‖ ≤
      (v^(-σ)*C*B)*mellinEdgeMajorant 1 t := by
    rw [norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hv]
    have hre : (((-σ:ℝ):ℂ)+(t:ℂ)*Complex.I).re = -σ := by simp
    rw [hre]
    calc
      _ ≤ (v^(-σ)*(C*(1+|t|)^N))*‖mellin W ((-σ:ℝ)+(t:ℂ)*Complex.I)‖ := by
        gcongr
        exact hQ t
      _ = (v^(-σ)*C)*(‖mellin W ((-σ:ℝ)+(t:ℂ)*Complex.I)‖*(1+|t|)^N) := by ring
      _ ≤ (v^(-σ)*C)*mellinEdgeMajorant B t :=
        mul_le_mul_of_nonneg_left (hW t) (by positivity)
      _ = _ := by unfold mellinEdgeMajorant; ring
  rw [metaplecticTransform,norm_mul]
  calc
    _ ≤ ‖((1/(2*Real.pi):ℝ):ℂ)‖*
        (∫ t : ℝ, (v^(-σ)*C*B)*mellinEdgeMajorant 1 t) := by
      apply mul_le_mul_of_nonneg_left _ (_root_.norm_nonneg _)
      exact norm_integral_le_of_norm_le ((mellinEdgeMajorant_integrable 1).const_mul _)
        (Filter.Eventually.of_forall hb)
    _ = _ := by rw [integral_const_mul]; ring

theorem metaplecticTransform_small_line_bound (ℓ : ℤ) {σ : ℝ} (hσ : 0 < σ)
    (hGamma : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, 0 < v →
      ‖metaplecticTransform ℓ W σ v‖ ≤ C*v^(-σ) := by
  obtain ⟨C,N,hC,hQ⟩ := metaplecticGamma_vertical_bound ℓ hσ hGamma
  obtain ⟨B,hB,hM⟩ := mellin_polynomial_majorant W hW hpos hsm (-σ) N
  have hI : 0 ≤ ∫ t : ℝ, mellinEdgeMajorant 1 t := integral_nonneg (fun t => by
    unfold mellinEdgeMajorant
    positivity)
  refine ⟨‖((1/(2*Real.pi):ℝ):ℂ)‖*C*B*(∫ t : ℝ, mellinEdgeMajorant 1 t),by positivity,?_⟩
  intro v hv
  apply metaplecticTransform_bound_of_majorant ℓ W hC hB.le N hQ _ hv
  intro t
  simpa only [sub_zero,abs_zero,add_zero,one_pow,mul_one] using hM 0 t

/-- Uniformity in a genuine smooth family follows from its fixed log
support and derivative bounds. -/
theorem UniformLogWeights.metaplecticTransform_bound {ι : Type*} {W : ι → ℝ → ℂ}
    (hW : UniformLogWeights W) (ℓ : ℤ) {σ : ℝ} (hσ : 0 < σ)
    (hGamma : AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i v, 0 < v →
      ‖metaplecticTransform ℓ (W i) σ v‖ ≤ C*v^(-σ) := by
  obtain ⟨C,N,hC,hQ⟩ := metaplecticGamma_vertical_bound ℓ hσ hGamma
  obtain ⟨B,hB,hM⟩ := hW.mellin_decay σ (N+2)
  have hI : 0 ≤ ∫ t : ℝ, mellinEdgeMajorant 1 t := integral_nonneg (fun t => by
    unfold mellinEdgeMajorant
    positivity)
  refine ⟨‖((1/(2*Real.pi):ℝ):ℂ)‖*C*B*(∫ t : ℝ, mellinEdgeMajorant 1 t),by positivity,?_⟩
  intro i v hv
  apply metaplecticTransform_bound_of_majorant ℓ (W i) hC hB.le N hQ _ hv
  intro t
  unfold mellinEdgeMajorant
  apply (le_div_iff₀ (by positivity : 0 < (1+|t|)^2)).mpr
  calc
    _ = (1+|t|)^(N+2)*‖mellin (W i) ((-σ:ℝ)+(t:ℂ)*Complex.I)‖ := by
      rw [pow_add]
      ring
    _ ≤ B := hM i (-σ) (by simpa only [abs_neg,abs_of_pos hσ] using (le_rfl : σ ≤ σ)) t

end CubicFirstMoment

end

end OAI
