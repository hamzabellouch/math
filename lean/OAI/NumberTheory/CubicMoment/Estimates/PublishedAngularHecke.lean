import OAI.NumberTheory.CubicMoment.Angular.AngularHeckeCharacter
import OAI.NumberTheory.CubicMoment.Angular.AngularHeckeGrowth
import OAI.NumberTheory.CubicMoment.Estimates.PublishedPrimitiveHecke

namespace OAI

/-! The fixed-angular primitive input, and its first contour consequence.
Rajan, Acta Arith. 85 (1998), Section 1, pp.281--282, gives the completed
unitary Hecke equation and entire order-one completion. Here the field
has one complex place, discriminant 3, and no imaginary norm parameter.
The Gamma shift is therefore |ell|/2. No smooth-sum estimate is an input. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

/-- Precise published continuation/functional equation for the actual
complete angular ideal coefficients. The dual has angle `-ell` and
conjugate finite character. The exceptional principal case is excluded. -/
def PrimitiveAngularHeckeInput : Prop :=
  ∀ (ℓ : ℤ) (q : Eisenstein), q ≠ 0 → ∀ χ : MulChar (Residues q) ℂ,
    PrimitiveResidueCharacter q χ → AngularUnitCompatible q χ ℓ →
    (ℓ ≠ 0 ∨ χ ≠ 1) →
    ∃ (root : ℂ) (L Ldual : ℂ → ℂ), ‖root‖ = 1 ∧ Differentiable ℂ L ∧
      (∀ s : ℂ, 1 < s.re → L s =
        normDirichletSeries (angularResidueIdealChar q χ ℓ) idealExponentNorm s) ∧
      (∀ s : ℂ, 1 < s.re → Ldual s =
        normDirichletSeries (angularResidueIdealChar q (star χ) (-ℓ)) idealExponentNorm s) ∧
      HeckeFunctionalEquation (residueHeckeScale q) (|(ℓ:ℝ)|/2) root L Ldual ∧
      ShiftedCompletedHeckeFiniteOrder (residueHeckeScale q) (|(ℓ:ℝ)|/2) L

theorem primitive_angular_analytic_data (hpub : PrimitiveAngularHeckeInput)
    {ℓ : ℤ} {q : Eisenstein} (hq : q ≠ 0) (χ : MulChar (Residues q) ℂ)
    (hp : PrimitiveResidueCharacter q χ) (hu : AngularUnitCompatible q χ ℓ)
    (hn : ℓ ≠ 0 ∨ χ ≠ 1)
    (hGamma : ∀ m : ℕ,
      GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2)) :
    ∃ (root : ℂ) (L Ldual : ℂ → ℂ), ‖root‖ = 1 ∧
      ShiftedPrimitiveHeckeAnalyticData (angularResidueIdealChar q χ ℓ)
        (angularResidueIdealChar q (star χ) (-ℓ)) (residueHeckeScale q)
        (|(ℓ:ℝ)|/2) root L Ldual := by
  obtain ⟨root,L,Ldual,hr,hL,hs,hds,hFE,hcomp⟩ := hpub ℓ q hq χ hp hu hn
  exact ⟨root,L,Ldual,hr,shifted_hecke_analyticData_of_completed
    (angularResidueIdealChar_norm_le_one hq χ ℓ)
    (angularResidueIdealChar_norm_le_one hq (star χ) (-ℓ))
    (residueHeckeScale_pos hq) (by positivity) hL hs hds hFE hcomp hGamma⟩

theorem angular_hecke_smooth_mellin_left (χ χdual : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {A k : ℝ} {ε : ℂ} {L Ldual : ℂ → ℂ}
    (data : ShiftedPrimitiveHeckeAnalyticData χ χdual A k ε L Ldual)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {Z : ℝ} (hZ : 1 ≤ Z) (m : ℕ) (t : ℝ) :
    (∑' ν, χ ν*mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)) =
      ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ,
        mellin W (((1/2-(m:ℝ)):ℝ)+(τ:ℂ)*Complex.I)*
          (Z:ℂ)^(((1/2-(m:ℝ)):ℝ)+(τ:ℂ)*Complex.I)*
          L (((1/2-(m:ℝ)):ℝ)+((τ-t:ℝ):ℂ)*Complex.I) := by
  obtain ⟨C,n,hC,hgrowth⟩ := data.strip_growth m
  have hshift := mellinHecke_contour_shift W hW hpos hsm
    (show 1/2-(m:ℝ) ≤ 2 by
      have hmr : (0:ℝ) ≤ m := by positivity
      linarith)
    hZ t L data.entire hC n (by intro σ hσ τ; exact hgrowth σ hσ (τ-t))
  norm_num only [Complex.ofReal_ofNat] at hshift
  rw [hecke_twisted_smooth_mellin χ hχ L data.right_series W hW hpos hsm
    (lt_of_lt_of_le zero_lt_one hZ) t,←hshift]

/-- The exact full angular smooth sum on the symmetry line. Its only
outside amplitude is sqrt(Z); the remaining root/conductor/Gamma factor
has modulus one. This follows from the published raw completion. -/
theorem angular_hecke_smooth_symmetry (χ χdual : EisensteinIdealExponent → ℂ)
    (hχ : ∀ ν, ‖χ ν‖ ≤ 1) {A k : ℝ} (hA : 0 < A) (hk : 0 ≤ k)
    {ε : ℂ} {L Ldual : ℂ → ℂ}
    (data : ShiftedPrimitiveHeckeAnalyticData χ χdual A k ε L Ldual)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {Z : ℝ} (hZ : 1 ≤ Z) (t : ℝ) :
    (∑' ν, χ ν*mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)) =
      (((1/(2*Real.pi):ℝ):ℂ)*(Real.sqrt Z:ℂ))*∫ τ : ℝ,
        mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)*
          heckeSymmetryFactor ε (A^2) Z k t τ*
          Ldual ((1/2:ℂ)-((τ-t:ℝ):ℂ)*Complex.I) := by
  have he := angular_hecke_smooth_mellin_left χ χdual hχ data W hW hpos hsm hZ 0 t
  simp only [Nat.cast_zero,sub_zero] at he
  norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] at he
  rw [he]
  have hp (τ : ℝ) := hecke_symmetry_integrand hA
    (lt_of_lt_of_le zero_lt_one hZ) hk data.functional_equation (mellin W) t τ
  simp only [mul_assoc] at hp ⊢
  simp_rw [hp]
  rw [integral_const_mul]
  simp only [Complex.ofReal_div,Complex.ofReal_one]

end CubicFirstMoment

end

end OAI
