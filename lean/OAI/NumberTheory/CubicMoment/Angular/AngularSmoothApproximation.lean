import OAI.NumberTheory.CubicMoment.Angular.AngularTruncatedDual

namespace OAI

/-! Uniform smooth dual approximation at each fixed infinity type,
derived from the precise published completion and classical Gamma
inputs. The original sum retains every primitive local Euler factor. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace CubicFirstMoment

def angularRetainedIntegral (W : ℝ → ℂ) (χdual : EisensteinIdealExponent → ℂ)
    (ε : ℂ) (A k Z J t : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*∫ τ : ℝ,
    mellin W ((1/2:ℂ)+(τ:ℂ)*Complex.I)*(Z:ℂ)^((1/2:ℂ)+(τ:ℂ)*Complex.I)*
      angularFiniteHeckeDual (fullIdealBall J) χdual idealExponentNorm ε A k
        ((1/2:ℂ)+((τ-t:ℝ):ℂ)*Complex.I)

/-- Uniform arbitrary-power approximation beyond the natural dual
length. The original sum and retained integral are explicitly defined. -/
theorem angular_smooth_approximation
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {k : ℝ} (hk : 0 ≤ k) {δ : ℝ} (hδ : 0 < δ) (B R : ℝ) :
    ∃ (m : ℕ) (C : ℝ), 2 ≤ m ∧ 0 ≤ C ∧
      ∀ (χ χdual : EisensteinIdealExponent → ℂ),
      (∀ ν, ‖χ ν‖ ≤ 1) → (∀ ν, ‖χdual ν‖ ≤ 1) →
      ∀ (ε : ℂ), ‖ε‖ ≤ 1 → ∀ (Y A Z J t : ℝ),
      1 ≤ Y → 0 < A → 1 ≤ Z → 0 < J → Z ≤ Y^B → J ≤ Y^B →
      (A^2*(1+|t|)^2)/(Z*J) ≤ Y^(-δ) →
      ∀ (L Ldual : ℂ → ℂ), ShiftedPrimitiveHeckeAnalyticData χ χdual A k ε L Ldual →
      ShiftedCompletedHeckeFiniteOrder A k L →
      AngularGammaQuotientStripBound k (1/2-(m:ℝ)) →
      ‖(∑' ν, χ ν*mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)) -
        angularRetainedIntegral W χdual ε A k Z J t‖ ≤ C*Y^(-R) := by
  obtain ⟨m,C,hm,hC,hbound⟩ := angular_dual_tail_arbitrary_power W hW hpos hsm hk hδ B R
  let c : ℂ := ((1/(2*Real.pi):ℝ):ℂ)
  refine ⟨m,‖c‖*C,hm,mul_nonneg (_root_.norm_nonneg _) hC,?_⟩
  intro χ χdual hχ hχdual ε hε Y A Z J t hY hA hZ hJ hZB hJB hcut L Ldual data hcomp hGamma
  have he := angular_smooth_truncated_identity χ χdual hχ hχdual hA hk data hcomp W hW hpos hsm hZ hm J t hGamma
  have hid : (∑' ν, χ ν*mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)) -
      angularRetainedIntegral W χdual ε A k Z J t =
      c*(∫ τ : ℝ, angularDualTailIntegrand W χdual ε A Z J k m t τ) := by
    dsimp [angularRetainedIntegral,c]
    linear_combination he
  rw [hid,norm_mul]
  calc
    _ ≤ ‖c‖*(C*Y^(-R)) := mul_le_mul_of_nonneg_left
      (hbound χdual hχdual ε hε Y A Z J hY hA (zero_lt_one.trans_le hZ) hJ hZB hJB t hcut)
      (_root_.norm_nonneg _)
    _ = _ := by ring


/-- Actual primitive angular characters satisfy the proved approximation.
The constant is chosen before the modulus, character, root and lengths. -/
theorem primitive_angular_smooth_approximation (hpub : PrimitiveAngularHeckeInput)
    (ℓ : ℤ) (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {δ : ℝ} (hδ : 0 < δ) (H R : ℝ)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder
      (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Eisenstein), q ≠ 0 →
      ∀ χ : MulChar (Residues q) ℂ, PrimitiveResidueCharacter q χ →
      AngularUnitCompatible q χ ℓ → (ℓ ≠ 0 ∨ χ ≠ 1) →
      ∃ root : ℂ, ‖root‖ = 1 ∧ ∀ (Y Z J t : ℝ),
      1 ≤ Y → 1 ≤ Z → 0 < J → Z ≤ Y^H → J ≤ Y^H →
      ((residueHeckeScale q)^2*(1+|t|)^2)/(Z*J) ≤ Y^(-δ) →
      ‖(∑' ν, angularResidueIdealChar q χ ℓ ν*mellinPhase t (idealExponentNorm ν)*
          W (idealExponentNorm ν/Z))-
        angularRetainedIntegral W (angularResidueIdealChar q (star χ) (-ℓ)) root
          (residueHeckeScale q) (|(ℓ:ℝ)|/2) Z J t‖ ≤ C*Y^(-R) := by
  have hk : 0 ≤ |(ℓ:ℝ)|/2 := by positivity
  obtain ⟨m,C,hm,hC,hbound⟩ := angular_smooth_approximation W hW hpos hsm hk hδ H R
  refine ⟨C,hC,?_⟩
  intro q hq χ hp hu hn
  obtain ⟨root,L,Ldual,hr,hL,hs,hds,hFE,hcomp⟩ := hpub ℓ q hq χ hp hu hn
  have hχ := angularResidueIdealChar_norm_le_one hq χ ℓ
  have hχdual := angularResidueIdealChar_norm_le_one hq (star χ) (-ℓ)
  have data := shifted_hecke_analyticData_of_completed hχ hχdual
    (residueHeckeScale_pos hq) hk hL hs hds hFE hcomp hGI
  refine ⟨root,hr,?_⟩
  intro Y Z J t hY hZ hJ hZH hJH hcut
  exact hbound _ _ hχ hχdual root hr.le Y (residueHeckeScale q) Z J t hY
    (residueHeckeScale_pos hq) hZ hJ hZH hJH hcut L Ldual data hcomp (hGQ m)

end CubicFirstMoment

end

end OAI
