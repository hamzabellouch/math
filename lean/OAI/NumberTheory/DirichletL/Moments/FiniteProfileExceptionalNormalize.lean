import OAI.NumberTheory.DirichletL.Moments.FiniteProfileExceptionalUnit

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentFiniteProfileExceptional
open HeckeFamily CenteredMomentHeckeTwist

def sourceControl (S : Finset (ℕ×ℕ)) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W

def normalizedProfile (S : Finset (ℕ×ℕ)) (W : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  (sourceControl S W)⁻¹ • W

theorem sourceControl_nonneg (S) (W : 𝓢(ℝ,ℂ)) : 0≤sourceControl S W := apply_nonneg _ _

theorem sourceControl_zero (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S)
    (W : 𝓢(ℝ,ℂ)) (hW : sourceControl S W=0) : W=0 := by
  ext x
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  exact (SchwartzMap.norm_le_seminorm ℝ W x).trans
    ((Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ) hS).trans_eq hW)

theorem normalizedProfile_control (S) (W : 𝓢(ℝ,ℂ)) :
    sourceControl S (normalizedProfile S W)≤1 := by
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) ((sourceControl S W)⁻¹ • W)≤1
  rw [map_smul_eq_mul,Real.norm_of_nonneg (inv_nonneg.mpr (sourceControl_nonneg S W))]
  change (sourceControl S W)⁻¹*sourceControl S W≤1
  by_cases h : sourceControl S W=0
  · simp [h]
  · rw [inv_mul_cancel₀ h]

theorem normalizedProfile_support (S) (W : 𝓢(ℝ,ℂ)) :
    Function.support (normalizedProfile S W:ℝ→ℂ)⊆Function.support (W:ℝ→ℂ) := by
  intro x hx hw
  apply hx
  simp [normalizedProfile,smul_apply,hw]

theorem normalizedProfile_reconstruct (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S)
    (W : 𝓢(ℝ,ℂ)) : sourceControl S W • normalizedProfile S W=W := by
  by_cases h : sourceControl S W=0
  · rw [sourceControl_zero S hS W h]
    simp [sourceControl,normalizedProfile]
  · simp [normalizedProfile,smul_smul,h]

theorem twistedIdealSum_profile_smul (χ : Character) (W : 𝓢(ℝ,ℂ))
    (c t X : ℝ) : twistedIdealSum χ (c • W : 𝓢(ℝ,ℂ)) t X = (c:ℂ)*twistedIdealSum χ W t X := by
  unfold twistedIdealSum
  rw [←tsum_mul_left]
  apply tsum_congr
  intro I
  change _ * ((c:ℂ) * W _) = (c:ℂ) * (_ * W _)
  ring

theorem twistedIdealSum_normalized (S : Finset (ℕ×ℕ)) (hS : (0,0)∈S)
    (χ : Character) (W : 𝓢(ℝ,ℂ)) (t X : ℝ) :
    twistedIdealSum χ W t X = (sourceControl S W:ℂ)*
      twistedIdealSum χ (normalizedProfile S W) t X := by
  rw [←twistedIdealSum_profile_smul,normalizedProfile_reconstruct S hS W]
end SevenEighths.CenteredMomentFiniteProfileExceptional

end

end OAI
