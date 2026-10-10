import OAI.Analysis.LiebThirring.ExtremizerMass

namespace OAI


noncomputable section
namespace SharpLiebThirring
open MeasureTheory Set ExtremizerProof

lemma sharp_times_extremizer_mass {γ : ℝ} (hγ : 1/2 < γ) :
    ENNReal.ofReal (sharpConstant γ)*potentialMass γ (equalityPotential γ) = 1 := by
  rw [(equalityPotential_admissible hγ).mass_eq_ofReal hγ,
    ← ENNReal.ofReal_mul (sharpConstant_pos hγ).le,
    sharp_times_extremizer_integral hγ,ENNReal.ofReal_one]

lemma optimalConstant_le_sharp {γ : ℝ} (hγ₀ : 1/2 < γ) (hγ₁ : γ < 3/2) :
    optimalConstant γ ≤ ENNReal.ofReal (sharpConstant γ) := by
  unfold optimalConstant
  refine iSup_le (fun W ↦ iSup_le (fun hW ↦ iSup_le (fun _ ↦ ?_)))
  exact ENNReal.div_le_of_le_mul (negativeMoment_bound hγ₀ hγ₁ hW)

lemma sharp_le_oneStateConstant {γ : ℝ} (hγ : 1/2 < γ) :
    ENNReal.ofReal (sharpConstant γ) ≤ oneStateConstant γ := by
  have hr : 0 < (γ-1/2)⁻¹ := inv_pos.mpr (by linarith)
  have hW := equalityPotential_admissible hγ
  have hpos : 0 < potentialMass γ (equalityPotential γ) := potential_mass_pos hr
  have hle : ENNReal.ofReal (sharpConstant γ) ≤
      oneStateMoment γ (equalityPotential γ) / potentialMass γ (equalityPotential γ) := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl hpos.ne') (Or.inl (hW.mass_ne_top hγ))).mpr
    rw [sharp_times_extremizer_mass hγ]
    exact one_le_oneStateMoment hr γ
  unfold oneStateConstant
  exact hle.trans (le_iSup_of_le (equalityPotential γ)
    (le_iSup_of_le hW (le_iSup_of_le hpos le_rfl)))

/-- Full sharp Lieb–Thirring bound, both optimal constants, and equality at the
explicit potential; no finite spectral cutoff is imposed. -/
theorem sharp_lieb_thirring : MainClaim := by
  intro γ hγ₀ hγ₁
  have hupper := optimalConstant_le_sharp hγ₀ hγ₁
  have hlower := sharp_le_oneStateConstant hγ₀
  have hone := oneStateConstant_le_optimalConstant γ
  have hr : 0 < (γ-1/2)⁻¹ := inv_pos.mpr (by linarith)
  have hW := equalityPotential_admissible hγ₀
  refine ⟨fun _ hW ↦ negativeMoment_bound hγ₀ hγ₁ hW,
    le_antisymm hupper (hlower.trans hone),le_antisymm (hone.trans hupper) hlower,
    hW,potential_mass_pos hr,?_⟩
  apply le_antisymm (negativeMoment_bound hγ₀ hγ₁ hW)
  rw [sharp_times_extremizer_mass hγ₀]
  exact one_le_negativeMoment hr γ

end SharpLiebThirring

end

end OAI
