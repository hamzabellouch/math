import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspIntegratedHardy

namespace OAI

/-! A fixed compact parallelogram contains the actual half-open cusp
cell, giving its finite measure and a uniform horizontal norm bound. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaHorizontalCell_compact_container :
    ∃ K : Set ℂ, IsCompact K ∧ cubicThetaHorizontalCell⊆K := by
  let Q : Set (Fin 2 → ℝ) := Icc 0 1
  let f : (Fin 2 → ℝ) → ℂ := fun x => 3*eisensteinRealCoords x
  refine ⟨f '' Q,isCompact_Icc.image (continuous_const.mul eisensteinRealCoords.continuous),?_⟩
  intro z hz
  refine ⟨cubicThetaPeriodCoordinates z,?_,?_⟩
  · exact ⟨fun i => (hz i).1,fun i => (hz i).2.le⟩
  · dsimp only [f,cubicThetaPeriodCoordinates]
    rw [ContinuousLinearEquiv.apply_symm_apply]
    ring

lemma cubicThetaHorizontalCell_measure_ne_top : volume cubicThetaHorizontalCell≠⊤ := by
  obtain ⟨K,hK,hsub⟩ := cubicThetaHorizontalCell_compact_container
  exact (lt_of_le_of_lt (measure_mono hsub) hK.measure_lt_top).ne

lemma cubicThetaHorizontalCell_normSq_bound :
    ∃ R : ℝ, 0≤R ∧ ∀ z∈cubicThetaHorizontalCell, Complex.normSq z≤R := by
  obtain ⟨K,hK,hsub⟩ := cubicThetaHorizontalCell_compact_container
  obtain ⟨R,hR⟩ := hK.exists_bound_of_continuousOn Complex.continuous_normSq.continuousOn
  refine ⟨max 0 R,le_max_left _ _,fun z hz => ?_⟩
  exact ((le_abs_self _).trans (hR z (hsub hz))).trans (le_max_right _ _)

end CubicFirstMoment

end

end OAI
