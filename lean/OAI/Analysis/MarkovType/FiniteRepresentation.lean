import OAI.Analysis.MarkovType.DenseFiniteApproximation
import OAI.Analysis.MarkovType.FiniteCoordinateSupport
import OAI.Analysis.MarkovType.FinitelyRepresentable
import OAI.Analysis.MarkovType.NormedC00
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Tactic.Linarith

namespace OAI

namespace MarkovSuperreflexivity

theorem finitelyRepresentable_completion_of_coordinates
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (p : Seminorm ℝ C00) (hp : ∀ a, p a = 0 → a = 0)
    (hcoord : ∀ (m : ℕ) (ε : ℝ), 0 < ε →
      ∃ T : (Fin m → ℝ) →ₗ[ℝ] X, ∀ a,
        p (C00.ofArray a) ≤ ‖T a‖ ∧
        ‖T a‖ ≤ (1 + ε) * p (C00.ofArray a)) :
    FinitelyRepresentable (UniformSpace.Completion (NormedC00 p hp)) X := by
  intro V hV η hη
  let δ : ℝ := min (η / 8) (1 / 2)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδhalf : δ ≤ 1 / 2 := min_le_right _ _
  have hδη : δ ≤ η / 8 := min_le_left _ _
  have hden : 0 < 1 - δ := by linarith
  have hinv : 0 < (1 - δ)⁻¹ := inv_pos.mpr hden
  have hraw : (1 + δ) * (1 + δ) ≤ (1 + η) * (1 - δ) := by
    have hsquare : δ * δ ≤ δ := by
      have := mul_le_mul_of_nonneg_left (show δ ≤ 1 by linarith) hδ.le
      nlinarith
    have hηδ := mul_le_mul_of_nonneg_left hδhalf hη.le
    nlinarith
  have hfactor : (1 - δ)⁻¹ * ((1 + δ) * (1 + δ)) ≤ 1 + η := by
    have h := (div_le_iff₀ hden).mpr hraw
    simpa only [div_eq_mul_inv, mul_comm] using h
  let ι : NormedC00 p hp →ₗᵢ[ℝ] UniformSpace.Completion (NormedC00 p hp) :=
    UniformSpace.Completion.toComplₗᵢ
  have hdense : DenseRange ι := UniformSpace.Completion.denseRange_coe
  obtain ⟨S, hS⟩ := exists_linearMap_approx_subtype ι hdense V δ hδ
  have hSnorm (z : V) :
      (1 - δ) * ‖z‖ ≤ ‖S z‖ ∧ ‖S z‖ ≤ (1 + δ) * ‖z‖ := by
    have habs : |‖S z‖ - ‖z‖| ≤ δ * ‖z‖ := by
      simpa only [ι.norm_map, Submodule.norm_coe] using
        (abs_norm_sub_norm_le (ι (S z))
          (z : UniformSpace.Completion (NormedC00 p hp))).trans (hS z)
    obtain ⟨hl, hu⟩ := abs_le.mp habs
    constructor <;> nlinarith
  obtain ⟨m, R, hR⟩ := finite_coordinate_factorization
    ((NormedC00.coefficients p hp).toLinearMap.comp S)
  have hRnorm (z : V) : p (C00.ofArray (R z)) = ‖S z‖ := by
    rw [hR z]
    rfl
  obtain ⟨T, hT⟩ := hcoord m δ hδ
  let U : V →ₗ[ℝ] X := T.comp R
  have hUnorm (z : V) : (1 - δ) * ‖z‖ ≤ ‖U z‖ ∧
      ‖U z‖ ≤ ((1 + δ) * (1 + δ)) * ‖z‖ := by
    constructor
    · calc
        (1 - δ) * ‖z‖ ≤ ‖S z‖ := (hSnorm z).1
        _ = p (C00.ofArray (R z)) := (hRnorm z).symm
        _ ≤ ‖U z‖ := (hT (R z)).1
    · calc
        ‖U z‖ ≤ (1 + δ) * p (C00.ofArray (R z)) := (hT (R z)).2
        _ = (1 + δ) * ‖S z‖ := by rw [hRnorm z]
        _ ≤ (1 + δ) * ((1 + δ) * ‖z‖) :=
          mul_le_mul_of_nonneg_left (hSnorm z).2 (by linarith)
        _ = ((1 + δ) * (1 + δ)) * ‖z‖ := (mul_assoc _ _ _).symm
  refine ⟨(1 - δ)⁻¹ • U, ?_⟩
  intro z
  have hscaled : ‖((1 - δ)⁻¹ • U) z‖ = (1 - δ)⁻¹ * ‖U z‖ := by
    simp only [LinearMap.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hinv]
  constructor
  · rw [hscaled]
    calc
      ‖z‖ = (1 - δ)⁻¹ * ((1 - δ) * ‖z‖) := by
        rw [← mul_assoc, inv_mul_cancel₀ hden.ne', one_mul]
      _ ≤ (1 - δ)⁻¹ * ‖U z‖ :=
        mul_le_mul_of_nonneg_left (hUnorm z).1 hinv.le
  · rw [hscaled]
    calc
      (1 - δ)⁻¹ * ‖U z‖ ≤ (1 - δ)⁻¹ * (((1 + δ) * (1 + δ)) * ‖z‖) :=
        mul_le_mul_of_nonneg_left (hUnorm z).2 hinv.le
      _ = ((1 - δ)⁻¹ * ((1 + δ) * (1 + δ))) * ‖z‖ :=
        (mul_assoc _ _ _).symm
      _ ≤ (1 + η) * ‖z‖ := mul_le_mul_of_nonneg_right hfactor (norm_nonneg z)

end MarkovSuperreflexivity

end OAI
