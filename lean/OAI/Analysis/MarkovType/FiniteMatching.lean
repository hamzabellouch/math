import OAI.Analysis.MarkovType.FiniteGoldstine
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

universe u v

variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

private theorem exists_continuous_range_section
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (T : Y →ₗ[ℝ] F) :
    ∃ S : LinearMap.range T →L[ℝ] Y,
      ∀ z : LinearMap.range T, T (S z) = (z : F) := by
  classical
  let R : Submodule ℝ F := LinearMap.range T
  let b := Module.finBasis ℝ R
  let y : Fin (Module.finrank ℝ R) → Y := fun i => Classical.choose (b i).property
  have hy (i : Fin (Module.finrank ℝ R)) : T (y i) = (b i : F) :=
    Classical.choose_spec (b i).property
  let S₀ : R →ₗ[ℝ] Y := b.constr ℝ y
  have hcomp : T.comp S₀ = R.subtype := by
    apply b.ext
    intro i
    change T (S₀ (b i)) = (b i : F)
    rw [show S₀ (b i) = y i from b.constr_basis ℝ y i]
    exact hy i
  let S : R →L[ℝ] Y := ⟨S₀, S₀.continuous_of_finiteDimensional⟩
  refine ⟨S, ?_⟩
  intro z
  exact congrArg (fun L : R →ₗ[ℝ] F => L z) hcomp

theorem finite_matching_unit
    (v : StrongDual ℝ (StrongDual ℝ Y)) (hv : ‖v‖ ≤ 1)
    {m : ℕ} (f : Fin m → (Y →L[ℝ] ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y : Y, ‖y‖ ≤ 1 + ε ∧ ∀ i, f i y = v (f i) := by
  classical
  let T : Y →ₗ[ℝ] (Fin m → ℝ) :=
    { toFun := fun y i => f i y
      map_add' := by
        intro y z
        funext i
        exact (f i).map_add y z
      map_smul' := by
        intro c y
        funext i
        exact (f i).map_smul c y }
  let a : Fin m → ℝ := fun i => v (f i)
  let R : Submodule ℝ (Fin m → ℝ) := LinearMap.range T
  have hclosed : IsClosed (R : Set (Fin m → ℝ)) := R.closed_of_finiteDimensional
  have ha : a ∈ R := by
    change a ∈ (R : Set (Fin m → ℝ))
    rw [← hclosed.closure_eq]
    apply Metric.mem_closure_iff.mpr
    intro δ hδ
    obtain ⟨y, _, hy⟩ := finite_goldstine v hv f hδ
    refine ⟨T y, ⟨y, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    apply (pi_norm_lt_iff hδ).mpr
    intro i
    change ‖a i - (T y) i‖ < δ
    rw [Real.norm_eq_abs]
    change |v (f i) - f i y| < δ
    rw [abs_sub_comm]
    exact hy i
  obtain ⟨S, hS⟩ := exists_continuous_range_section T
  have hSpos : 0 < ‖S‖ + 1 := by linarith [norm_nonneg S]
  let δ : ℝ := ε / (‖S‖ + 1)
  have hδ : 0 < δ := div_pos hε hSpos
  obtain ⟨y, hy, hfy⟩ := finite_goldstine v hv f hδ
  let e : R := ⟨a - T y, R.sub_mem ha ⟨y, rfl⟩⟩
  have he : ‖e‖ < δ := by
    change ‖a - T y‖ < δ
    apply (pi_norm_lt_iff hδ).mpr
    intro i
    change ‖a i - (T y) i‖ < δ
    rw [Real.norm_eq_abs]
    change |v (f i) - f i y| < δ
    rw [abs_sub_comm]
    exact hfy i
  have hcorrection : ‖S e‖ ≤ ε := by
    calc
      ‖S e‖ ≤ ‖S‖ * ‖e‖ := S.le_opNorm e
      _ ≤ ‖S‖ * δ := mul_le_mul_of_nonneg_left he.le (norm_nonneg S)
      _ ≤ (‖S‖ + 1) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = δ * (‖S‖ + 1) := mul_comm _ _
      _ = ε := div_mul_cancel₀ ε (ne_of_gt hSpos)
  refine ⟨y + S e, (norm_add_le _ _).trans (add_le_add hy hcorrection), ?_⟩
  intro i
  have heval : T (y + S e) = a := by
    rw [map_add, hS e]
    change T y + (a - T y) = a
    rw [add_comm, sub_add_cancel]
  exact congrFun heval i

theorem finite_matching
    (v : StrongDual ℝ (StrongDual ℝ Y))
    {m : ℕ} (f : Fin m → (Y →L[ℝ] ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y : Y, ‖y‖ ≤ (1 + ε) * ‖v‖ ∧ ∀ i, f i y = v (f i) := by
  by_cases hv0 : v = 0
  · subst v
    refine ⟨0, ?_, fun i => by simp⟩
    calc
      ‖(0 : Y)‖ = 0 := norm_zero
      _ ≤ (1 + ε) * ‖(0 : StrongDual ℝ (StrongDual ℝ Y))‖ :=
        mul_nonneg (by linarith) (ContinuousLinearMap.opNorm_nonneg _)
  have hvpos : 0 < ‖v‖ := (norm_pos_iff (a := v)).mpr hv0
  let v' : StrongDual ℝ (StrongDual ℝ Y) := ‖v‖⁻¹ • v
  have hv' : ‖v'‖ ≤ 1 := by
    calc
      ‖v'‖ ≤ ‖‖v‖⁻¹‖ * ‖v‖ := ContinuousLinearMap.opNorm_smul_le _ _
      _ = 1 := by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvpos),
          inv_mul_cancel₀ (ne_of_gt hvpos)]
  obtain ⟨y, hy, hfy⟩ := finite_matching_unit v' hv' f hε
  refine ⟨‖v‖ • y, ?_, ?_⟩
  · calc
      ‖‖v‖ • y‖ = ‖v‖ * ‖y‖ :=
        (norm_smul ‖v‖ y).trans
          (congrArg (fun t : ℝ => t * ‖y‖) (Real.norm_of_nonneg (norm_nonneg v)))
      _ ≤ ‖v‖ * (1 + ε) := mul_le_mul_of_nonneg_left hy (norm_nonneg v)
      _ = (1 + ε) * ‖v‖ := mul_comm _ _
  · intro i
    rw [(f i).map_smul, hfy i]
    change ‖v‖ * (‖v‖⁻¹ * v (f i)) = v (f i)
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hvpos), one_mul]

end MarkovSuperreflexivity

end

end OAI
