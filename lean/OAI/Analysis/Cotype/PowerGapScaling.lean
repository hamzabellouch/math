import OAI.Analysis.Cotype.PowerGapInverse
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
namespace Cotype

theorem exists_powerGapScale {N : ℕ} {C : ℝ} (hC2 : C < (2 : ℝ)^N) :
    ∃ β : ℝ, 1 < β ∧ β < 2 ∧ C < β^N := by
  have hpow : ∀ᶠ x : ℝ in 𝓝 (2 : ℝ), C < x^N :=
    (continuous_pow N).continuousAt.eventually (lt_mem_nhds hC2)
  have hone : ∀ᶠ x : ℝ in 𝓝 (2 : ℝ), 1 < x := lt_mem_nhds (by norm_num)
  have h : ∀ᶠ x : ℝ in 𝓝[<] (2 : ℝ), (1 < x ∧ C < x^N) ∧ x < 2 :=
    ((hone.and hpow).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨β, ⟨hβ1, hβN⟩, hβ2⟩ := h.exists
  exact ⟨β, hβ1, hβ2, hβN⟩

theorem exists_scaled_powerGapInverse {N : ℕ} {C β : ℝ}
    (hβ : 0 < β) (hgap : C < β^N)
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormOneClass A] [CompleteSpace A]
    (T : A) (hT : ‖T‖ ≤ 1) (hTN : ‖(1-T)^N‖ ≤ C) :
    ∃ U : Aˣ, (U : A) = (β-1) • (1 : A) + T ∧
      ‖(↑U⁻¹ : A)‖ ≤ powerGapInverseBound N (2/β) (C/β^N) / β := by
  let H : A := β⁻¹ • (1-T)
  have hb : 0 ≤ 2/β := by positivity
  have hq : C/β^N < 1 := (div_lt_one (pow_pos hβ N)).mpr hgap
  have hH : ‖H‖ ≤ 2/β := by
    dsimp [H]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hβ)]
    calc
      _ ≤ β⁻¹ * (‖(1 : A)‖ + ‖T‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr hβ.le)
      _ ≤ β⁻¹ * (1+1) := by rw [norm_one]; gcongr
      _ = 2/β := by ring
  have hHN : ‖H^N‖ ≤ C/β^N := by
    dsimp [H]
    rw [smul_pow, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hβ.le) N)]
    calc
      _ ≤ (β⁻¹)^N * C := mul_le_mul_of_nonneg_left hTN (by positivity)
      _ = C/β^N := by rw [inv_pow, div_eq_mul_inv, mul_comm]
  obtain ⟨V, hV, hnormV⟩ := exists_powerGapInverse hb hq H hH hHN
  have hv1 : (V : A)*(↑V⁻¹ : A) = 1 := V.val_inv
  have hv2 : (↑V⁻¹ : A)*(V : A) = 1 := V.inv_val
  let U : Aˣ :=
    ⟨β • (V : A), β⁻¹ • (↑V⁻¹ : A), by
      rw [smul_mul_assoc, mul_smul_comm, hv1, smul_smul,
        mul_inv_cancel₀ hβ.ne', one_smul], by
      rw [smul_mul_assoc, mul_smul_comm, hv2, smul_smul,
        inv_mul_cancel₀ hβ.ne', one_smul]⟩
  refine ⟨U, ?_, ?_⟩
  · change β • (V : A) = _
    rw [hV]
    dsimp [H]
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hβ.ne', one_smul]
    module
  · change ‖β⁻¹ • (↑V⁻¹ : A)‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hβ)]
    exact (mul_le_mul_of_nonneg_left hnormV (inv_nonneg.mpr hβ.le)).trans_eq
      (by simp only [div_eq_mul_inv]; ring)

end Cotype

end

end OAI
