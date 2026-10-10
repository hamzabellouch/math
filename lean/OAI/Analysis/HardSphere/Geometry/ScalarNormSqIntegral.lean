import Mathlib
import OAI.Analysis.HardSphere.Cutoffs.Regularize

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
open scoped RealInnerProductSpace
namespace HardSphere

lemma scalar_norm_sq_integral {N : ℕ} {L : Length} (u : ScalarL2 N L) :
    ‖u‖^2 = ∫ X, ‖u X‖^2 := by
  rw [← real_inner_self_eq_norm_sq (F := ScalarL2 N L), L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

lemma ae_norm_eq_of_L2_norm_eq {N : ℕ} {L : Length} (u v : ScalarL2 N L)
    (hle : ∀ᵐ X ∂volume, ‖u X‖ ≤ ‖v X‖) (he : ‖u‖ = ‖v‖) :
    ∀ᵐ X ∂volume, ‖u X‖ = ‖v X‖ := by
  have hiu := (Lp.memLp u).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hiv := (Lp.memLp v).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hp : ∀ᵐ X ∂volume, 0 ≤ ‖v X‖^2 - ‖u X‖^2 :=
    hle.mono fun X hX ↦ sub_nonneg.mpr (pow_le_pow_left₀ (norm_nonneg _) hX 2)
  have hz : (∫ X, ‖v X‖^2 - ‖u X‖^2) = 0 := by
    rw [integral_sub hiv hiu, ← scalar_norm_sq_integral, ← scalar_norm_sq_integral, he, sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg_ae hp (hiv.sub hiu)).mp hz
  filter_upwards [hae] with X hX
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ((sub_eq_zero.mp hX).symm)

lemma norm_modulusPartial_le {N : ℕ} {L : Length} (u v : ScalarL2 N L) :
    ‖modulusPartial u v‖ ≤ ‖v‖ :=
  L2Contraction.norm_fieldApply_le _ (modulusCoefficient_meas u)
    (Eventually.of_forall fun X ↦ ComplexRegularization.differential_le 0 (u X)) v

lemma IsGroundVector.norm_modulusPartial {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : IsGroundVector N L a u) (p : Direction N) :
    ‖modulusPartial u.1 (u.2 p)‖ = ‖u.2 p‖ := by
  have he := hu.energy_modulus
  have hle : ∀ p ∈ (Finset.univ : Finset (Direction N)),
      ‖modulusPartial u.1 (u.2 p)‖^2 ≤ ‖u.2 p‖^2 :=
    fun p _ ↦ pow_le_pow_left₀ (norm_nonneg _) (norm_modulusPartial_le _ _) 2
  have h := (Finset.sum_eq_sum_iff_of_le hle).mp he p (Finset.mem_univ _)
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

lemma IsGroundVector.ae_norm_modulusPartial {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : IsGroundVector N L a u) (p : Direction N) :
    ∀ᵐ X ∂volume, ‖ComplexRegularization.differential 0 (u.1 X) (u.2 p X)‖ = ‖u.2 p X‖ := by
  have hle : ∀ᵐ X ∂volume, ‖modulusPartial u.1 (u.2 p) X‖ ≤ ‖u.2 p X‖ := by
    filter_upwards [coe_modulusPartial u.1 (u.2 p)] with X hX
    rw [hX]
    exact ComplexRegularization.differential_apply_le _ _ _
  have he := ae_norm_eq_of_L2_norm_eq _ _ hle (hu.norm_modulusPartial p)
  filter_upwards [he, coe_modulusPartial u.1 (u.2 p)] with X h1 h2
  rwa [h2] at h1

end HardSphere

end
end
end

end OAI
