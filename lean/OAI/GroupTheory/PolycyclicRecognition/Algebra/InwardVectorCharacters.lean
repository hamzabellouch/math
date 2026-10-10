import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactCharacterCertificates
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NegativeRayDescent
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.InnerProductSpace.Continuous

namespace OAI

/-! # Characters opposite a ray residual -/

noncomputable section
namespace PolycyclicRecognition
open scoped InnerProductSpace
variable {Q E : Type} [CommGroup Q] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def inwardVectorCharacter (e : Q →* Multiplicative E) (v : E) :
    Q →* Multiplicative ℝ where
  toFun q := Multiplicative.ofAdd (-⟪v, (e q).toAdd⟫_ℝ)
  map_one' := by simp
  map_mul' q r := by simp [inner_add_right, mul_comm]

theorem inwardVectorCharacter_continuous (e : Q →* Multiplicative E) (q : Q) :
    Continuous (fun v : E => (inwardVectorCharacter e v q).toAdd) := by
  change Continuous (fun v : E => -⟪v, (e q).toAdd⟫_ℝ)
  exact (continuous_id.inner continuous_const).neg

theorem inwardVectorCharacter_exists_positive (e : Q →* Multiplicative E)
    (hspan : Submodule.span ℝ (Set.range (fun q => (e q).toAdd)) = ⊤)
    (v : E) (hv : v ≠ 0) : ∃ q, 0 < (inwardVectorCharacter e v q).toAdd := by
  by_contra h
  have hnonneg (q : Q) : 0 ≤ ⟪v, (e q).toAdd⟫_ℝ := by
    have hq : ¬0 < -⟪v, (e q).toAdd⟫_ℝ := fun hq => h ⟨q, hq⟩
    linarith
  have hzero (q : Q) : ⟪v, (e q).toAdd⟫_ℝ = 0 := by
    have hi := hnonneg q⁻¹
    simp only [map_inv, toAdd_inv, inner_neg_right] at hi
    exact le_antisymm (by linarith) (hnonneg q)
  have hall : ∀ x ∈ Submodule.span ℝ (Set.range (fun q => (e q).toAdd)),
      ⟪v, x⟫_ℝ = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨q, rfl⟩ := hx; exact hzero q
    | zero => simp
    | add x y _ _ hx hy => simp only [inner_add_right, hx, hy, add_zero]
    | smul r x _ hx => simp only [real_inner_smul_right, hx, mul_zero]
  exact hv (inner_self_eq_zero.mp (hall v (hspan ▸ Submodule.mem_top)))

def inwardRayHemisphere (t : E) : Set E := {v | ‖v‖ = 1 ∧ 0 ≤ ⟪v, t⟫_ℝ}

theorem inwardRayHemisphere_compact [ProperSpace E] (t : E) :
    IsCompact (inwardRayHemisphere t) := by
  have hs : IsCompact {v : E | ‖v‖ = 1} := by
    simpa only [Metric.sphere, dist_zero_right] using (isCompact_sphere (0 : E) 1)
  have hi : Continuous (fun v : E => ⟪v, t⟫_ℝ) := continuous_id.inner continuous_const
  have hc : IsClosed {v : E | 0 ≤ ⟪v, t⟫_ℝ} := isClosed_le continuous_const hi
  exact hs.inter_right hc

theorem normalized_residual_mem_inwardRayHemisphere (t q : E)
    (hv : negativeRayResidual t q ≠ 0) :
    ‖negativeRayResidual t q‖⁻¹ • negativeRayResidual t q ∈ inwardRayHemisphere t := by
  have hp := norm_pos_iff.mpr hv
  constructor
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ (ne_of_gt hp)]
  · rw [real_inner_smul_left]
    exact mul_nonneg (inv_nonneg.mpr hp.le) (negativeRayResidual_inner_nonneg t q)

end PolycyclicRecognition

end

end OAI
