import Mathlib
import OAI.Analysis.Conductivity.Variational.ProductFactorSpec

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace ScalarConductivity
open Filter Topology

def recoverJoinChild (i : Fin 3) (θ : ℝ) (β δ : DiagonalTriple) : DiagonalTriple :=
  fun j => if j = i then θ / ((δ j)⁻¹ - (1 - θ) / β j)
    else (δ j - (1 - θ) * β j) / θ

lemma div_self_div_eq (θ t : ℝ) (hθ : θ ≠ 0) : θ / (θ / t) = t := by
  by_cases ht : t = 0
  · simp [ht]
  · field_simp

lemma recoverJoinChild_join (i : Fin 3) {θ : ℝ} (hθ : θ ≠ 0)
    (α β : DiagonalTriple) : recoverJoinChild i θ β (coordinateJoin i θ α β) = α := by
  ext j
  by_cases hj : j = i
  · simp only [recoverJoinChild, coordinateJoin, hj, ite_true, inv_inv, add_sub_cancel_right]
    exact div_self_div_eq _ _ hθ
  · simp only [recoverJoinChild, coordinateJoin, hj, ite_false, add_sub_cancel_right]
    exact mul_div_cancel_left₀ _ hθ

lemma coordinateJoin_recoverJoinChild (i : Fin 3) {θ : ℝ} (hθ : θ ≠ 0)
    (β δ : DiagonalTriple) : coordinateJoin i θ (recoverJoinChild i θ β δ) β = δ := by
  ext j
  by_cases hj : j = i
  · simp only [recoverJoinChild, coordinateJoin, hj, ite_true]
    rw [div_self_div_eq _ _ hθ, sub_add_cancel, inv_inv]
  · simp only [recoverJoinChild, coordinateJoin, hj, ite_false]
    rw [mul_div_cancel₀ _ hθ, sub_add_cancel]

lemma continuousAt_recoverJoinChild (i : Fin 3) {θ : ℝ} (hθ : θ ≠ 0)
    (α β : DiagonalTriple) (hα : α i ≠ 0)
    (hjoin : coordinateJoin i θ α β i ≠ 0) :
    ContinuousAt (recoverJoinChild i θ β) (coordinateJoin i θ α β) := by
  apply continuousAt_pi.mpr
  intro j
  by_cases hj : j = i
  · subst j
    simp only [recoverJoinChild, ite_true]
    apply continuousAt_const.div
    · exact ((continuous_apply i).continuousAt.inv₀ hjoin).sub continuousAt_const
    · simp only [coordinateJoin, ite_true, inv_inv, add_sub_cancel_right]
      exact div_ne_zero hθ hα
  · simp only [recoverJoinChild, ite_eq_right hj]
    have hc : Continuous (fun δ : DiagonalTriple => δ j) := continuous_apply j
    exact (hc.continuousAt.sub continuousAt_const).div continuousAt_const hθ

lemma coordinateJoin_zero (i : Fin 3) (α β : DiagonalTriple) : coordinateJoin i 0 α β = β := by
  ext j
  simp [coordinateJoin]

lemma coordinateJoin_one (i : Fin 3) (α β : DiagonalTriple) : coordinateJoin i 1 α β = α := by
  ext j
  simp [coordinateJoin]

theorem isOpen_finiteLaminate {a b : ℝ} (ha : 0 < a) :
    IsOpen {α : DiagonalTriple | IsFiniteLaminate a b α} := by
  apply isOpen_iff_mem_nhds.mpr
  intro α hα
  induction hα with
  | scalar s has hsb =>
    exact mem_interior_iff_mem_nhds.mp (scalar_mem_interior_finiteLaminate ha has hsb)
  | @join i θ hθ₀ hθ₁ α β hα hβ ihα ihβ =>
    by_cases hθ : θ = 0
    · simpa [hθ, coordinateJoin_zero] using ihβ
    · let δ := coordinateJoin i θ α β
      have hαi : α i ≠ 0 := (ha.trans (hα.bounds ha i).1).ne'
      have hδi : δ i ≠ 0 :=
        (ha.trans (coordinateJoin_bounds ha (hα.bounds ha) (hβ.bounds ha) i ⟨hθ₀, hθ₁⟩ i).1).ne'
      have hc := continuousAt_recoverJoinChild i hθ α β hαi hδi
      have he : recoverJoinChild i θ β δ = α := recoverJoinChild_join i hθ α β
      have hm : ∀ᶠ δ' in 𝓝 δ, IsFiniteLaminate a b (recoverJoinChild i θ β δ') :=
        hc.preimage_mem_nhds (by rw [he]; exact ihα)
      filter_upwards [hm] with δ' hδ'
      have hj := IsFiniteLaminate.join i θ hθ₀ hθ₁ hδ' hβ
      simpa only [coordinateJoin_recoverJoinChild i hθ β δ'] using hj

lemma IsFiniteLaminate.permute {a b : ℝ} {α : DiagonalTriple}
    (h : IsFiniteLaminate a b α) (e : Equiv.Perm (Fin 3)) :
    IsFiniteLaminate a b (α ∘ e) := by
  induction h with
  | scalar s has hsb => exact .scalar s has hsb
  | @join i θ hθ₀ hθ₁ α β hα hβ ihα ihβ =>
    convert IsFiniteLaminate.join (e.symm i) θ hθ₀ hθ₁ ihα ihβ using 1
    ext j
    simp only [Function.comp_apply, coordinateJoin]
    congr 1
    exact propext ⟨fun h => by simpa using congrArg e.symm h,
      fun h => by simpa using congrArg e h⟩

end ScalarConductivity

end

end OAI
