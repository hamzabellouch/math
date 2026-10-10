import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumAncilla

namespace OAI

/-! Coordinate projections for the initial and output penalties. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaMask {n : ℕ} (p : SourceSpinBasis n → Prop) :
    EuclideanSpace ℂ (SourceSpinBasis n) →ₗ[ℂ] EuclideanSpace ℂ (SourceSpinBasis n) := by
  classical
  exact {
    toFun := fun u => WithLp.toLp 2 (fun s => if p s then u s else 0)
    map_add' := by intro u v; ext s; by_cases hs : p s <;> simp [hs]
    map_smul' := by intro a u; ext s; by_cases hs : p s <;> simp [hs] }

@[simp] theorem qmaMask_apply {n : ℕ} (p : SourceSpinBasis n → Prop)
    (u : EuclideanSpace ℂ (SourceSpinBasis n)) (s : SourceSpinBasis n) :
    qmaMask p u s = if p s then u s else 0 := rfl

theorem qmaMask_norm_le {n : ℕ} (p : SourceSpinBasis n → Prop)
    (u : EuclideanSpace ℂ (SourceSpinBasis n)) : ‖qmaMask p u‖ ≤ ‖u‖ := by
  classical
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro s _
  by_cases hs : p s <;> simp [qmaMask_apply,hs]

theorem qmaMask_complement_square {n : ℕ} (p : SourceSpinBasis n → Prop)
    (u : EuclideanSpace ℂ (SourceSpinBasis n)) :
    ‖qmaMask p u‖^2+‖qmaMask (fun s => ¬p s) u‖^2 = ‖u‖^2 := by
  classical
  simp only [EuclideanSpace.norm_sq_eq,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : p s <;> simp [hs]

theorem qmaMask_sub_norm_le {n : ℕ} (p : SourceSpinBasis n → Prop)
    (u v : EuclideanSpace ℂ (SourceSpinBasis n)) :
    ‖qmaMask p u-qmaMask p v‖ ≤ ‖u-v‖ := by
  rw [←map_sub]
  exact qmaMask_norm_le p (u-v)

theorem qmaMask_square_difference {n : ℕ} (p : SourceSpinBasis n → Prop)
    (u v : EuclideanSpace ℂ (SourceSpinBasis n)) :
    |‖qmaMask p u‖^2-‖qmaMask p v‖^2| ≤ (‖u‖+‖v‖)*‖u-v‖ := by
  rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  have ha := (abs_norm_sub_norm_le (qmaMask p u) (qmaMask p v)).trans (qmaMask_sub_norm_le p u v)
  have hb := add_le_add (qmaMask_norm_le p u) (qmaMask_norm_le p v)
  exact mul_le_mul hb ha (abs_nonneg _) (by positivity)

theorem qmaMask_sub_self {n : ℕ} (p : SourceSpinBasis n → Prop)
    (u : EuclideanSpace ℂ (SourceSpinBasis n)) :
    u-qmaMask p u = qmaMask (fun s => ¬p s) u := by
  ext s
  by_cases hs : p s <;> simp [hs]

end ContinuumCoulomb

end

end OAI
