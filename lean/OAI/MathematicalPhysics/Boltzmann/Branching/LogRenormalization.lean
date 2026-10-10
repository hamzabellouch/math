import OAI.MathematicalPhysics.Boltzmann.Compactness.RenormalizedIntegrability

namespace OAI

/-! # The logarithmic renormalization and its positive derivative -/
noncomputable section
open Set
namespace BoltzmannNonuniqueness.Renormalization

theorem logOneAdd_hasDerivAt {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (fun x : ℝ => Real.log (1+x)) (1/(1+z)) z := by
  convert ((hasDerivAt_id z).const_add 1).log (show (1+z:ℝ) ≠ 0 by positivity) using 1 <;> simp

theorem logOneAdd_derivWithin {z : ℝ} (hz : 0 ≤ z) :
    derivWithin (fun x : ℝ => Real.log (1+x)) (Ici 0) z = 1/(1+z) :=
  (logOneAdd_hasDerivAt hz).hasDerivWithinAt.derivWithin (uniqueDiffOn_Ici (0:ℝ) z hz)

def logarithm : Renormalization where
  toFun := fun x => Real.log (1+x)
  regular := (contDiffOn_const.add contDiffOn_id).log (fun x hx => by have : 0 ≤ x := hx; positivity)
  at_zero := by simp
  derivative_bound := ⟨1,zero_le_one,fun z hz => by
    have hz' : 0 ≤ z := hz
    rw [logOneAdd_derivWithin hz,abs_of_nonneg (by positivity)]⟩

theorem weighted_log_le_self {m u : ℝ} (hm : 0 < m) (hu : 0 ≤ u) :
    m*Real.log (1+u/m) ≤ u := by
  have h := Real.log_le_sub_one_of_pos (show 0 < 1+u/m by positivity)
  calc
    _ ≤ m*((1+u/m)-1) := mul_le_mul_of_nonneg_left h hm.le
    _ = u := by
      field_simp
      ring

end BoltzmannNonuniqueness.Renormalization

end

end OAI
