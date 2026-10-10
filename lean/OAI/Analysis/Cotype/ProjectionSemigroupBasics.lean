import OAI.Analysis.Cotype.ProjectionSemigroup

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem projectionSemigroup_factor_contracts (P : Y →L[ℝ] Y)
    (hP : ∀ y, ‖P y‖ ≤ ‖y‖) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (y : Y) :
    ‖(P + r • (1-P)) y‖ ≤ ‖y‖ := by
  have he : P + r • (1-P) = (1-r) • P + r • (1 : Y →L[ℝ] Y) := by module
  rw [he]
  change ‖(1-r) • P y + r • y‖ ≤ ‖y‖
  calc
    _ ≤ ‖(1-r) • P y‖ + ‖r • y‖ := norm_add_le _ _
    _ = (1-r)*‖P y‖ + r*‖y‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr hr1), abs_of_nonneg hr]
    _ ≤ (1-r)*‖y‖ + r*‖y‖ := by gcongr; exact hP y
    _ = ‖y‖ := by ring

theorem projectionSemigroup_contracts {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hP : ∀ i y, ‖P i y‖ ≤ ‖y‖) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (y : Y) :
    ‖projectionSemigroup P r y‖ ≤ ‖y‖ :=
  projectionProduct_norm_apply _ (fun i => projectionSemigroup_factor_contracts (P i) (hP i) hr hr1) y

@[simp] theorem projectionSemigroup_zero {m : ℕ} (P : Fin m → Y →L[ℝ] Y) :
    projectionSemigroup P 0 = projectionProduct P := by
  simp [projectionSemigroup]

@[simp] theorem projectionSemigroup_one {m : ℕ} (P : Fin m → Y →L[ℝ] Y) :
    projectionSemigroup P 1 = 1 := by
  simp [projectionSemigroup, projectionProduct_one]

theorem projectionSemigroup_factor_mul (P : Y →L[ℝ] Y)
    (hP : P * P = P) (r s : ℝ) :
    (P + r • (1-P)) * (P + s • (1-P)) = P + (r*s) • (1-P) := by
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub,
    one_mul, mul_one, hP, sub_self, smul_zero, add_zero]
  module

theorem projectionSemigroup_factor_commute (P Q : Y →L[ℝ] Y)
    (h : Commute P Q) (r s : ℝ) :
    Commute (P + r • (1-P)) (Q + s • (1-Q)) := by
  have h1 : Commute P (1-Q) := (Commute.one_right P).sub_right h
  have h2 : Commute (1-P) Q := (Commute.one_left Q).sub_left h
  have h3 : Commute (1-P) (1-Q) := (Commute.one_right _).sub_right h2
  exact (h.add_right (h1.smul_right s)).add_left
    ((h2.add_right (h3.smul_right s)).smul_left r)

theorem projectionSemigroup_mul {m : ℕ} (P : Fin m → Y →L[ℝ] Y)
    (hp : ∀ i, P i * P i = P i) (hc : ∀ i j, Commute (P i) (P j)) (r s : ℝ) :
    projectionSemigroup P r * projectionSemigroup P s = projectionSemigroup P (r*s) := by
  induction m with
  | zero => simp [projectionSemigroup, projectionProduct]
  | succ m ih =>
    have ht := ih (fun i => P i.succ) (fun i => hp i.succ)
      (fun i j => hc i.succ j.succ)
    have hm := projectionProduct_commute
      (fun i : Fin m => P i.succ + r • (1-P i.succ))
      (P 0 + s • (1-P 0))
      (fun i => projectionSemigroup_factor_commute _ _ (hc i.succ 0) r s)
    change Commute (projectionSemigroup (fun i => P i.succ) r)
      (P 0 + s • (1-P 0)) at hm
    change ((P 0 + r • (1-P 0)) * projectionSemigroup (fun i => P i.succ) r) *
        ((P 0 + s • (1-P 0)) * projectionSemigroup (fun i => P i.succ) s) =
      (P 0 + (r*s) • (1-P 0)) * projectionSemigroup (fun i => P i.succ) (r*s)
    rw [mul_assoc, ← mul_assoc (projectionSemigroup _ r), hm.eq,
      mul_assoc, ht, ← mul_assoc, projectionSemigroup_factor_mul _ (hp 0)]

end Cotype

end

end OAI
