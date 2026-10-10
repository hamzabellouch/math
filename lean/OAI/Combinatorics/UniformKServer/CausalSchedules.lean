import Mathlib
import OAI.Combinatorics.UniformKServer.EpochAlphaSchedule

namespace OAI

                                      
section

/-! Prefix extensionality of the concrete epoch recurrences. This supplies
filtration measurability without making future parameters available early. -/
noncomputable section
namespace UniformKServer.CausalSchedules
variable {ι : Type*} [Fintype ι]

theorem active_congr (c δ : ℝ) {x y : ℕ → ℝ} (t : ℕ)
    (h : ∀ s, s ≤ t → x s=y s) :
    AllocationSchedule.schedule c δ x t=AllocationSchedule.schedule c δ y t := by
  induction t with
  | zero => simp only [AllocationSchedule.schedule,h 0 le_rfl]
  | succ t ih =>
    simp only [AllocationSchedule.schedule,ih (fun s hs => h s (by omega)),h (t+1) le_rfl]

theorem held_congr (δ : ℝ) {x y : ℕ → ℝ} (t : ℕ)
    (h : ∀ s, s ≤ t → x s=y s) :
    AllocationSchedule.held δ x t=AllocationSchedule.held δ y t := by
  induction t with
  | zero => exact h 0 le_rfl
  | succ t ih =>
    simp only [AllocationSchedule.held,ih (fun s hs => h s (by omega)),h (t+1) le_rfl]

theorem forced_congr (δ : ℝ) {x y : ℕ → ℝ} {p q : ℕ → Bool} (t : ℕ)
    (h : ∀ s, s ≤ t → x s=y s) (hp : ∀ s, s < t → p s=q s) :
    HeldRelative.schedule δ x p t=HeldRelative.schedule δ y q t := by
  induction t with
  | zero => exact h 0 le_rfl
  | succ t ih =>
    simp only [HeldRelative.schedule,ih (fun s hs => h s (by omega))
      (fun s hs => hp s (by omega)),h (t+1) le_rfl,hp t (by omega)]

theorem epoch_congr {a b : ℕ → ι → ℝ} {p q : ℕ → Bool} (t : ℕ)
    (h : ∀ s, s ≤ t → a s=b s) (hp : ∀ s, s < t → p s=q s) :
    EpochGeometry.schedule a p t=EpochGeometry.schedule b q t := by
  induction t with
  | zero => simp only [EpochGeometry.schedule,h 0 le_rfl]
  | succ t ih =>
    simp only [EpochGeometry.schedule,ih (fun s hs => h s (by omega))
      (fun s hs => hp s (by omega)),h t (by omega),h (t+1) le_rfl,hp t (by omega)]

theorem side_congr {a b : ℕ → ι → ℝ} {p q : ℕ → Bool} (t : ℕ)
    (h : ∀ s, s ≤ t → a s=b s) (hp : ∀ s, s < t → p s=q s) :
    SideReferenceSchedule.side a p t=SideReferenceSchedule.side b q t := by
  simp only [SideReferenceSchedule.side,epoch_congr t h hp,h t le_rfl]

theorem reset_congr {a b : ℕ → ι → ℝ} {p q : ℕ → Bool} (t : ℕ)
    (h : ∀ s, s ≤ t+1 → a s=b s) (hp : ∀ s, s ≤ t → p s=q s) :
    SideReferenceSchedule.reset a p t=SideReferenceSchedule.reset b q t := by
  unfold SideReferenceSchedule.reset
  rw [epoch_congr t (fun s hs => h s (by omega))
    (fun s hs => hp s (by omega)),h t (by omega),h (t+1) le_rfl,hp t le_rfl]

theorem side_reference_congr {a b : ℕ → ι → ℝ} {p q : ℕ → Bool} (t : ℕ)
    (h : ∀ s, s ≤ t → a s=b s) (hp : ∀ s, s < t → p s=q s) :
    SideReferenceSchedule.reference a p t=SideReferenceSchedule.reference b q t := by
  apply forced_congr
  · intro s hs
    exact side_congr s (fun r hr => h r (by omega)) (fun r hr => hp r (by omega))
  · intro s hs
    exact reset_congr s (fun r hr => h r (by omega)) (fun r hr => hp r (by omega))

theorem alpha_congr {a b : ℕ → ι → ℝ} {p q : ℕ → Bool} (k : ℕ) (ct C : ℝ) (t : ℕ)
    (h : ∀ s, s ≤ t → a s=b s) (hp : ∀ s, s < t → p s=q s) :
    EpochAlphaSchedule.schedule a p k ct C t=EpochAlphaSchedule.schedule b q k ct C t := by
  simp only [EpochAlphaSchedule.schedule,h t le_rfl,epoch_congr t h hp,side_reference_congr t h hp]

end UniformKServer.CausalSchedules

end


end

end OAI
