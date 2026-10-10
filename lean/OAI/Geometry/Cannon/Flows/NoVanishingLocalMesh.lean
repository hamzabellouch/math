import Mathlib
import OAI.Geometry.Cannon.Energy.MeshEnergy

namespace OAI

section
section
section
noncomputable section
section
section
section
section
open Set MeasureTheory
open scoped BigOperators

namespace CannonCrossEnergyLocal

open Set Metric Filter Topology CannonApprox CannonCrossEnergy

theorem no_vanishing_local_mesh {X : Type*} [MetricSpace X] [CompactSpace X]
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → X)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ r n)
    (f w : ℕ → X → ℝ) (S : ℕ → Set X) (K : Set X)
    (hKS : ∀ᶠ n in atTop, K ⊆ S n)
    (hCS : ∀ᶠ n in atTop, ∀ i, (ball (p n i) (2*r n) ∩ K).Nonempty →
      closedBall (p n i) (2*r n) ⊆ S n)
    (hf : ∀ᶠ n in atTop, ContinuousOn (f n) (S n))
    (hw : ∀ᶠ n in atTop, ContinuousOn (w n) (S n))
    (a b q : ℝ) (hab : a < b) (hq : 0 < q)
    (hlevels : ∀ᶠ n in atTop, ∀ t ∈ Icc a b, ∃ D : Set X,
      IsCompact D ∧ D.Nonempty ∧ IsPreconnected D ∧ D ⊆ K ∧
      (∀ x ∈ D, f n x = t) ∧ q ≤ CannonCrossEnergy.oscillation (w n) D)
    (hfe : Tendsto (fun n => meshEnergy (p n) (r n) 2 (f n) K) atTop (𝓝 0))
    (hwe : Tendsto (fun n => meshEnergy (p n) (r n) 2 (w n) K) atTop (𝓝 0)) :
    False := by
  classical
  have he := hfe.mul hwe
  simp only [mul_zero] at he
  have hlow : (q*(b-a))^2 ≤ (0:ℝ) := by
    apply ge_of_tendsto he
    filter_upwards [hlevels,hf,hw,hKS,hCS] with n hn hfn hwn hKSn hCSn
    let α := {i : ι n // (ball (p n i) (2*r n) ∩ K).Nonempty}
    let C : α → Set X := fun i => closedBall (p n i.val) (2*r n)
    have hcover : ∀ x ∈ K, ∃ i : α, x ∈ C i := by
      intro x hx
      obtain ⟨i,hi⟩ := hpnet n x
      have hxi : x ∈ ball (p n i) (2*r n) := by
        rw [mem_ball,dist_comm]
        linarith [hr n]
      exact ⟨⟨i,⟨x,hxi,hx⟩⟩, ball_subset_closedBall hxi⟩
    have hsum := finite_cell_level_comparison C (fun _ => isCompact_closedBall _ _)
      (fun _ => nonempty_closedBall.mpr (mul_nonneg (by norm_num) (hr n).le)) K hcover (f n) (w n)
      (S n) hKSn (fun i => hCSn i.val i.property) hfn hwn a b q hab.le hn
    calc
      (q*(b-a))^2 ≤ (∑ i, CannonCrossEnergy.oscillation (f n) (C i)*
          CannonCrossEnergy.oscillation (w n) (C i))^2 :=
        pow_le_pow_left₀ (mul_nonneg hq.le (sub_nonneg.mpr hab.le)) hsum 2
      _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
  exact (not_le_of_gt (sq_pos_of_pos (mul_pos hq (sub_pos.mpr hab)))) hlow

end CannonCrossEnergyLocal

open Set Topology

end
end
end
end
end
end
end
end

end OAI
