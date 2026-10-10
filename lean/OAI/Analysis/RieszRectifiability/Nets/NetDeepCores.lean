import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.ConstructedSupportCells

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set

theorem netAncestor_forced_near_net_point {X : Type*} [MetricSpace X] {E : Set X}
    (R : ℝ) (hR : 0 < R) (N : (k : ℕ) → SeparatedCover E (latticeRadius R k))
    (k t : ℕ) (x z : E) (hx : (x : X) ∈ (N (k + t)).points)
    (hz : (z : X) ∈ (N k).points)
    (hxz : dist (x : X) (z : X) < latticeRadius R k / 4) : netAncestor N k t x = z := by
  cases t with
  | zero =>
      change x = z
      by_contra hne
      have hs := (N k).separated (by simpa only [Nat.add_zero] using! hx) hz
        (fun h => hne (Subtype.ext h))
      have hp := latticeRadius_pos R hR k
      linarith
  | succ t => exact netAncestor_forced_near_center R hR N k t x z hz hxz

theorem netDescendants_arbitrarily_deep {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (hr : ∀ k, 0 < r k)
    (hmono : Monotone (fun k => (N k).points)) (k q : ℕ) (z : E) (x : X)
    (hx : x ∈ netDescendants N k z) :
    ∃ t : ℕ, ∃ hxE : x ∈ E,
      x ∈ (N (k + (q + t))).points ∧ netAncestor N k (q + t) ⟨x, hxE⟩ = z := by
  obtain ⟨t, hxE, hxN, ha⟩ := hx
  refine ⟨t, hxE, hmono (by omega) hxN, ?_⟩
  rw [show q + t = t + q by omega, netAncestor_add,
    netAncestor_self_of_mem N hr hmono (k + t) q ⟨x, hxE⟩ hxN]
  exact ha

theorem closedNetCell_avoids_deep_other_core {X : Type*} [MetricSpace X] {E : Set X}
    (R : ℝ) (hR : 0 < R) (N : (k : ℕ) → SeparatedCover E (latticeRadius R k))
    (hmono : Monotone (fun k => (N k).points)) (k q : ℕ) (w z : E)
    (hz : (z : X) ∈ (N (k + q)).points) (hne : netAncestor N k q z ≠ w) :
    closedNetCell N k w ⊆ (ball (z : X) (latticeRadius R (k + q) / 4))ᶜ := by
  apply isOpen_ball.isClosed_compl.closure_subset_iff.mpr
  intro x hx hball
  obtain ⟨t, hxE, hxN, ha⟩ := netDescendants_arbitrarily_deep N (latticeRadius_pos R hR)
    hmono k q w x hx
  have hxN' : x ∈ (N ((k + q) + t)).points :=
    (congrArg (fun l : ℕ => x ∈ (N l).points) (Nat.add_assoc k q t)).mpr hxN
  have hf := netAncestor_forced_near_net_point R hR N (k + q) t ⟨x, hxE⟩ z hxN' hz hball
  rw [netAncestor_add, hf] at ha
  exact hne ha

theorem supportLatticeCell_avoids_deep_other_core {d : ℕ}
    (μ : MeasureTheory.Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k q : ℕ)
    (w : (supportLatticeNets μ R hR k).points)
    (z : (supportLatticeNets μ R hR (k + q)).points)
    (hne : supportLatticeAncestor μ R hR k q z ≠ w) :
    supportLatticeCell μ R hR k w ⊆
      (ball (z : Ambient d) (latticeRadius R (k + q) / 4))ᶜ := by
  have hn : netAncestor (supportLatticeNets μ R hR) k q (supportLatticeCenter μ R hR (k + q) z) ≠
      supportLatticeCenter μ R hR k w := by
    intro heq
    apply hne
    apply Subtype.ext
    exact congrArg (fun y : μ.support => (y : Ambient d)) heq
  exact closedNetCell_avoids_deep_other_core R hR (supportLatticeNets μ R hR)
    (supportLatticeNets_monotone μ R hR) k q (supportLatticeCenter μ R hR k w)
    (supportLatticeCenter μ R hR (k + q) z) z.property hn

end

end RieszRectifiability

end OAI
