import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.NetAncestorForcing

namespace OAI

namespace RieszRectifiability

noncomputable section

open Metric Set

def netDescendants {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k : ℕ) (z : E) : Set X :=
  {x | ∃ t : ℕ, ∃ hx : x ∈ E, x ∈ (N (k + t)).points ∧ netAncestor N k t ⟨x, hx⟩ = z}

def closedNetCell {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k : ℕ) (z : E) : Set X :=
  closure (netDescendants N k z)

theorem netDescendants_subset {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k : ℕ) (z : E) : netDescendants N k z ⊆ E := by
  rintro x ⟨t, hx, _, _⟩
  exact hx

theorem center_mem_netDescendants {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k : ℕ) (z : E)
    (hz : (z : X) ∈ (N k).points) : (z : X) ∈ netDescendants N k z :=
  ⟨0, z.property, by simpa only [Nat.add_zero] using! hz, rfl⟩

theorem closedNetCell_isClosed {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k : ℕ) (z : E) : IsClosed (closedNetCell N k z) :=
  isClosed_closure

theorem closedNetCell_subset {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (hE : IsClosed E) (k : ℕ) (z : E) :
    closedNetCell N k z ⊆ E :=
  hE.closure_subset_iff.mpr (netDescendants_subset N k z)

theorem closedNetCell_subset_closedBall {X : Type*} [MetricSpace X] {E : Set X}
    (R : ℝ) (hR : 0 < R) (N : (k : ℕ) → SeparatedCover E (latticeRadius R k))
    (k : ℕ) (z : E) : closedNetCell N k z ⊆ closedBall (z : X) (2 * latticeRadius R k) := by
  apply isClosed_closedBall.closure_subset_iff.mpr
  rintro x ⟨t, hx, _, ha⟩
  have hb := netAncestor_dist_le_latticeRadius R hR N k t ⟨x, hx⟩
  rw [ha] at hb
  exact hb

theorem netDescendants_nested {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k t : ℕ) (z w : E)
    (ha : netAncestor N k t w = z) :
    netDescendants N (k + t) w ⊆ netDescendants N k z := by
  rintro x ⟨u, hx, hnet, hanc⟩
  refine ⟨t + u, hx, ?_, ?_⟩
  · exact (congrArg (fun l : ℕ => x ∈ (N l).points) (Nat.add_assoc k t u)).mp hnet
  · rw [netAncestor_add, hanc, ha]

theorem closedNetCell_nested {X : Type*} [MetricSpace X] {E : Set X} {r : ℕ → ℝ}
    (N : (k : ℕ) → SeparatedCover E (r k)) (k t : ℕ) (z w : E)
    (ha : netAncestor N k t w = z) : closedNetCell N (k + t) w ⊆ closedNetCell N k z :=
  closure_mono (netDescendants_nested N k t z w ha)

theorem closedNetCell_avoids_other_core {X : Type*} [MetricSpace X] {E : Set X}
    (R : ℝ) (hR : 0 < R) (N : (k : ℕ) → SeparatedCover E (latticeRadius R k))
    (k : ℕ) (z w : E) (hz : (z : X) ∈ (N k).points) (hne : z ≠ w) :
    closedNetCell N k w ⊆ (ball (z : X) (latticeRadius R k / 4))ᶜ := by
  apply isOpen_ball.isClosed_compl.closure_subset_iff.mpr
  rintro x ⟨t, hx, hnet, hanc⟩ hball
  have hp := latticeRadius_pos R hR k
  cases t with
  | zero =>
      have hxw : (⟨x, hx⟩ : E) = w := hanc
      have hxz : x ≠ (z : X) := by
        intro h
        have he : (⟨x, hx⟩ : E) = z := Subtype.ext h
        exact hne (he.symm.trans hxw)
      have hs := (N k).separated (by simpa only [Nat.add_zero] using! hnet) hz hxz
      change dist x (z : X) < latticeRadius R k / 4 at hball
      linarith
  | succ t =>
      have hforce := netAncestor_forced_near_center R hR N k t ⟨x, hx⟩ z hz hball
      exact hne (hforce.symm.trans hanc)

end

end RieszRectifiability

end OAI
