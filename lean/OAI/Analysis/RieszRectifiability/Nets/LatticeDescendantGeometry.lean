import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.FiniteSupportRefinements

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

structure SupportCellDescendant {d : ℕ} (μ : Measure (Ambient d))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points) where
  depth : ℕ
  center : Ambient d
  mem_net : center ∈ (supportLatticeNets μ R hR (k + depth)).points
  ancestor : supportLatticeAncestor μ R hR k depth ⟨center, mem_net⟩ = z

variable {d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R}
  {k : ℕ} {z : (supportLatticeNets μ R hR k).points}

def SupportCellDescendant.radius (i : SupportCellDescendant μ R hR k z) : ℝ := latticeRadius R (k + i.depth)

def SupportCellDescendant.binaryLevel (i : SupportCellDescendant μ R hR k z) : ℕ := 6 * i.depth + 1

def SupportCellDescendant.cell (i : SupportCellDescendant μ R hR k z) : Set (Ambient d) :=
  cleanSupportCell μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩

theorem SupportCellDescendant.radius_pos (i : SupportCellDescendant μ R hR k z) : 0 < i.radius :=
  latticeRadius_pos R hR (k + i.depth)

theorem SupportCellDescendant.center_mem_support (i : SupportCellDescendant μ R hR k z) : i.center ∈ μ.support :=
  (supportLatticeNets μ R hR (k + i.depth)).subset i.mem_net

theorem SupportCellDescendant.center_dist_top (i : SupportCellDescendant μ R hR k z) :
    dist i.center (z : Ambient d) ≤ 2 * latticeRadius R k := by
  have hm := (center_mem_cleanSupportCell μ R hR (k + i.depth) ⟨i.center, i.mem_net⟩).1
  have hp := supportLatticeCell_nested μ R hR k i.depth ⟨i.center, i.mem_net⟩ hm
  rw [i.ancestor] at hp
  exact (supportLatticeCell_bounds μ R hR k z).2 hp

theorem SupportCellDescendant.binary_radius (i : SupportCellDescendant μ R hR k z) :
    i.radius = (2 * latticeRadius R k) * (1 / 2 : ℝ) ^ i.binaryLevel := by
  change latticeRadius R (k + i.depth) = _
  rw [latticeRadius_add]
  change _ = (2 * latticeRadius R k) * (1 / 2 : ℝ) ^ (6 * i.depth + 1)
  rw [pow_succ, pow_mul]
  norm_num
  ring

theorem SupportCellDescendant.scale_eq (i j : SupportCellDescendant μ R hR k z)
    (hij : i.binaryLevel ≤ j.binaryLevel) :
    j.radius = i.radius * (1 / 2 : ℝ) ^ (j.binaryLevel - i.binaryLevel) := by
  rw [i.binary_radius, j.binary_radius]
  simp only [mul_assoc, ← pow_add, Nat.add_sub_of_le hij]

theorem SupportCellDescendant.separated (i j : SupportCellDescendant μ R hR k z)
    (hij : i.binaryLevel = j.binaryLevel) (hne : i ≠ j) :
    (1 / 8 : ℝ) * i.radius + (1 / 8 : ℝ) * j.radius ≤ dist i.center j.center := by
  have ht : i.depth = j.depth := by
    change 6 * i.depth + 1 = 6 * j.depth + 1 at hij
    omega
  rcases i with ⟨ti, xi, hxi, hai⟩
  rcases j with ⟨tj, xj, hxj, haj⟩
  dsimp only at ht
  subst tj
  have hxy : xi ≠ xj := by
    intro heq
    subst xj
    exact hne rfl
  have hs := (supportLatticeNets μ R hR (k + ti)).separated hxi hxj hxy
  change (1 / 8 : ℝ) * latticeRadius R (k + ti) +
    (1 / 8 : ℝ) * latticeRadius R (k + ti) ≤ dist xi xj
  have hp := latticeRadius_pos R hR (k + ti)
  linarith

theorem SupportCellDescendant.core_admissible (i : SupportCellDescendant μ R hR k z)
    (hcore : AdmissibleRadius μ (latticeRadius R k / 8)) :
    AdmissibleRadius μ ((1 / 8 : ℝ) * i.radius) := by
  refine ⟨mul_pos (by norm_num) i.radius_pos, ?_⟩
  have hle := latticeRadius_antitone R hR.le (Nat.le_add_right k i.depth)
  apply (ENNReal.ofReal_le_ofReal (show (1 / 8 : ℝ) * i.radius ≤ latticeRadius R k / 8 by
    change (1 / 8 : ℝ) * latticeRadius R (k + i.depth) ≤ _
    linarith)).trans hcore.2

theorem SupportCellDescendant.cell_subset_top (i : SupportCellDescendant μ R hR k z) :
    i.cell ⊆ cleanSupportCell μ R hR k z := by
  have h := cleanSupportCell_nested μ R hR k i.depth ⟨i.center, i.mem_net⟩
  rw [i.ancestor] at h
  exact h

end

end RieszRectifiability

end OAI
