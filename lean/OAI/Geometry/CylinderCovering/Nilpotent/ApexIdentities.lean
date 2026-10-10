import OAI.Geometry.CylinderCovering.Nilpotent.Theorem
import OAI.Geometry.CylinderCovering.Nilpotent.ApexBridge

namespace OAI

noncomputable section
open Set MeasureTheory RuledApproximation

namespace CylinderCovering.NilpotentApexIdentities
open NilpotentApexNet

theorem selected_apex_clauses :
    Nilpotent.AuxiliaryApexStatement ∧ PhysicalApexNetStatement := by
  obtain ⟨_, _, _, _, _, haux, hphysical, _, _⟩ := Nilpotent.fullConstruction
  exact ⟨haux, hphysical⟩

theorem collapsed_apex_covered {k ρ σ s p : ℝ}
    (hk : 0 ≤ k) (hρ : 0 < ρ) (hσ : |σ| ≤ 1)
    (hs : |s| ≤ 1) (hp : |p| ≤ 1) :
    (s, s • velocity k σ p) ∈
      ⋃ j : Fin (meshCount ρ + 1), cylinder k ρ σ j := by
  apply apex_cover hk hρ hσ
  refine ⟨s, p, 0, hs, hp, le_rfl, hρ.le, ?_⟩
  simp

theorem endpoint_count : meshCount 1 + 1 = 3 := by
  norm_num [meshCount]

theorem weightedArea_neg_sign (h k ρ σ : ℝ) (j : Fin (meshCount ρ + 1)) :
    weightedArea h k ρ (-σ) j = weightedArea h k ρ σ j := by
  simp [weightedArea, NilpotentApexNet.weight, velocity]

theorem paired_weighted_cost (h : ℝ) {k ρ : ℝ}
    (hk : 0 ≤ k) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    (∑ j : Fin (meshCount ρ + 1), weightedArea h k ρ 1 j) +
      (∑ j : Fin (meshCount ρ + 1), weightedArea h k ρ (-1) j) ≤
      32 * (1 + k / 2) ^ 2 * ρ := by
  have hplus := apex_cost (σ := 1) h hk hρ hρ1
  have hminus := apex_cost (σ := -1) h hk hρ hρ1
  linarith

theorem both_physical_apex_covers {h k ρ : ℝ}
    (hh : 0 < h) (hk : 0 ≤ k) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    HasFiniteCover Cylinder.parallelogram
      (firstPhysicalMap h '' Nilpotent.apexSweep k ρ)
      (h * (16 * (1 + k / 2) ^ 2 * ρ)) ∧
    HasFiniteCover Cylinder.parallelogram
      (secondPhysicalMap h 1 '' Nilpotent.apexSweep (-k) ρ)
      (h * (16 * (1 + k / 2) ^ 2 * ρ)) := by
  constructor
  · simpa using signed_apex_cover (σ := 1) hh hk hρ hρ1 (by norm_num)
  · apply Nilpotent.physical_second_cover
    simpa using signed_apex_cover (σ := -1) hh hk hρ hρ1 (by norm_num)

end CylinderCovering.NilpotentApexIdentities

end

end OAI
