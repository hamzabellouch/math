import OAI.Analysis.CircleDomains.Topology.JoinedPaths
import OAI.Analysis.CircleDomains.Modulus.CountablePhysicalCost

namespace OAI

/-! Binary joining preserves finite physical length and adds the exact
physical occupation costs. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {G : Set Y} {U : Set X}

def collarRestrictions (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (n : ℕ) : FinitePhysicalPath e y₀ :=
  affineFinitePhysicalPath e hU y₀ γ (collarTime_strictAnti (Nat.lt_succ_self n))

theorem collarRestrictions_length_sum (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) :
    (∑'n, physicalDomainLength e y₀ (collarRestrictions e hU y₀ γ n).val) =
      physicalDomainLength e y₀ γ.val :=
  (physicalDomainLength_collarPieces e hU y₀ γ (collarRestrictions e hU y₀ γ)
    (fun _ _ => rfl)).symm

def joinedPhysicalPieces (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ δ : FinitePhysicalPath e y₀) : ℕ → FinitePhysicalPath e y₀
  | 0 => δ
  | n+1 => collarRestrictions e hU y₀ γ n

theorem joinedPhysicalPieces_match (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ δ : FinitePhysicalPath e y₀) (h : γ.val ⊤ = δ.val ⊥) (n : ℕ) (s : PathTime) :
    joinedPath γ.val δ.val h (affinePathTime (collarTime (n+1)) (collarTime n) s) =
      (joinedPhysicalPieces e hU y₀ γ δ n).val s := by
  cases n with
  | zero =>
    change joinedPath γ.val δ.val h (affinePathTime (collarTime 1) (collarTime 0) s) = δ.val s
    rw [collarTime_zero]
    exact joinedPath_second γ.val δ.val h s
  | succ n => exact joinedPath_collar_succ γ.val δ.val h n s

theorem joinedPhysicalPieces_length_sum (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ δ : FinitePhysicalPath e y₀) :
    (∑'n, physicalDomainLength e y₀ (joinedPhysicalPieces e hU y₀ γ δ n).val) =
      physicalDomainLength e y₀ δ.val + physicalDomainLength e y₀ γ.val := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  exact congrArg (fun a => physicalDomainLength e y₀ δ.val + a)
    (collarRestrictions_length_sum e hU y₀ γ)

def joinedFinitePhysicalPath (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ δ : FinitePhysicalPath e y₀) (h : γ.val ⊤ = δ.val ⊥) : FinitePhysicalPath e y₀ :=
  ⟨joinedPath γ.val δ.val h, by
    apply (physicalDomainLength_collarPieces_le e hU y₀
      (joinedPhysicalPieces e hU y₀ γ δ) _ (joinedPhysicalPieces_match e hU y₀ γ δ h)).trans_lt
    rw [joinedPhysicalPieces_length_sum]
    exact ENNReal.add_lt_top.mpr ⟨δ.property, γ.property⟩⟩

variable [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]

theorem collarRestrictions_cost_sum (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (g : Y → ℝ≥0∞) (hg : Measurable g) :
    (∑'n, ∫⁻y, g y ∂dyadicPhysicalOccupation e y₀ (collarRestrictions e hU y₀ γ n)) =
      ∫⁻y, g y ∂dyadicPhysicalOccupation e y₀ γ :=
  (physicalCost_collarPieces e hU y₀ γ (collarRestrictions e hU y₀ γ)
    (fun _ _ => rfl) g hg).symm

theorem physicalCost_joined (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y)
    (γ δ : FinitePhysicalPath e y₀) (h : γ.val ⊤ = δ.val ⊥)
    (g : Y → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻y, g y ∂dyadicPhysicalOccupation e y₀ (joinedFinitePhysicalPath e hU y₀ γ δ h)) =
      (∫⁻y, g y ∂dyadicPhysicalOccupation e y₀ γ) +
        (∫⁻y, g y ∂dyadicPhysicalOccupation e y₀ δ) := by
  rw [physicalCost_collarPieces e hU y₀ _ (joinedPhysicalPieces e hU y₀ γ δ)
    (joinedPhysicalPieces_match e hU y₀ γ δ h) g hg, tsum_eq_zero_add' ENNReal.summable]
  change (∫⁻y, g y ∂dyadicPhysicalOccupation e y₀ δ) +
    (∑'n, ∫⁻y, g y ∂dyadicPhysicalOccupation e y₀ (collarRestrictions e hU y₀ γ n)) = _
  rw [collarRestrictions_cost_sum e hU y₀ γ g hg, add_comm]

end CircleDomainRigidity

end

end OAI
