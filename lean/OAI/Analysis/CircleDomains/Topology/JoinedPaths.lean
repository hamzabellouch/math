import OAI.Analysis.CircleDomains.Topology.CountablePathTimes
import Mathlib.Topology.Path

namespace OAI

/-! A binary continuous join with exact affine parametrizations of both
halves, for attaching collar tails to retained fragments. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [TopologicalSpace X]

def joinedPath (γ δ : C(PathTime, X)) (h : γ ⊤ = δ ⊥) : C(PathTime, X) :=
  ((⟨γ, rfl, rfl⟩ : Path (γ ⊥) (γ ⊤)).trans (⟨δ, h.symm, rfl⟩ : Path (γ ⊤) (δ ⊤))).toContinuousMap

theorem joinedPath_first (γ δ : C(PathTime, X)) (h : γ ⊤ = δ ⊥) (s : PathTime) :
    joinedPath γ δ h (affinePathTime ⊥ (collarTime 1) s) = γ s := by
  change ((⟨γ, rfl, rfl⟩ : Path (γ ⊥) (γ ⊤)).trans
    (⟨δ, h.symm, rfl⟩ : Path (γ ⊤) (δ ⊤))) _ = _
  rw [Path.trans_apply]
  have hhalf : (affinePathTime ⊥ (collarTime 1) s : ℝ) ≤ 1/2 := by
    rw [affinePathTime_coe]
    simp only [collarTime, pow_one]
    change ((1:ℝ)/2 - 0) * (s : ℝ) + 0 ≤ 1/2
    nlinarith [s.property.2]
  rw [dite_eq_left hhalf]
  apply congrArg γ
  apply Subtype.ext
  simp only [affinePathTime_coe, collarTime, pow_one]
  change 2 * ((1/2 - 0) * (s : ℝ) + 0) = (s : ℝ)
  ring

theorem joinedPath_second (γ δ : C(PathTime, X)) (h : γ ⊤ = δ ⊥) (s : PathTime) :
    joinedPath γ δ h (affinePathTime (collarTime 1) ⊤ s) = δ s := by
  change ((⟨γ, rfl, rfl⟩ : Path (γ ⊥) (γ ⊤)).trans
    (⟨δ, h.symm, rfl⟩ : Path (γ ⊤) (δ ⊤))) _ = _
  rw [Path.trans_apply]
  split_ifs with ht
  · have hs : (s : ℝ) = 0 := by
      have hs0 := s.property.1
      have hh : (1 - 1/2) * (s : ℝ) + 1/2 ≤ (1:ℝ)/2 := by
        rw [affinePathTime_coe] at ht
        simpa only [collarTime, pow_one, Set.Icc.coe_top] using ht
      linarith
    have hs' : s = ⊥ := Subtype.ext hs
    subst s
    change γ _ = δ ⊥
    rw [← h]
    apply congrArg γ
    apply Subtype.ext
    simp [affinePathTime_zero, collarTime]
  · apply congrArg δ
    apply Subtype.ext
    simp only [affinePathTime_coe, collarTime, pow_one]
    change 2 * ((1 - 1/2) * (s : ℝ) + 1/2) - 1 = (s : ℝ)
    ring

theorem joinedPath_collar_succ (γ δ : C(PathTime, X)) (h : γ ⊤ = δ ⊥)
    (n : ℕ) (s : PathTime) :
    joinedPath γ δ h (affinePathTime (collarTime (n+2)) (collarTime (n+1)) s) =
      γ (affinePathTime (collarTime (n+1)) (collarTime n) s) := by
  have he : affinePathTime (collarTime (n+2)) (collarTime (n+1)) s =
      affinePathTime ⊥ (collarTime 1)
        (affinePathTime (collarTime (n+1)) (collarTime n) s) := by
    apply Subtype.ext
    simp only [affinePathTime_coe, collarTime, pow_succ, pow_zero, one_mul]
    change ((1/2:ℝ)^n * (1/2) - (1/2)^n * (1/2) * (1/2)) * (s:ℝ) +
      (1/2)^n * (1/2) * (1/2) =
      ((1/2)-0) * (((1/2)^n - (1/2)^n*(1/2))*(s:ℝ) + (1/2)^n*(1/2)) + 0
    ring
  rw [he, joinedPath_first]

theorem joinedPath_zero (γ δ : C(PathTime, X)) (h : γ ⊤ = δ ⊥) :
    joinedPath γ δ h ⊥ = γ ⊥ := by
  simpa only [affinePathTime_zero] using joinedPath_first γ δ h ⊥

theorem joinedPath_one (γ δ : C(PathTime, X)) (h : γ ⊤ = δ ⊥) :
    joinedPath γ δ h ⊤ = δ ⊤ := by
  simpa only [affinePathTime_one] using joinedPath_second γ δ h ⊤

end CircleDomainRigidity

end

end OAI
