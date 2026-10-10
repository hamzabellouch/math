import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.RichHyperplaneVariance

namespace OAI

namespace SharpRamseyFive.RichPlaneGeometry
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.RichPlaneOverlap
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

theorem multiplicity_budgets
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 3)
    (X : Finset (ℙ K V)) (M Kp u : ℕ) (hMpos : 0 < M)
    (hM : ∀ A ∈ F, M ≤ (X.filter fun x => x.submodule ≤ A).card)
    (hpointcap : ∀ H : Submodule K V, finrank K H = 4 →
      (X.filter fun x => x.submodule ≤ H).card ≤ Kp)
    (hlineLarge : 2*(Nat.card K+1) ≤ M)
    (hlineNum : 2*X.card ≤ u*M)
    (hmean : 2*((Q (Nat.card K) 2:ℝ)/Q (Nat.card K) 3)*Kp ≤ M)
    (hhyperNum : 4*(Nat.card K:ℝ)^2*Kp ≤ (u:ℝ)*M^2) :
    (∀ L : Submodule K V, finrank K L = 2 → (F.filter fun A => L ≤ A).card ≤ u) ∧
    (∀ H : Submodule K V, finrank K H = 4 → (F.filter fun A => A ≤ H).card ≤ u) := by
  constructor
  · intro L hL
    have hh := (rich_planes_through_line_twice F hF X M hM hlineLarge L hL).trans hlineNum
    exact Nat.le_of_mul_le_mul_right hh hMpos
  · intro H hH
    have hcap : ((X.filter fun x => x.submodule ≤ H).card:ℝ) ≤ Kp := by exact_mod_cast hpointcap H hH
    have hμ : 2*((Q (Nat.card K) 2:ℝ)/Q (Nat.card K) 3)*
        (X.filter fun x => x.submodule ≤ H).card ≤ M :=
      (mul_le_mul_of_nonneg_left hcap (by positivity)).trans hmean
    have hv := rich_planes_inside_hyperplane H hH F hF X M hM hμ
    have hnum := mul_le_mul_of_nonneg_left hcap (by positivity : 0 ≤ 4*(Nat.card K:ℝ)^2)
    have hc : ((F.filter fun A => A ≤ H).card:ℝ)*M^2 ≤ (u:ℝ)*M^2 :=
      hv.trans (hnum.trans hhyperNum)
    have hpos : (0:ℝ) < (M:ℝ)^2 := by positivity
    exact_mod_cast (mul_le_mul_iff_left₀ hpos).mp hc

theorem capped_rich_plane_count
    (F : Finset (Submodule K V)) (hF : ∀ A ∈ F, finrank K A = 3)
    (X : Finset (ℙ K V)) (M Kp u : ℕ) (hMpos : 0 < M)
    (hM : ∀ A ∈ F, M ≤ (X.filter fun x => x.submodule ≤ A).card)
    (hpointcap : ∀ H : Submodule K V, finrank K H = 4 →
      (X.filter fun x => x.submodule ≤ H).card ≤ Kp)
    (hlineLarge : 2*(Nat.card K+1) ≤ M)
    (hlineNum : 2*X.card ≤ u*M)
    (hmean : 2*((Q (Nat.card K) 2:ℝ)/Q (Nat.card K) 3)*Kp ≤ M)
    (hhyperNum : 4*(Nat.card K:ℝ)^2*Kp ≤ (u:ℝ)*M^2)
    (hlarge : 64*X.card ≤ M^2) :
    (F.card:ℝ)*M ≤ 16*X.card*(2*(u:ℝ)+1) := by
  obtain ⟨hl,hh⟩ := multiplicity_budgets F hF X M Kp u hMpos hM hpointcap
    hlineLarge hlineNum hmean hhyperNum
  exact rich_plane_count F hF u hl hh X M hM hlarge

end SharpRamseyFive.RichPlaneGeometry

end OAI
