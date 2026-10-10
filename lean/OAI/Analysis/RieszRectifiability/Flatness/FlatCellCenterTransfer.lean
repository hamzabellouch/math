import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.CellChainGeometry
import OAI.Analysis.RieszRectifiability.Flatness.FlatCellSeeds

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem HasFlatCell.mono {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points) (A B α β : ℝ)
    (hBA : B ≤ A) (hαβ : α ≤ β) (hflat : HasFlatCell n μ R hR k z A α) :
    HasFlatCell n μ R hR k z B β := by
  obtain ⟨S, hS, hf, hb⟩ := hflat
  have hr := (latticeRadius_pos R hR k).le
  have hsub := ball_subset_ball (x := (z : Ambient d)) (mul_le_mul_of_nonneg_right hBA hr)
  have hbound := mul_le_mul_of_nonneg_right hαβ hr
  exact ⟨S, hS, fun x hx hs => (hf x (hsub hx) hs).trans hbound,
    fun x hx hs => (hb x (hsub hx) hs).trans hbound⟩

theorem HasFlatCell.tube_at_descendant_center {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points) (H α : ℝ) (K : ℕ)
    (hH : 1 ≤ H) (hα : 0 ≤ α)
    (hflat : HasFlatCell n μ R hR k z (H * (2 : ℝ) ^ K + 2) α)
    (i : SupportCellDescendant μ R hR k z) :
    ∃ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane n S ∧
      ∀ x ∈ ball i.center ((H * latticeRadius R k) * (2 : ℝ) ^ K), x ∈ μ.support →
        infDist x (S : Set (Ambient d)) ≤ α * (H * latticeRadius R k) := by
  obtain ⟨S, hS, hf, _⟩ := hflat
  refine ⟨S, hS, ?_⟩
  have hp := latticeRadius_pos R hR k
  have hsub : ball i.center ((H * latticeRadius R k) * (2 : ℝ) ^ K) ⊆
      ball (z : Ambient d) ((H * (2 : ℝ) ^ K + 2) * latticeRadius R k) := by
    apply ball_subset_outer_of_radius_dist
    have hi := i.center_dist_top
    nlinarith
  intro x hx hxs
  apply (hf x (hsub hx) hxs).trans
  have ht := mul_le_mul_of_nonneg_right hH hp.le
  have hu := mul_le_mul_of_nonneg_left ht hα
  simpa only [one_mul] using! hu

theorem HasFlatCell.beta_lt {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points) (A H α ε : ℝ)
    (hH : 0 < H) (hHA : H ≤ A) (hα : 0 ≤ α) (hsmall : 2 * α < ε * H)
    (hflat : HasFlatCell n μ R hR k z A α) :
    bilateralBeta n μ z (H * latticeRadius R k) < ε := by
  obtain ⟨S, hS, hf, hb⟩ := hflat
  have hr := latticeRadius_pos R hR k
  have hsub : ball (z : Ambient d) (H * latticeRadius R k) ⊆
      ball (z : Ambient d) (A * latticeRadius R k) :=
    ball_subset_ball (mul_le_mul_of_nonneg_right hHA hr.le)
  apply (bilateralBeta_le_planeError n μ z (H * latticeRadius R k)
    (mul_pos hH hr).le S hS).trans_lt
  have h1 := directedBallDeviation_le μ.support (S : Set (Ambient d)) z
    (H * latticeRadius R k) (α * latticeRadius R k) (mul_nonneg hα hr.le)
    (fun x hx hs => hf x (hsub hx) hs)
  have h2 := directedBallDeviation_le (S : Set (Ambient d)) μ.support z
    (H * latticeRadius R k) (α * latticeRadius R k) (mul_nonneg hα hr.le)
    (fun x hx hs => hb x (hsub hx) hs)
  apply (div_lt_iff₀ (mul_pos hH hr)).mpr
  nlinarith [mul_lt_mul_of_pos_right hsmall hr]

end

end RieszRectifiability

end OAI
