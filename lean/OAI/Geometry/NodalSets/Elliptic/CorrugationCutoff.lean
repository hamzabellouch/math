import Mathlib.Analysis.SpecialFunctions.Pow.Real
import OAI.Geometry.NodalSets.Elliptic.CompactSmoothExtension

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric
open scoped ContDiff Topology
noncomputable section

theorem compact_fractional_cutoff {K U : Set Coord} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (χ : Coord → ℝ) (C : ℝ), 0 < C ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x ∈ K, χ =ᶠ[𝓝 x] (fun _ ↦ 1)) ∧
      ∀ x, ‖fderiv ℝ χ x‖ ≤ C * (χ x)^((7:ℝ)/8) := by
  obtain ⟨b,hb,hbc,hbU,hbr,hb1⟩ := compact_smooth_cutoff hK hU hKU
  obtain ⟨M,hM⟩ := (hb.continuous_fderiv (by simp)).norm.bddAbove_range_of_hasCompactSupport
    ((hbc.fderiv (𝕜 := ℝ)).norm)
  let C := 8*(max M 0+1)
  have hC : 0 < C := by dsimp [C]; positivity
  let χ : Coord → ℝ := fun x ↦ (b x)^8
  have hsupp : tsupport χ ⊆ tsupport b := by
    apply closure_mono
    intro x hx hz
    exact hx (by simp [χ,hz])
  refine ⟨χ,C,hC,hb.pow 8,hbc.of_isClosed_subset isClosed_closure hsupp,hsupp.trans hbU,?_,?_,?_⟩
  · intro x
    exact ⟨pow_nonneg (hbr x).1 _,pow_le_one₀ (hbr x).1 (hbr x).2⟩
  · intro x hx
    filter_upwards [hb1 x hx] with y hy
    simp [χ,hy]
  · intro x
    have hD : ‖fderiv ℝ b x‖ ≤ max M 0+1 := by
      have hm := hM ⟨x,rfl⟩
      have hm' := le_max_left M 0
      linarith
    have hpow : (χ x)^((7:ℝ)/8) = (b x)^7 := by
      change ((b x)^8)^((7:ℝ)/8) = _
      rw [← Real.rpow_natCast (b x) 8,← Real.rpow_mul (hbr x).1]
      norm_num
    rw [hpow]
    change ‖fderiv ℝ (b^8) x‖ ≤ _
    rw [fderiv_pow 8 (hb.differentiable (by simp) x),norm_smul]
    simp only [Nat.cast_ofNat,nsmul_eq_mul,Nat.reduceSub,Real.norm_eq_abs,
      abs_mul,abs_of_nonneg (pow_nonneg (hbr x).1 7)]
    norm_num
    calc
      8* b x^7 * ‖fderiv ℝ b x‖ ≤ 8*b x^7*(max M 0+1) :=
        mul_le_mul_of_nonneg_left hD (mul_nonneg (by norm_num) (pow_nonneg (hbr x).1 7))
      _ = C*b x^7 := by dsimp [C]; ring

theorem exists_corrugation_cutoff : ∃ (χ : Coord → ℝ) (C : ℝ),
    0 < C ∧ ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
    tsupport χ ⊆ ball (0:Coord) (1/2) ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
    (∀ x ∈ closedBall (0:Coord) (1/4), χ =ᶠ[𝓝 x] (fun _ ↦ 1)) ∧
    ∀ x, ‖fderiv ℝ χ x‖ ≤ C*(χ x)^((7:ℝ)/8) := by
  apply compact_fractional_cutoff (isCompact_closedBall _ _) isOpen_ball
  intro x hx
  exact mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hx) (by norm_num))

end
end Yau.Geometry

end OAI
