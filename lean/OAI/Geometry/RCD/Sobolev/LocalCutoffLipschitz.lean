import OAI.Analysis.RCDHeat.HeatFisher

namespace OAI

/-! # Uniform cutoff bounds for locally Lipschitz functions

Only values and Lipschitz control on the support of the cutoff are needed.
The constants are uniform over a family with the same local bounds.
-/

open Set Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem local_lipschitz_cutoff {s : Set X} {f ψ : X → ℝ} {L A C B : ℝ≥0}
    (hf : LipschitzOnWith L f s) (hA : ∀ x ∈ s, |f x| ≤ A)
    (hψ : LipschitzWith C ψ) (hB : ∀ x, |ψ x| ≤ B)
    (hzero : ∀ x ∉ s, ψ x = 0) :
    LipschitzWith (A*C+B*L) (fun x => ψ x*f x) ∧
      ∀ x, |ψ x*f x| ≤ B*A := by
  obtain ⟨F,hF,he⟩ := hf.extend_real
  let H := fun x => min (max (F x) (-(A:ℝ))) (A:ℝ)
  have hH : LipschitzWith L H := (hF.max_const (-(A:ℝ))).min_const (A:ℝ)
  have hHb (x : X) : |H x| ≤ A := by
    apply abs_le.mpr
    exact ⟨le_min (le_max_right _ _) (by nlinarith [A.coe_nonneg]),min_le_right _ _⟩
  have hHeq (x : X) (hx : x ∈ s) : H x = f x := by
    dsimp only [H]
    rw [← he hx,max_eq_left (abs_le.mp (hA x hx)).1,
      min_eq_left (abs_le.mp (hA x hx)).2]
  have heq : (fun x => ψ x*H x) = (fun x => ψ x*f x) := by
    funext x
    by_cases hx : x ∈ s
    · rw [hHeq x hx]
    · simp only [hzero x hx,zero_mul]
  rw [← heq]
  constructor
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq]
    have hid : ψ x*H x-ψ y*H y=(ψ x-ψ y)*H x+ψ y*(H x-H y) := by ring
    rw [hid]
    calc
      _ ≤ |(ψ x-ψ y)*H x|+|ψ y*(H x-H y)| := abs_add_le _ _
      _ = |ψ x-ψ y| * |H x|+|ψ y| * |H x-H y| := by rw [abs_mul,abs_mul]
      _ ≤ ((C:ℝ)*dist x y)*A+B*((L:ℝ)*dist x y) := by
        gcongr
        · simpa only [Real.dist_eq] using hψ.dist_le_mul x y
        · exact hHb x
        · exact hB y
        · simpa only [Real.dist_eq] using hH.dist_le_mul x y
      _ = (A*C+B*L:ℝ≥0)*dist x y := by push_cast; ring
  · intro x
    rw [← congrFun heq x,abs_mul]
    exact mul_le_mul (hB x) (hHb x) (abs_nonneg _) B.coe_nonneg

theorem radial_local_lipschitz_cutoff (z : X) {r : ℝ} (hr : 0 < r)
    {f : X → ℝ} {L A : ℝ≥0}
    (hf : LipschitzOnWith L f (closedBall z (2*r)))
    (hA : ∀ x ∈ closedBall z (2*r), |f x| ≤ A) :
    LipschitzWith (A*⟨r⁻¹,inv_nonneg.mpr hr.le⟩+L)
      (fun x => radialCutoff z r x*f x) ∧
    (∀ x, |radialCutoff z r x*f x| ≤ A) := by
  have hh := local_lipschitz_cutoff hf hA (radialCutoff_lipschitz z hr)
    (B := 1) (fun x => by
      rw [abs_of_nonneg (radialCutoff_bounds z r x).1]
      exact (radialCutoff_bounds z r x).2)
    (fun x hx => radialCutoff_eq_zero z hr
      (le_of_lt (by simpa only [mem_closedBall,not_le,dist_comm] using hx)))
  simpa only [one_mul,NNReal.coe_one] using hh

end RegularPointCoordinates

end

end OAI
