import OAI.Geometry.RCD.Sobolev.MeasuredTestScaling

namespace OAI

/-! # Compactly supported tests of locally Lipschitz functions

An exact bounded Lipschitz extension on the test support reduces products
to the bounded Lipschitz class used by measured approximation.
-/

open Set Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates

theorem interior_lipschitz_test_product {n : ℕ} {R : ℝ} (hR : 0≤R)
    {g ψ : Euclidean n → ℝ} {L M B : ℝ≥0}
    (hg : LipschitzOnWith L g (closedBall 0 R)) (hψ : LipschitzWith M ψ)
    (hψb : ∀ z, |ψ z|≤B) (hψ0 : ∀ z, R<‖z‖ → ψ z=0) :
    ∃ C : ℝ≥0, 0<C ∧ LipschitzWith C (fun z => ψ z*g z) ∧
      ∀ z, |ψ z*g z|≤C := by
  obtain ⟨F,hF,he⟩ := hg.extend_real
  let A : ℝ≥0 := ⟨|g 0|+(L:ℝ)*R,by positivity⟩
  have hFb (z : Euclidean n) (hz : z∈closedBall 0 R) : |F z|≤A := by
    have hd := hF.dist_le_mul z 0
    have hzR : ‖z‖≤R := by simpa only [mem_closedBall,dist_zero_right] using hz
    rw [Real.dist_eq,← he (mem_closedBall_self hR),dist_zero_right] at hd
    have ht := abs_add_le (F z-g 0) (g 0)
    simp only [sub_add_cancel] at ht
    change |F z|≤|g 0|+(L:ℝ)*R
    nlinarith [mul_le_mul_of_nonneg_left hzR L.coe_nonneg]
  let H := fun z => min (max (F z) (-(A:ℝ))) (A:ℝ)
  have hH : LipschitzWith L H := (hF.max_const (-(A:ℝ))).min_const (A:ℝ)
  have hHb (z : Euclidean n) : |H z|≤A := by
    apply abs_le.mpr
    exact ⟨le_min (le_max_right _ _) (by nlinarith [A.coe_nonneg]),min_le_right _ _⟩
  have hHeq : EqOn H g (closedBall 0 R) := by
    intro z hz
    dsimp only [H]
    rw [max_eq_left (abs_le.mp (hFb z hz)).1,min_eq_left (abs_le.mp (hFb z hz)).2]
    exact (he hz).symm
  have heq : (fun z => ψ z*H z)=(fun z => ψ z*g z) := by
    funext z
    by_cases hz : z∈closedBall (0:Euclidean n) R
    · rw [hHeq hz]
    · have hzR : R<‖z‖ := by simpa only [mem_closedBall,dist_zero_right,not_le] using hz
      simp only [hψ0 z hzR,zero_mul]
  have hprod : LipschitzWith (A*M+B*L) (fun z => ψ z*H z) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq]
    have he : ψ x*H x-ψ y*H y=(ψ x-ψ y)*H x+ψ y*(H x-H y) := by ring
    rw [he]
    calc
      _ ≤ |(ψ x-ψ y)*H x|+|ψ y*(H x-H y)| := abs_add_le _ _
      _ = |ψ x-ψ y| * |H x|+|ψ y| * |H x-H y| := by rw [abs_mul,abs_mul]
      _ ≤ ((M:ℝ)*dist x y)*A+B*((L:ℝ)*dist x y) := by
        gcongr
        · simpa only [Real.dist_eq] using hψ.dist_le_mul x y
        · exact hHb x
        · exact hψb y
        · simpa only [Real.dist_eq] using hH.dist_le_mul x y
      _ = (A*M+B*L:ℝ≥0)*dist x y := by push_cast; ring
  let C : ℝ≥0 := 1+B*A+(A*M+B*L)
  refine ⟨C,by dsimp only [C]; positivity,?_,?_⟩
  · rw [← heq]
    exact hprod.weaken (le_add_of_nonneg_left (by positivity))
  · intro z
    have hb : |ψ z*H z|≤(B*A:ℝ≥0) := by
      rw [abs_mul]
      exact mul_le_mul (hψb z) (hHb z) (abs_nonneg _) B.coe_nonneg
    have hez := congrFun heq z
    rw [hez] at hb
    have hba : B*A≤C := (le_add_of_nonneg_left (show (0:ℝ≥0)≤1 from zero_le_one)).trans
      (le_add_of_nonneg_right (show (0:ℝ≥0)≤A*M+B*L from zero_le))
    exact hb.trans (by exact_mod_cast hba)

end RegularPointCoordinates

end

end OAI
