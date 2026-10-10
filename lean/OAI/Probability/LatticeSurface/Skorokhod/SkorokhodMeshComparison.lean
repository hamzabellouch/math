import Mathlib
import OAI.Probability.LatticeSurface.Skorokhod.SkorokhodMeshSupport

namespace OAI

namespace ConvexSkorokhod

open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma mesh_comparison (B : Body E) (x₀ c : E) (r R δ η : ℝ)
    (hx₀ : x₀∈B.carrier) (hr : 0 < r) (hR : ‖x₀-c‖ ≤ R)
    (hball : Metric.closedBall c r⊆B.carrier) (w : ℝ → E)
    (hosc : ∀t∈Icc (0:ℝ) 1,‖w t-w 0‖ ≤ r/2)
    (hδ : 0 ≤ δ) (huc : ∀s∈Icc (0:ℝ) 1,∀t∈Icc (0:ℝ) 1,|s-t| < η → ‖w s-w t‖ ≤ δ)
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (hmn : (1:ℝ)/m+1/n < η)
    (t : ℝ) (ht : t∈Icc (0:ℝ) 1) :
    ‖mesh B x₀ w m t-mesh B x₀ w n t‖ ≤ δ+Real.sqrt (4*δ*(R^2/r)) := by
  let p := ⌊t*((m*n:ℕ):ℝ)⌋₊
  have hp : p ≤ m*n := by
    apply Nat.floor_le_of_le
    simpa only [mul_one,one_mul] using mul_le_mul_of_nonneg_right ht.2 (Nat.cast_nonneg (m*n))
  let v₀ : ℕ → E := fun i => sampledDriver w m (i/n)
  let v₁ : ℕ → E := fun i => sampledDriver w n (i/m)
  have hv₀ : v₀ 0=w 0 := by simp [v₀,sampledDriver]
  have hv₁ : v₁ 0=w 0 := by simp [v₁,sampledDriver]
  have hbound₀ : ∀i ≤ p,‖v₀ i-v₀ 0‖ ≤ r/2 := by
    intro i hi
    rw [hv₀]
    exact hosc _ (sampled_time_bounds i m n hm hn (hi.trans hp))
  have hbound₁ : ∀i ≤ p,‖v₁ i-v₁ 0‖ ≤ r/2 := by
    intro i hi
    rw [hv₁]
    exact hosc _ (sampled_time_bounds i n m hn hm (by simpa [Nat.mul_comm] using hi.trans hp))
  have hvar₀ := regulator_variation_bound B x₀ c r R hx₀ hr hR hball v₀ p hbound₀
  have hvar₁ := regulator_variation_bound B x₀ c r R hx₀ hr hR hball v₁ p hbound₁
  have hinput : ∀i ≤ p,‖(x₀+(v₀ i-v₀ 0))-(x₀+(v₁ i-v₁ 0))‖ ≤ δ := by
    intro i hi
    rw [hv₀,hv₁]
    have he : (x₀+(v₀ i-w 0))-(x₀+(v₁ i-w 0))=v₀ i-v₁ i := by abel
    rw [he]
    exact huc _ (sampled_time_bounds i m n hm hn (hi.trans hp)) _
      (sampled_time_bounds i n m hn hm (by simpa [Nat.mul_comm] using hi.trans hp))
      ((sampled_time_error i m n hm hn).trans_lt hmn)
  have hb := walk_driver_stability B x₀ x₀ hx₀ hx₀ v₀ v₁ p δ hδ hinput
  have hc : 2*δ*(variation (regulator B x₀ v₀) p+variation (regulator B x₀ v₁) p) ≤ 4*δ*(R^2/r) := by
    nlinarith [mul_le_mul_of_nonneg_left hvar₀ hδ,mul_le_mul_of_nonneg_left hvar₁ hδ]
  have hw₀ : walk B x₀ v₀ p=mesh B x₀ w m t := by
    rw [show v₀=fun i => sampledDriver w m (i/n) from rfl,walk_repeat B x₀ hx₀ _ n hn]
    unfold mesh
    congr 1
    exact floor_product_div t m n hn
  have hw₁ : walk B x₀ v₁ p=mesh B x₀ w n t := by
    rw [show v₁=fun i => sampledDriver w n (i/m) from rfl,walk_repeat B x₀ hx₀ _ m hm]
    unfold mesh
    congr 1
    simpa only [Nat.mul_comm] using floor_product_div t n m hm
  rw [hw₀,hw₁] at hb
  exact hb.trans (add_le_add le_rfl (Real.sqrt_le_sqrt hc))

end ConvexSkorokhod

end OAI
