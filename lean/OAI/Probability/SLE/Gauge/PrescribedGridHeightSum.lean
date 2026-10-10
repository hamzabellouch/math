import OAI.Probability.SLE.Gauge.PrescribedCoverGrid
import OAI.Probability.SLE.Gauge.PrescribedHeightSum

namespace OAI

/-! Summing the one-point height factor over the actual finite shifted
grid. The constant depends on the bounded region, not on the mesh. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace SLEExactGauge

private lemma int_row_sum (α r : ℝ) (N : ℤ) :
    (∑ j∈Finset.Icc 0 N, (((j:ℝ)+1/2)*r)^(-α)) =
      ∑ j∈Finset.range (N+1).toNat, (((j:ℝ)+1/2)*r)^(-α) := by
  rw [Int.Icc_eq_finset_map,Finset.sum_map]
  simp only [sub_zero,Function.Embedding.trans_apply,addLeftEmbedding_apply,zero_add,
    Nat.castEmbedding_apply,Int.cast_natCast]

theorem prescribed_grid_height_sum_bound (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α<1)
    {R r : ℝ} (hR : 0 ≤ R) (hr : 0<r) (hr1 : r ≤ 1) (K : Set ℂ) :
    (∑ ij∈prescribedGridIndex R r K, (prescribedGridCenter r ij).im^(-α)) ≤
      ((2*R+5)*((2:ℝ)^α/(1-α))*(R+3)^(1-α))*r^(-2:ℝ) := by
  classical
  let N : ℤ := ⌈R/r⌉+1
  have hN0 : 0 ≤ N := by
    have hceil := Int.le_ceil (R/r)
    have hquot : 0 ≤ R/r := div_nonneg hR hr.le
    have hNreal : (0:ℝ) ≤ N := by dsimp only [N]; push_cast; linarith
    exact_mod_cast hNreal
  have hN : (N:ℝ) ≤ R/r+2 := by
    have hceil := Int.ceil_lt_add_one (R/r)
    dsimp only [N]
    push_cast
    linarith
  let M := (N+1).toNat
  have hM : (M:ℝ)=(N:ℝ)+1 := by
    have h := Int.toNat_of_nonneg (show 0 ≤ N+1 by omega)
    exact_mod_cast h
  have hwidth : (M:ℝ)*r ≤ R+3 := by
    rw [hM]
    have h := mul_le_mul_of_nonneg_right hN hr.le
    rw [add_mul,div_mul_cancel₀ _ hr.ne'] at h
    nlinarith
  have hcol : (2*(N:ℝ)+1) ≤ (2*R+5)/r := by
    apply (le_div_iff₀ hr).mpr
    have h := mul_le_mul_of_nonneg_right hN hr.le
    rw [add_mul,div_mul_cancel₀ _ hr.ne'] at h
    nlinarith
  have hsub : prescribedGridIndex R r K ⊆ (Finset.Icc (-N) N) ×ˢ (Finset.Icc 0 N) := by
    intro ij hij
    have hmem := Finset.mem_filter.mp hij
    have hi := Finset.mem_product.mp hmem.1
    exact Finset.mem_product.mpr ⟨hi.1,Finset.mem_Icc.mpr
      ⟨hmem.2.1,(Finset.mem_Icc.mp hi.2).2⟩⟩
  have hrows : (∑ j∈Finset.Icc 0 N, (((j:ℝ)+1/2)*r)^(-α)) ≤
      ((2:ℝ)^α/(1-α))*r⁻¹*(R+3)^(1-α) := by
    rw [int_row_sum]
    refine (scaled_half_integer_row_sum α hα0 hα1 hr M).trans ?_
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (mul_nonneg (Nat.cast_nonneg M) hr.le) hwidth (by linarith)) (by positivity)
  calc
    _ = ∑ ij∈prescribedGridIndex R r K, (((ij.2:ℝ)+1/2)*r)^(-α) := by
      apply Finset.sum_congr rfl
      intro ij hij
      rw [(prescribedGrid_center_height hr hij).1]
    _ ≤ ∑ ij∈(Finset.Icc (-N) N) ×ˢ (Finset.Icc 0 N), (((ij.2:ℝ)+1/2)*r)^(-α) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ij hij _ =>
        Real.rpow_nonneg (mul_nonneg (by
          have hj := (Finset.mem_Icc.mp (Finset.mem_product.mp hij).2).1
          have hjR : (0:ℝ) ≤ ij.2 := by exact_mod_cast hj
          linarith) hr.le) _)
    _ = (2*(N:ℝ)+1)*∑ j∈Finset.Icc 0 N, (((j:ℝ)+1/2)*r)^(-α) := by
      have hcard : ((Finset.Icc (-N) N).card:ℝ)=2*(N:ℝ)+1 := by
        have hh := Int.card_Icc_of_le (a := -N) (b := N) (by omega)
        have hh' : ((Finset.Icc (-N) N).card:ℝ)=(N:ℝ)+1-(-(N:ℝ)) := by exact_mod_cast hh
        linarith
      rw [Finset.sum_product]
      dsimp only [Prod.snd]
      rw [Finset.sum_const,nsmul_eq_mul,hcard]
    _ ≤ ((2*R+5)/r)*(((2:ℝ)^α/(1-α))*r⁻¹*(R+3)^(1-α)) :=
      mul_le_mul hcol hrows (Finset.sum_nonneg (fun j hj => Real.rpow_nonneg (by
        have hjR : (0:ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
        positivity) _)) (by positivity)
    _ = _ := by
      rw [Real.rpow_neg hr.le,Real.rpow_two]
      field_simp

end SLEExactGauge

end

end OAI
