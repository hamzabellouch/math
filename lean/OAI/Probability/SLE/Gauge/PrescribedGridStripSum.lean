import OAI.Probability.SLE.Gauge.PrescribedGridHeightSum

namespace OAI

/-! The height weight of cells near the real boundary. The bound tends
  to zero with the strip height, uniformly in the cleanup mesh. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace SLEExactGauge

private lemma int_filtered_row_sum (α r η : ℝ) (N : ℤ) :
    (∑ j∈(Finset.Icc 0 N).filter (fun j : ℤ => ((j:ℝ)+1/2)*r<η),
      (((j:ℝ)+1/2)*r)^(-α)) =
      ∑ j∈(Finset.range (N+1).toNat).filter (fun j : ℕ => ((j:ℝ)+1/2)*r<η),
        (((j:ℝ)+1/2)*r)^(-α) := by
  rw [Finset.sum_filter, Int.Icc_eq_finset_map,Finset.sum_map,Finset.sum_filter]
  simp only [sub_zero,Function.Embedding.trans_apply,addLeftEmbedding_apply,zero_add,
    Nat.castEmbedding_apply,Int.cast_natCast]

theorem prescribed_grid_lower_strip_sum (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α<1)
    {R r η : ℝ} (hR : 0 ≤ R) (hr : 0<r) (hr1 : r ≤ 1) (hη : 0 ≤ η) (K : Set ℂ) :
    (∑ ij∈(prescribedGridIndex R r K).filter
      (fun ij => (prescribedGridCenter r ij).im<η), (prescribedGridCenter r ij).im^(-α)) ≤
      ((2*R+5)*((2:ℝ)^α/(1-α)))*r^(-2:ℝ)*(η+r)^(1-α) := by
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
  have hcol : (2*(N:ℝ)+1) ≤ (2*R+5)/r := by
    apply (le_div_iff₀ hr).mpr
    have h := mul_le_mul_of_nonneg_right hN hr.le
    rw [add_mul,div_mul_cancel₀ _ hr.ne'] at h
    nlinarith
  have hsub : (prescribedGridIndex R r K).filter
      (fun ij => (prescribedGridCenter r ij).im<η) ⊆
      (Finset.Icc (-N) N) ×ˢ ((Finset.Icc 0 N).filter
        (fun j : ℤ => ((j:ℝ)+1/2)*r<η)) := by
    intro ij hij
    obtain ⟨hgrid,hstrip⟩ := Finset.mem_filter.mp hij
    have hmem := Finset.mem_filter.mp hgrid
    have hi := Finset.mem_product.mp hmem.1
    apply Finset.mem_product.mpr
    refine ⟨hi.1,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨hmem.2.1,(Finset.mem_Icc.mp hi.2).2⟩,?_⟩⟩
    rwa [← (prescribedGrid_center_height hr hgrid).1]
  have hrows : (∑ j∈(Finset.Icc 0 N).filter
      (fun j : ℤ => ((j:ℝ)+1/2)*r<η), (((j:ℝ)+1/2)*r)^(-α)) ≤
      ((2:ℝ)^α/(1-α))*r⁻¹*(η+r)^(1-α) := by
    rw [int_filtered_row_sum]
    exact half_integer_lower_strip_sum α hα0 hα1 hr hη _
  calc
    _ = ∑ ij∈(prescribedGridIndex R r K).filter
        (fun ij => (prescribedGridCenter r ij).im<η), (((ij.2:ℝ)+1/2)*r)^(-α) := by
      apply Finset.sum_congr rfl
      intro ij hij
      rw [(prescribedGrid_center_height hr (Finset.mem_filter.mp hij).1).1]
    _ ≤ ∑ ij∈(Finset.Icc (-N) N) ×ˢ ((Finset.Icc 0 N).filter
        (fun j : ℤ => ((j:ℝ)+1/2)*r<η)), (((ij.2:ℝ)+1/2)*r)^(-α) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ij hij _ =>
        Real.rpow_nonneg (mul_nonneg (by
          have hj := (Finset.mem_Icc.mp
            (Finset.mem_filter.mp (Finset.mem_product.mp hij).2).1).1
          have hjR : (0:ℝ) ≤ ij.2 := by exact_mod_cast hj
          linarith) hr.le) _)
    _ = (2*(N:ℝ)+1)*∑ j∈(Finset.Icc 0 N).filter
        (fun j : ℤ => ((j:ℝ)+1/2)*r<η), (((j:ℝ)+1/2)*r)^(-α) := by
      have hcard : ((Finset.Icc (-N) N).card:ℝ)=2*(N:ℝ)+1 := by
        have hh := Int.card_Icc_of_le (a := -N) (b := N) (by omega)
        have hh' : ((Finset.Icc (-N) N).card:ℝ)=(N:ℝ)+1-(-(N:ℝ)) := by exact_mod_cast hh
        linarith
      rw [Finset.sum_product]
      dsimp only [Prod.snd]
      rw [Finset.sum_const,nsmul_eq_mul,hcard]
    _ ≤ ((2*R+5)/r)*(((2:ℝ)^α/(1-α))*r⁻¹*(η+r)^(1-α)) :=
      mul_le_mul hcol hrows (Finset.sum_nonneg (fun j hj => Real.rpow_nonneg (by
        have hjR : (0:ℝ) ≤ j := by
          exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).1
        positivity) _)) (by positivity)
    _ = _ := by
      rw [Real.rpow_neg hr.le,Real.rpow_two]
      field_simp

end SLEExactGauge

end

end OAI
