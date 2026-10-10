import OAI.Analysis.LipschitzHilbert.Estimates.FiniteSmoothProduct

namespace OAI

/-! The actual smooth Carleson product estimate on every finite frequency
range. The countable spatial partition introduces no constant or cutoff. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace LipschitzHilbert.PacketRepresentation
open DyadicLineGrid

theorem smooth_carleson_estimate (I : Finset ℤ)
    (f : ℝ → ℂ) (hfm : Measurable f) (B : ℝ) (hB : 0≤B) (hfb : ∀ x, ‖f x‖≤B)
    (ratio : ℝ) (hratio : 0<ratio) (h : SchwartzMap ℝ ℂ) :
    (∑ k∈I, ∫⁻ x,
      ENNReal.ofReal (‖lineConvolution (lineProjectionKernel dyadicDifference (scale k)
        (scale_pos _).ne') f x‖^2)*
      ENNReal.ofReal (‖lineConvolution (lineProjectionKernel reassemblyLow (ratio*scale k)
        (mul_pos hratio (scale_pos _)).ne') h x‖^2))≤
      ENNReal.ofReal (dyadicCarlesonConstant*B^2)*
        ENNReal.ofReal (lineCellMaximalConstant reassemblyLow ratio)^2*
        ENNReal.ofReal (36*(∫ x, ‖h x‖^2)) := by
  classical
  let w := fun k x =>
    ENNReal.ofReal (‖lineConvolution (lineProjectionKernel dyadicDifference (scale k)
      (scale_pos _).ne') f x‖^2)*
    ENNReal.ofReal (‖lineConvolution (lineProjectionKernel reassemblyLow (ratio*scale k)
      (mul_pos hratio (scale_pos _)).ne') h x‖^2)
  let a := fun p : I×ℤ => ∫⁻ x in cell 0 p.1.val p.2, w p.1.val x
  have hfinite (F : Finset (I×ℤ)) : (∑ p∈F, a p)≤
      ENNReal.ofReal (dyadicCarlesonConstant*B^2)*
        ENNReal.ofReal (lineCellMaximalConstant reassemblyLow ratio)^2*
        ENNReal.ofReal (36*(∫ x, ‖h x‖^2)) := by
    have hh := finite_smooth_product 0 (fun p : F => p.val.1.val) (fun p : F => p.val.2)
      (by
        intro p q hp hq
        apply Subtype.ext
        exact Prod.ext (Subtype.ext hp) hq)
      f hfm B hB hfb ratio hratio h
    change (∑ p : F, a p.val)≤_ at hh
    rw [Finset.sum_coe_sort] at hh
    exact hh
  have hall : (∑' p, a p)≤
      ENNReal.ofReal (dyadicCarlesonConstant*B^2)*
        ENNReal.ofReal (lineCellMaximalConstant reassemblyLow ratio)^2*
        ENNReal.ofReal (36*(∫ x, ‖h x‖^2)) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    exact iSup_le hfinite
  have hpartition (k : ℤ) : (∑' j, ∫⁻ x in cell 0 k j, w k x)=∫⁻ x, w k x := by
    have he : (⋃ j : ℤ, cell 0 k j)=(univ : Set ℝ) := by
      apply Set.eq_univ_of_forall
      intro x
      exact mem_iUnion.mpr ⟨index 0 k x,mem_index_cell 0 k x⟩
    have hh := lintegral_iUnion (μ:=volume) (f:=w k) (cell_measurable 0 k)
      (fun i j hij => cells_disjoint 0 k hij)
    rw [he,Measure.restrict_univ] at hh
    exact hh.symm
  have he : (∑' p, a p)=∑ k∈I, ∫⁻ x, w k x := by
    rw [ENNReal.tsum_prod']
    simp only [a,hpartition,tsum_fintype]
    exact Finset.sum_coe_sort I (fun k => ∫⁻ x, w k x)
  rw [he] at hall
  exact hall

end LipschitzHilbert.PacketRepresentation

end

end OAI
