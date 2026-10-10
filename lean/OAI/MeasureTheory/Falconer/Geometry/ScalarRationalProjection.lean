import OAI.MeasureTheory.Falconer.Estimates.ScalarCoefficientExpressions

namespace OAI

/-! Fixed rational coefficients have small projections under small
 doubling, by inclusion in an actual repeated sumset. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_reciprocal_integer_projection {δ K : ℝ} (hδ : 0 < δ)
    (X : Finset ℝ) (hX : X.Nonempty)
    (hdoubling : ((scalarCells δ (X+X)).card:ℝ) ≤ K*(scalarCells δ X).card)
    (m : ℕ) (hm : 0 < m) :
    ((scalarCells δ (X+X.image (fun x => (m:ℝ)⁻¹*x))).card:ℝ) ≤
      5*(m+3:ℝ)*(2*K)^(m+1)*(scalarCells δ X).card := by
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hsub : X+X.image (fun x => (m:ℝ)⁻¹*x) ⊆
      ((m+1) • X).image (fun x => (m:ℝ)⁻¹*x) := by
    intro z hz
    obtain ⟨x,hx,v,hv,rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    have hxsum : (m:ℝ)*x ∈ m • X := by
      simpa only [nsmul_eq_mul] using (Finset.nsmul_mem_nsmul (n := m) hx)
    refine Finset.mem_image.mpr ⟨(m:ℝ)*x+y,?_,?_⟩
    · rw [succ_nsmul]
      exact Finset.add_mem_add hxsum hy
    · rw [mul_add,← mul_assoc,inv_mul_cancel₀ hmR.ne',one_mul]
  have hsmall : |(m:ℝ)⁻¹| ≤ (1:ℝ) := by
    rw [abs_of_pos (inv_pos.mpr hmR)]
    exact (inv_le_one₀ hmR).2 (by exact_mod_cast hm)
  have hd := scalar_dilation_cells (c := (m:ℝ)⁻¹) hδ ((m+1) • X) 1 (by simpa only [Nat.cast_one] using hsmall)
  have hp := scalar_pluennecke δ X X hX hdoubling (m+1) 0
  simp only [zero_nsmul,sub_zero,add_zero,Nat.cast_zero,Nat.cast_add,Nat.cast_one] at hp
  have hs : ((scalarCells δ (X+X.image (fun x => (m:ℝ)⁻¹*x))).card:ℝ) ≤
      5*((scalarCells δ ((m+1) • X)).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card (Finset.image_subset_image hsub)).trans hd
  calc
    _ ≤ 5*((scalarCells δ ((m+1) • X)).card:ℝ) := hs
    _ ≤ 5*((m+1+2:ℝ)*(2*K)^(m+1)*(scalarCells δ X).card) :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = _ := by ring

end Falconer

end OAI
