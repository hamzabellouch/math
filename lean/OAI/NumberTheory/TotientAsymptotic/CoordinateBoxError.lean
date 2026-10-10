import OAI.NumberTheory.TotientAsymptotic.CoordinateCubeSize
import OAI.NumberTheory.TotientAsymptotic.UniformPrefactor

namespace OAI

/-! The relative affine box error vanishes uniformly away from the last
coordinates, even when the retained dimension varies. -/
noncomputable section
open scoped Topology
open Filter
namespace TotientAsymptotic

theorem coordinateCubeShift_natural_bound : ∃ C : ℝ,0 < C ∧
    ∀ (M N : ℕ) (j : Fin N),N ≤ M →
      coordinateCubeShift N j*rho^(M-(j.val+1)) ≤ C := by
  obtain ⟨A,hA,hbound⟩ := coordinateCubeShift_normalized_bound
  refine ⟨A/rho,div_pos hA rho_pos,?_⟩
  intro M N j hNM
  have he : N-j.val ≤ M-(j.val+1)+1 := by have := j.isLt; omega
  have hh := (mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one rho_pos.le rho_lt_one.le he)
    (coordinateCubeShift_nonneg N j)).trans (hbound N j)
  rw [pow_succ] at hh
  apply (le_div_iff₀ rho_pos).mpr
  simpa only [mul_assoc] using hh

theorem fordBandScale_scaled_lower : ∀ᶠ x : ℝ in atTop,
    ∀ i : ℕ,i < m x →
      (lam/2)*(m x-i:ℕ) ≤ fordBandScale x i*rho^(m x-i) := by
  filter_upwards [inverse_scale_bound,
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hB
  intro i hi
  have hm : (0:ℝ) < m x := by exact_mod_cast (show 0 < m x by omega)
  have hden : 0 < B x*rho^(m x) := mul_pos hB (pow_pos rho_pos _)
  have hb : (lam/2)*(m x:ℝ) ≤ B x*rho^(m x) := by
    have hh := (div_le_div_iff₀ hden lam_pos).mp hx
    nlinarith only [hh]
  have hb' : lam/2 ≤ B x*rho^(m x)/(m x:ℝ) := (le_div_iff₀ hm).mpr hb
  have he : fordBandScale x i*rho^(m x-i) =
      (B x*rho^(m x)/(m x:ℝ))*(m x-i:ℕ) := by
    unfold fordBandScale
    calc
      _ = B x*(rho^i*rho^(m x-i))*(1-(i:ℝ)/m x) := by ring
      _ = B x*rho^(m x)*(1-(i:ℝ)/m x) := by
        rw [←pow_add,Nat.add_sub_of_le hi.le]
      _ = _ := by
        rw [Nat.cast_sub hi.le]
        field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_right hb' (Nat.cast_nonneg _)

theorem coordinate_box_error_small {E : ℝ} (_hE : 0 < E) :
    ∀ᶠ P : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ (N : ℕ) (j : Fin N),N ≤ m x → P ≤ m x-(j.val+1) →
      ∀ κ : ℝ,0 ≤ κ → κ ≤ E →
        1+κ*coordinateCubeShift N j ≤ fordBandScale x (j.val+1)/100 := by
  obtain ⟨C,hC,hbound⟩ := coordinateCubeShift_natural_bound
  filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually
    (eventually_ge_atTop (200*(1+E*C)/lam)),eventually_ge_atTop (1:ℕ)] with P hP hP1
  filter_upwards [fordBandScale_scaled_lower] with x hx
  intro N j hNM hj κ hκ hκE
  have hjm : j.val+1 < m x := by have := j.isLt; omega
  have hh : (P:ℝ) ≤ (m x-(j.val+1):ℕ) := by exact_mod_cast hj
  have hbudget : 200*(1+E*C) ≤ lam*(m x-(j.val+1):ℕ) := by
    have ht := (div_le_iff₀ lam_pos).mp hP
    have hh' := mul_le_mul_of_nonneg_left hh lam_pos.le
    linarith only [ht,hh']
  have hpow : 0 < rho^(m x-(j.val+1)) := pow_pos rho_pos _
  have hprod := mul_le_mul_of_nonneg_left (hbound (m x) N j hNM) hκ
  have hright := mul_le_mul_of_nonneg_right hκE hC.le
  have hscale := hx (j.val+1) hjm
  have hp1 : rho^(m x-(j.val+1)) ≤ 1 := pow_le_one₀ rho_pos.le rho_lt_one.le
  apply (mul_le_mul_iff_left₀ hpow).mp
  nlinarith only [hprod,hright,hscale,hbudget,hp1]

end TotientAsymptotic

end

end OAI
