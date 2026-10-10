import OAI.NumberTheory.TotientAsymptotic.CoordinateEnlargement
import OAI.NumberTheory.TotientAsymptotic.UnbandedGridVolume

namespace OAI

/-! The affine normalization has a dimension-independent volume cost. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace TotientAsymptotic

theorem coordinateEnlargement_product_bound : ∃ E : ℝ,0 < E ∧
    ∀ M N : ℕ,N ≤ M → (∏ i : Fin N,coordinateEnlargement M N i) ≤ E := by
  let E := Real.exp (∑' n : ℕ,(n:ℝ)*simplexBoxError 0 n)
  refine ⟨E,Real.exp_pos _,?_⟩
  intro M N hNM
  have hh := reverse_enlargement_jacobian (m:=M) (P:=M-N) (Nat.sub_le _ _)
    (simplexBoxError 0) (simplexBoxError_nonneg (by norm_num))
    (summable_simplexBoxError_weighted 0)
  rw [Nat.sub_sub_self hNM] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  have hs := summable_simplexBoxError_weighted 0
  have he := hs.sum_add_tsum_nat_add (M-N)
  have hn : 0 ≤ ∑ n∈Finset.range (M-N),(n:ℝ)*simplexBoxError 0 n :=
    Finset.sum_nonneg (fun n _ => mul_nonneg (Nat.cast_nonneg _)
      (simplexBoxError_nonneg (by norm_num) _))
  have ht : (∑' n : ℕ,((n+(M-N):ℕ):ℝ)*simplexBoxError 0 (n+(M-N))) ≤ 
      ∑' n : ℕ,(n:ℝ)*simplexBoxError 0 n := by linarith only [he,hn]
  simpa only [Nat.add_comm] using ht

theorem fixed_coordinate_grid_prefactor : ∃ C : ℝ,0 < C ∧
    ∀ᶠ x : ℝ in atTop,∀ N : ℕ,0 < N → N ≤ m x →
      (∏ i : Fin N,coordinateEnlargement (m x) N i)*
        (volume (prefixRegion N (B x+prefixCubeCost N) 0 0)).toReal ≤ C*G x N := by
  obtain ⟨E,hE,hprod⟩ := coordinateEnlargement_product_bound
  obtain ⟨A,hA,hcost⟩ := prefixCubeCost_relative_bound
  refine ⟨E*Real.exp A,mul_pos hE (Real.exp_pos _),?_⟩
  filter_upwards [hcost,B_tendsto.eventually (eventually_gt_atTop (0:ℝ))] with x hx hB
  intro N hN hNm
  have hBN : 0 ≤ B x+prefixCubeCost N := add_nonneg hB.le (prefixCubeCost_nonneg N)
  have hden : 0 < ((N.factorial:ℝ)*∏ i : Fin N,g (i.val+1)) :=
    mul_pos (by positivity) (Finset.prod_pos (fun i _ => g_pos _))
  have hvolume : (volume (prefixRegion N (B x+prefixCubeCost N) 0 0)).toReal =
      (B x+prefixCubeCost N)^N/((N.factorial:ℝ)*∏ i : Fin N,g (i.val+1)) := by
    rw [volume_prefixRegion_explicit N hN]
    simp only [Pi.zero_apply,mul_zero,Finset.sum_const_zero,sub_zero,max_eq_left hBN,
      ENNReal.toReal_ofReal (div_nonneg (pow_nonneg hBN _) hden.le)]
  have hratio : (N:ℝ)*prefixCubeCost N/B x ≤ A :=
    (hx N hNm).trans (mul_le_of_le_one_right hA.le (pow_le_one₀ rho_pos.le rho_lt_one.le))
  have hpower := (add_pow_le_exp_ratio hB (prefixCubeCost_nonneg N) N).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hratio) (pow_nonneg hB.le N))
  rw [hvolume]
  calc
    _ ≤ E*(Real.exp A*(B x)^N/((N.factorial:ℝ)*∏ i : Fin N,g (i.val+1))) :=
      mul_le_mul (hprod (m x) N hNm) (div_le_div_of_nonneg_right hpower hden.le)
        (div_nonneg (pow_nonneg hBN _) hden.le) hE.le
    _ = _ := by rw [G,prod_fin_shifted N g]; ring

end TotientAsymptotic

end

end OAI
