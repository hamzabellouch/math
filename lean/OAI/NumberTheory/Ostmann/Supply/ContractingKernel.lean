import OAI.NumberTheory.Ostmann.Supply.KernelScalarBounds
import OAI.NumberTheory.Ostmann.Supply.LocalBlockBound
import OAI.NumberTheory.Ostmann.Supply.UnitKernelMean

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [NeZero p]

theorem sparseKernel_pencil_bounds {u v : ℂ} (hu : ‖u‖ ≤ 103/100) (hv : ‖v‖ ≤ 103/100) :
    ‖(u+v)*(sparseKernelScale:ℂ)‖ ≤ 9/5 ∧ ‖u*v‖ ≤ 2 := by
  have hsum := norm_add_le u v
  have ht : ‖(sparseKernelScale:ℂ)‖ = 17/20 := by norm_num [sparseKernelScale]
  rw [norm_mul,ht,norm_mul]
  constructor
  · nlinarith
  · nlinarith [norm_nonneg u,norm_nonneg v,mul_nonneg
      (show 0 ≤ (103/100:ℝ)-‖u‖ by linarith) (show 0 ≤ (103/100:ℝ)-‖v‖ by linarith)]

theorem local_sparse_block_estimate (S : Finset (ZMod p)) (u v : ℂ)
    (hp : 1000 ≤ p) (hlo : (1/3:ℝ) ≤ density S) (hhi : density S ≤ 2/3)
    (hg : gamma S ≤ supplyEpsilon^2) (hu : ‖u‖ ≤ 103/100) (hv : ‖v‖ ≤ 103/100) :
    ‖localKernelBlock S sparseKernelScale u v‖  ≤ 
      ‖kernelScalar S sparseKernelScale u v‖+100*(8*supplyEpsilon/Real.sqrt p)^2 := by
  have hε : 0 ≤ supplyEpsilon := supplyEpsilon_pos.le
  have hpr : (1000:ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0:ℝ)<p := by linarith
  have hroot : 0 ≤ Real.sqrt (p:ℝ) := Real.sqrt_nonneg _
  have hc := sparseKernel_pencil_bounds hu hv
  have hc2 : ‖(u+v)*(sparseKernelScale:ℂ)‖ ≤ 2 := by linarith [hc.1]
  have hB := squaredSparseKernel_norm_le S hlo hhi supplyEpsilon_pos.le supplyEpsilon_le_one hg
  have heval : ‖(u+v)*(sparseKernelScale:ℂ)‖*(2*supplyEpsilon/Real.sqrt p)+
      ‖u*v‖*((2/Real.sqrt p)*‖squaredLocalKernelOperator S sparseKernelScale‖)  ≤ 
      8*supplyEpsilon/Real.sqrt p := by
    calc
      _  ≤  2*(2*supplyEpsilon/Real.sqrt p)+2*((2/Real.sqrt p)*supplyEpsilon) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hc2 (by positivity))
          (mul_le_mul hc.2 (mul_le_mul_of_nonneg_left hB (by positivity))
            (mul_nonneg (by positivity) (norm_nonneg _)) (by norm_num))
      _ = _ := by ring
  have hd : ‖(u+v)*(sparseKernelScale:ℂ)‖/2+
      ‖u*v‖*‖squaredLocalKernelOperator S sparseKernelScale‖  ≤  (95/100:ℝ) := by
    have hh := add_le_add (div_le_div_of_nonneg_right hc.1 (by norm_num : (0:ℝ) ≤ 2))
      (mul_le_mul hc.2 hB (norm_nonneg _) (by norm_num))
    norm_num [supplyEpsilon] at hh ⊢
    linarith
  have hdist : ‖kernelScalar S sparseKernelScale u v-1‖  ≤  (2+8*supplyEpsilon)/(p:ℝ) := by
    apply (kernelScalar_distance_le S sparseKernelScale u v hlo hhi).trans
    calc
      _  ≤  2/(p:ℝ)+2*(4*supplyEpsilon/(p:ℝ)) := by
        exact add_le_add (div_le_div_of_nonneg_right hc2 hp0.le)
          (mul_le_mul hc.2 (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hB (by norm_num)) hp0.le)
            (by positivity) (by norm_num))
      _ = _ := by ring
  have hsabs := (abs_norm_sub_norm_le (kernelScalar S sparseKernelScale u v) (1:ℂ)).trans hdist
  simp only [norm_one] at hsabs
  have hs := scalar_near_one (s := ‖kernelScalar S sparseKernelScale u v‖) hpr (by linarith [(abs_le.mp hsabs).1])
    (by linarith [(abs_le.mp hsabs).2])
  have he := local_error_small hpr
  exact localBlock_norm_le S Sᶜ (localKernelOperator S sparseKernelScale u v)
    hs.1 hs.2 he.1 he.2 (by norm_num) (by norm_num) le_rfl
    (fun z => (localKernel_row_bound S sparseKernelScale u v hlo hhi supplyEpsilon_pos.le hg z).trans
      (mul_le_mul_of_nonneg_right heval (norm_nonneg _)))
    ((localKernel_column_bound S sparseKernelScale u v hlo hhi supplyEpsilon_pos.le hg).trans heval)
    (fun z => (localKernel_lower_bound S sparseKernelScale u v z).trans
      (mul_le_mul_of_nonneg_right hd (norm_nonneg _)))

theorem local_sparse_uniform_bound (S : Finset (ZMod p)) (u v : ℂ)
    (hp : 1000 ≤ p) (hlo : (1/3:ℝ) ≤ density S) (hhi : density S ≤ 2/3)
    (hg : gamma S ≤ supplyEpsilon^2) (hu : ‖u‖ ≤ 103/100) (hv : ‖v‖ ≤ 103/100) :
    ‖localKernelBlock S sparseKernelScale u v‖  ≤  1+3/(p:ℝ) := by
  have hε : 0 ≤ supplyEpsilon := supplyEpsilon_pos.le
  have hpr : (1000:ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0:ℝ)<p := by linarith
  have hc := sparseKernel_pencil_bounds hu hv
  have hB := squaredSparseKernel_norm_le S hlo hhi supplyEpsilon_pos.le supplyEpsilon_le_one hg
  have hdist : ‖kernelScalar S sparseKernelScale u v-1‖  ≤  (2+8*supplyEpsilon)/(p:ℝ) := by
    apply (kernelScalar_distance_le S sparseKernelScale u v hlo hhi).trans
    have h1 := div_le_div_of_nonneg_right (show ‖(u+v)*(sparseKernelScale:ℂ)‖ ≤ 2 by linarith [hc.1]) hp0.le
    have h2 := mul_le_mul hc.2 (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hB (by norm_num : (0:ℝ) ≤ 4)) hp0.le) (by positivity) (by norm_num)
    have hh := add_le_add h1 h2
    convert hh using 1
    ring
  have hs := (norm_sub_norm_le (kernelScalar S sparseKernelScale u v) (1:ℂ)).trans hdist
  simp only [norm_one] at hs
  exact local_uniform_norm_numerical (s := ‖kernelScalar S sparseKernelScale u v‖) hpr (by linarith)
    (local_sparse_block_estimate S u v hp hlo hhi hg hu hv)

theorem local_sparse_contraction (S : Finset (ZMod p))
    (hp : 1000 ≤ p) (hlo : (1/3:ℝ) ≤ density S) (hhi : density S ≤ 2/3)
    (hg : gamma S ≤ supplyEpsilon^2) :
    ‖localKernelBlock S sparseKernelScale 1 1‖  ≤ 
      unitKernelMean S sparseKernelScale*(1-(8/5:ℝ)/(p:ℝ)) := by
  have hε : 0 ≤ supplyEpsilon := supplyEpsilon_pos.le
  have hpr : (1000:ℝ) ≤ p := by exact_mod_cast hp
  have hnorm := local_sparse_block_estimate S 1 1 hp hlo hhi hg (by norm_num) (by norm_num)
  have hs := sparseKernel_scalar_one_le S (by omega) hlo hhi supplyEpsilon_pos.le supplyEpsilon_le_one hg
  have hn := local_strict_norm_numerical hpr hs hnorm
  exact local_relative_norm_numerical hpr hn (sparse_unitKernelMean_lower S (by omega)
    sparseKernelScale_nonneg sparseKernelScale_le_one (by linarith) (by linarith) hg)

end Ostmann.Supply

end

end OAI
