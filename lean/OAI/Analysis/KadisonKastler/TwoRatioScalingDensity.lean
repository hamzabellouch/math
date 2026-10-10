import OAI.Analysis.KadisonKastler.TwoRatioScalingWords
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

namespace OAI

/-! # Density of the constructed state-scaling ratios -/

namespace KadisonKastler

open Generator Filter
open scoped Topology

noncomputable section

theorem exists_twoRatio_scale_near {r ε : ℝ} (hr : 0 < r) (hr1 : r < 1) (hε : 0 < ε) :
    ∃ k l : ℤ, fixedProductLambda^k * fixedProductMu^l < 1 ∧
      dist (fixedProductLambda^k * fixedProductMu^l) r < ε := by
  have hd : Dense (AddSubgroup.closure
      ({Real.log fixedProductLambda,Real.log fixedProductMu} : Set ℝ) : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.mpr fixedProduct_log_ratio_irrational
  let U : Set ℝ := Real.exp ⁻¹' Metric.ball r ε ∩ Set.Iio 0
  have hU : IsOpen U :=
    (Metric.isOpen_ball.preimage Real.continuous_exp).inter isOpen_Iio
  have hmem : Real.log r ∈ U := by
    refine ⟨?_,Real.log_neg hr hr1⟩
    change dist (Real.exp (Real.log r)) r < ε
    simpa only [Real.exp_log hr,dist_self] using hε
  obtain ⟨x,hxU,hx⟩ := hd.inter_open_nonempty U hU ⟨Real.log r,hmem⟩
  obtain ⟨k,l,hkl⟩ := AddSubgroup.mem_closure_pair.mp hx
  have hp : 0 < fixedProductLambda^k * fixedProductMu^l :=
    mul_pos (zpow_pos fixedProductLambda_pos k) (zpow_pos fixedProductMu_pos l)
  have he : Real.log (fixedProductLambda^k * fixedProductMu^l)=x := by
    rw [Real.log_mul (ne_of_gt (zpow_pos fixedProductLambda_pos k))
      (ne_of_gt (zpow_pos fixedProductMu_pos l)),Real.log_zpow,Real.log_zpow]
    simpa only [zsmul_eq_mul] using hkl
  have hv : fixedProductLambda^k * fixedProductMu^l=Real.exp x := by
    rw [← he,Real.exp_log hp]
  refine ⟨k,l,?_,?_⟩
  · rw [hv]
    exact Real.exp_lt_one_iff.mpr hxU.2
  · rw [hv]
    exact hxU.1

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

theorem PointedMatrixSites.exists_scaling_coisometry_near
    (S : PointedMatrixSites M Ω twoRatioSiteParameter)
    {r ε : ℝ} (hr : 0 < r) (hr1 : r < 1) (hε : 0 < ε) :
    ∃ (s : ℝ) (w : Algebra M),
      0 < s ∧ s < 1 ∧ dist s r < ε ∧ w*star w=1 ∧ StateScales M Ω s w.val := by
  obtain ⟨k,l,hs,hclose⟩ := exists_twoRatio_scale_near hr hr1 hε
  obtain ⟨w,hw,hscale⟩ := S.exists_twoRatio_scaling_coisometry k l hs.le
  exact ⟨_,w,mul_pos (zpow_pos fixedProductLambda_pos k) (zpow_pos fixedProductMu_pos l),
    hs,hclose,hw,hscale⟩

end

end KadisonKastler

end OAI
