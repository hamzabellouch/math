import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.ModelCandidates
import OAI.Probability.SLEGauge.CandidateCover

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory Set Filter Finset
open scoped NNReal ENNReal Topology
namespace SLEExactGauge.CleanupCost
open BoundaryRows

lemma nat_mul_exp_neg_linear (c : ℝ) (hc : 0<c) :
    Tendsto (fun n : ℕ=>(n:ℝ)*Real.exp (-c*n)) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ=>c*(n:ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hc).mpr tendsto_natCast_atTop_atTop
  have hh := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp ht).const_mul c⁻¹
  simp only [Function.comp_def,pow_one,mul_zero] at hh
  convert hh using 1
  funext n
  rw [neg_mul,←mul_assoc,←mul_assoc,inv_mul_cancel₀ hc.ne',one_mul]

lemma nat_mul_exp_neg_two_pow :
    Tendsto (fun n : ℕ=>(n:ℝ)*Real.exp (-((2:ℝ)^n)/16)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n=>mul_nonneg (Nat.cast_nonneg n) (Real.exp_pos _).le)
    (g:=fun n : ℕ=>(n:ℝ)*Real.exp (-(1/16:ℝ)*n))
  · intro n
    have hn : (n:ℝ)≤(2:ℝ)^n := by exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
    exact Real.exp_le_exp.mpr (by linarith)
  · exact nat_mul_exp_neg_linear (1/16) (by norm_num)

lemma nat_mul_boundary_power {α : ℝ} (hα : α<1) (r : ℕ→ℝ)
    (hr : ∀n,0≤r n) (hsmall : ∀ᶠ n in atTop,r n≤Real.exp (-(n:ℝ)^2)) :
    Tendsto (fun n : ℕ=>(n:ℝ)*(Real.exp (-(n:ℝ))+r n)^(1-α)) atTop (𝓝 0) := by
  have hβ : 0<1-α := by linarith
  have hg : Tendsto (fun n : ℕ=>(2:ℝ)^(1-α)*((n:ℝ)*Real.exp (-(1-α)*n))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (nat_mul_exp_neg_linear (1-α) hβ).const_mul ((2:ℝ)^(1-α))
  apply squeeze_zero' (Eventually.of_forall (fun n=>mul_nonneg (Nat.cast_nonneg n)
    (Real.rpow_nonneg (add_nonneg (Real.exp_pos _).le (hr n)) _))) _ hg
  filter_upwards [hsmall,eventually_ge_atTop 1] with n hn hn1
  have hn1' : (1:ℝ)≤n := by exact_mod_cast hn1
  have hh : -(n:ℝ)^2≤-(n:ℝ) := by nlinarith
  have he : Real.exp (-(n:ℝ))+r n≤2*Real.exp (-(n:ℝ)) := by
    have hh' := Real.exp_le_exp.mpr hh
    linarith
  calc
    _ ≤ (n:ℝ)*(2*Real.exp (-(n:ℝ)))^(1-α) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (add_nonneg (Real.exp_pos _).le (hr n)) he hβ.le) (Nat.cast_nonneg n)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Real.exp_pos _).le,
        Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
      rw [show -(n:ℝ)*(1-α)=-(1-α)*(n:ℝ) by ring]
      ring

 

def envelope (α : ℝ) (r : ℕ→ℝ) (n : ℕ) : ℝ :=
  (n:ℝ)*Real.exp (-((2:ℝ)^n)/16)+(n:ℝ)*(Real.exp (-(n:ℝ))+r n)^(1-α)

lemma envelope_tendsto {α : ℝ} (hα : α<1) (r : ℕ→ℝ)
    (hr : ∀n,0≤r n) (hsmall : ∀ᶠ n in atTop,r n≤Real.exp (-(n:ℝ)^2)) :
    Tendsto (envelope α r) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ=>(n:ℝ)*Real.exp (-((2:ℝ)^n)/16) +
    (n:ℝ)*(Real.exp (-(n:ℝ))+r n)^(1-α)) atTop (𝓝 0)
  simpa only [zero_add] using
    nat_mul_exp_neg_two_pow.add (nat_mul_boundary_power hα r hr hsmall)

lemma envelope_uniform_bound {α : ℝ} (hα : α<1) (r : ℕ→ℝ)
    (hr : ∀n,0≤r n) (hsmall : ∀ᶠ n in atTop,r n≤Real.exp (-(n:ℝ)^2)) :
    ∃C : ℝ,0<C ∧ ∀n,envelope α r n≤C := by
  obtain ⟨C,hC,hbound⟩ := (Metric.isBounded_range_of_tendsto (envelope α r)
    (envelope_tendsto hα r hr hsmall)).exists_pos_norm_le
  exact ⟨C,hC,fun n=>(le_abs_self _).trans (hbound _ (mem_range_self n))⟩

 

lemma two_region_cell_sum (α r : ℝ) (hα : 0≤α) (hα1 : α<1) (hr : 0<r)
    (M N : ℕ) (X Y ε A q : ℝ)
    (hX : (M:ℝ)*r≤X) (hY : (N:ℝ)*r≤Y)
    (hε : 0≤ε) (hA : 0≤A) (hq : 0≤q) (P : ℕ→ℕ→ℝ)
    (hnear : ∀i∈Finset.range M,∀j∈Finset.range N,
      ((j:ℝ)+1/2)*r<ε → P i j≤A*r^α*(((j:ℝ)+1/2)*r)^(-α))
    (hfar : ∀i∈Finset.range M,∀j∈Finset.range N,
      ε≤((j:ℝ)+1/2)*r → P i j≤A*r^α*(((j:ℝ)+1/2)*r)^(-α)*q) :
    (∑i∈Finset.range M,∑j∈Finset.range N,P i j)≤
      A*r^α*(rowConstant α*X/r^2)*(q*Y^(1-α)+(ε+r)^(1-α)) := by
  classical
  let y : ℕ→ℝ := fun j=>((j:ℝ)+1/2)*r
  have hn (j : ℕ) : 0≤A*r^α*(y j)^(-α) := by dsimp [y]; positivity
  have hb (i : ℕ) (hi : i∈Finset.range M) (j : ℕ) (hj : j∈Finset.range N) :
      P i j≤A*r^α*((y j)^(-α)*q+(if y j<ε then (y j)^(-α) else 0)) := by
    by_cases hy : y j<ε
    · rw [ite_eq_left hy,mul_add]
      exact (hnear i hi j hj hy).trans (le_add_of_nonneg_left (by positivity))
    · rw [ite_eq_right hy,add_zero,←mul_assoc]
      exact hfar i hi j hj (le_of_not_gt hy)
  have hsplit : (∑i∈Finset.range M,∑j∈Finset.range N,
        A*r^α*((y j)^(-α)*q+(if y j<ε then (y j)^(-α) else 0)))=
      A*r^α*(q*(∑i∈Finset.range M,∑j∈Finset.range N,(y j)^(-α))+
        (∑i∈Finset.range M,∑j∈(Finset.range N).filter (fun j=>y j<ε),(y j)^(-α))) := by
    simp_rw [Finset.sum_filter,mul_add,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]
    ring
  have hh1 := rectangle_rows α hα hα1 r hr M N X Y hX hY
  have hh2 := rectangle_truncated_rows α hα hα1 r hr M N X ε hX hε
  calc
    _ ≤ ∑i∈Finset.range M,∑j∈Finset.range N,
        A*r^α*((y j)^(-α)*q+(if y j<ε then (y j)^(-α) else 0)) := by
      exact Finset.sum_le_sum (fun i hi=>Finset.sum_le_sum (hb i hi))
    _ = _ := hsplit
    _ ≤ A*r^α*(q*(rowConstant α*X*Y^(1-α)/r^2)+
        rowConstant α*X*(ε+r)^(1-α)/r^2) :=
      mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hh1 hq) hh2)
        (mul_nonneg hA (Real.rpow_nonneg hr.le _))
    _ = _ := by ring

 

theorem cleanup_sum (d α r : ℝ) (hα : 0≤α) (hα1 : α<1) (hr : 0<r) (hdα : d+α=2)
    (M N n : ℕ) (X Y ε A q : ℝ)
    (hX : (M:ℝ)*r≤X) (hY : (N:ℝ)*r≤Y)
    (hε : 0≤ε) (hA : 0≤A) (hq : 0≤q) (P : ℕ→ℕ→ℝ)
    (hnear : ∀i∈Finset.range M,∀j∈Finset.range N,
      ((j:ℝ)+1/2)*r<ε → P i j≤A*r^α*(((j:ℝ)+1/2)*r)^(-α))
    (hfar : ∀i∈Finset.range M,∀j∈Finset.range N,
      ε≤((j:ℝ)+1/2)*r → P i j≤A*r^α*(((j:ℝ)+1/2)*r)^(-α)*q) :
    (∑i∈Finset.range M,∑j∈Finset.range N,2*(n:ℝ)*r^d*P i j)≤
      2*(n:ℝ)*A*rowConstant α*X*(q*Y^(1-α)+(ε+r)^(1-α)) := by
  simp_rw [←Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left
    (two_region_cell_sum α r hα hα1 hr M N X Y ε A q hX hY hε hA hq P hnear hfar)
    (show 0≤2*(n:ℝ)*r^d by positivity)
  refine hh.trans_eq ?_
  have hcancel : r^d*r^α/r^2=1 := by
    rw [←Real.rpow_add hr,hdα,Real.rpow_two,div_self (pow_ne_zero 2 hr.ne')]
  calc
    _ = 2*(n:ℝ)*A*rowConstant α*X*(q*Y^(1-α)+(ε+r)^(1-α))*(r^d*r^α/r^2) := by ring
    _ = _ := by rw [hcancel,mul_one]

end SLEExactGauge.CleanupCost
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped NNReal ENNReal Topology Classical
namespace SLEExactGauge.CenteredMoments
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator
open LoewnerRestart CompactSequence MomentBatches BoxGrid

namespace CenteredMomentModel
variable {κ a : ℝ} {ha : 1/4<a} {W : Measure GDriver} (M : CenteredMomentModel κ a ha W)

def cleanupCost (m : ℝ) (n : ℕ) (b : GDriver) : ℝ≥0∞ :=
  ∑k : Cells m (M.finalRadius n),
    (M.cleanupEvent (center m (M.finalRadius n) k.1 k.2) n).indicator
      (fun _=>ENNReal.ofReal (4*(n:ℝ)*(M.finalRadius n)^(2-alpha a))) b

lemma cleanupCost_measurable (m : ℝ) (n : ℕ) : Measurable (M.cleanupCost m n) := by
  apply Finset.measurable_sum
  intro k hk
  exact measurable_const.indicator (M.cleanupEvent_measurable _
    (center_im_pos m _ (M.finalRadius_pos n) _ _) n)

lemma cleanupCost_integral [IsProbabilityMeasure W] (m : ℝ) (n : ℕ) :
    (∫⁻b,M.cleanupCost m n b∂W)=ENNReal.ofReal
      (∑i∈Finset.range (columns m (M.finalRadius n)),
       ∑j∈Finset.range (rows m (M.finalRadius n)),
        4*(n:ℝ)*(M.finalRadius n)^(2-alpha a)*
          W.real (M.cleanupEvent (center m (M.finalRadius n) i j) n)) := by
  have hr := M.finalRadius_pos n
  simp only [cleanupCost]
  rw [lintegral_finsetSum]
  · simp_rw [lintegral_indicator_const (M.cleanupEvent_measurable _
      (center_im_pos m _ hr _ _) n)]
    rw [Fintype.sum_prod_type]

    simp_rw [←Fin.sum_univ_eq_sum_range]
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _=>Finset.sum_nonneg (fun j _=>by positivity))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _=>by positivity)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [ENNReal.ofReal_mul (show 0≤4*(n:ℝ)*(M.finalRadius n)^(2-alpha a) by positivity),Measure.real,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  · intro k hk
    exact measurable_const.indicator (M.cleanupEvent_measurable _
      (center_im_pos m _ hr _ _) n)

 
lemma cleanupCost_integral_bound [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : GDriver)=>b.1 t) W)
    (m : ℝ) (hm : 0≤ m) (n : ℕ) (hr : BatchReady a n)
    (hr1 : M.finalRadius n≤1) :
    (∫⁻b,M.cleanupCost m n b∂W) ≤ ENNReal.ofReal
      (4*(n:ℝ)*M.cellConstant*BoundaryRows.rowConstant (alpha a)*(2*m+1)*
        (Real.exp (-((2:ℝ)^n/16))*(m+1)^(1-alpha a)+
          (Real.exp (-(n:ℝ))+M.finalRadius n)^(1-alpha a))) := by
  rw [M.cleanupCost_integral]
  apply ENNReal.ofReal_le_ofReal
  have hsum := CleanupCost.cleanup_sum (2-alpha a) (alpha a) (M.finalRadius n)
    (alpha_pos ha).le (alpha_lt_one (ha:=ha)) (M.finalRadius_pos n) (by ring)
    (columns m (M.finalRadius n)) (rows m (M.finalRadius n)) n
    (2*m+1) (m+1) (Real.exp (-(n:ℝ))) M.cellConstant (Real.exp (-((2:ℝ)^n/16)))
    ((columns_width m _ hm (M.finalRadius_pos n)).trans (by linarith))
    ((rows_height m _ hm (M.finalRadius_pos n)).trans (by linarith))
    (Real.exp_pos _).le M.cellConstant_pos.le (Real.exp_pos _).le
    (fun i j=>W.real (M.cleanupEvent (center m (M.finalRadius n) i j) n))
    (fun i _ j _ _=>M.cleanup_near hW _ (center_im_pos m _ (M.finalRadius_pos n) i j) n)
    (fun i _ j _ hy=>M.cleanup_far hW _ (center_im_pos m _ (M.finalRadius_pos n) i j) n hr hy)
  have hh := mul_le_mul_of_nonneg_left hsum (show (0:ℝ)≤2 by norm_num)
  simp_rw [Finset.mul_sum] at hh
  calc
    _ = ∑i∈Finset.range (columns m (M.finalRadius n)),
       ∑j∈Finset.range (rows m (M.finalRadius n)),
       2*(2*(n:ℝ)*(M.finalRadius n)^(2-alpha a)*W.real
         (M.cleanupEvent (center m (M.finalRadius n) i j) n)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ _ := hh.trans_eq (by ring)

lemma cleanupCost_uniform_bound [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : GDriver)=>b.1 t) W)
    (m : ℝ) (hm : 0≤ m) :
    ∃B : ℝ≥0∞,B<∞ ∧ ∀ᶠ n in atTop,(∫⁻b,M.cleanupCost m n b∂W)≤B := by
  obtain ⟨C,hC,hbound⟩ := CleanupCost.envelope_uniform_bound (alpha_lt_one (ha:=ha))
    M.finalRadius (fun n=>(M.finalRadius_pos n).le) (Eventually.of_forall M.finalRadius_le)
  let D := 4*M.cellConstant*BoundaryRows.rowConstant (alpha a)*(2*m+1)*max 1 ((m+1)^(1-alpha a))
  refine ⟨ENNReal.ofReal (D*C),ENNReal.ofReal_lt_top,?_⟩
  filter_upwards [eventually_batchReady a (by linarith)] with n hn
  have hs : M.finalRadius n≤1 := (M.finalRadius_le n).trans
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _)))
  apply (M.cleanupCost_integral_bound hW m hm n hn hs).trans
  apply ENNReal.ofReal_le_ofReal
  have hrow := BoundaryRows.rowConstant_pos (alpha_lt_one (ha:=ha))
  have hD : 0≤D := by
    dsimp [D]
    have := M.cellConstant_pos
    positivity
  have henv : 4*(n:ℝ)*M.cellConstant*BoundaryRows.rowConstant (alpha a)*(2*m+1)*
        (Real.exp (-((2:ℝ)^n/16))*(m+1)^(1-alpha a)+
          (Real.exp (-(n:ℝ))+M.finalRadius n)^(1-alpha a)) ≤
      D*CleanupCost.envelope (alpha a) M.finalRadius n := by
    have hy : (m+1)^(1-alpha a) ≤ max 1 ((m+1)^(1-alpha a)) := le_max_right ..
    have hu : (Real.exp (-(n:ℝ))+M.finalRadius n)^(1-alpha a) ≤
        max 1 ((m+1)^(1-alpha a))*(Real.exp (-(n:ℝ))+M.finalRadius n)^(1-alpha a) := by
      exact le_mul_of_one_le_left (Real.rpow_nonneg
        (add_nonneg (Real.exp_pos _).le (M.finalRadius_pos n).le) _) (le_max_left ..)
    have hh := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hy (Real.exp_pos (-((2:ℝ)^n/16))).le) hu)
      (show 0≤4*(n:ℝ)*M.cellConstant*BoundaryRows.rowConstant (alpha a)*(2*m+1) by
        have := M.cellConstant_pos; positivity)
    exact hh.trans_eq (by dsimp [D,CleanupCost.envelope]; rw [neg_div]; ring)
  exact henv.trans (mul_le_mul_of_nonneg_left (hbound n) hD)

end CenteredMomentModel
end SLEExactGauge.CenteredMoments
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped NNReal ENNReal Topology Classical
namespace SLEExactGauge.CenteredMoments
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator
open LoewnerRestart CompactSequence MomentBatches BoxGrid Deterministic CandidateCover

def allFrontiers (a : ℝ) (b : GDriver) : Set ℂ :=
  ⋃T : ℝ≥0,frontier {z | alive a b.1 T z}

lemma exp_neg_nat_sq_tendsto :
    Tendsto (fun n : ℕ=>Real.exp (-(n:ℝ)^2)) atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ=>(n:ℝ)^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2:ℕ)≠0)).comp tendsto_natCast_atTop_atTop
  exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hs)

namespace CenteredMomentModel
variable {κ a : ℝ} {ha : 1/4<a} {W : Measure GDriver} (M : CenteredMomentModel κ a ha W)

abbrev GridCells (m : ℝ) (n : ℕ) := Cells m (M.finalRadius n)
abbrev CandidateIndices (m : ℝ) (n : ℕ) := M.GridCells m n × Fin (M.testCount n)
abbrev CoverIndices (m : ℝ) (n : ℕ) := M.CandidateIndices m n ⊕ M.GridCells m n

def gridCenter (m : ℝ) (n : ℕ) (k : M.GridCells m n) : ℂ :=
  center m (M.finalRadius n) k.1 k.2

def costBound (m : ℝ) (n : ℕ) (b : GDriver) : ℝ≥0∞ :=
  ENNReal.ofReal ((6*M.candidateScale)^2/M.candidateLower)*M.spatialMass b (region m)+
    M.cleanupCost m n b

lemma costBound_measurable (m : ℝ) (n : ℕ) : Measurable (M.costBound m n) :=
  (measurable_const.mul (M.spatialMass_measurable _ (region_measurable m))).add
    (M.cleanupCost_measurable m n)

lemma costBound_uniform [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : GDriver)=>b.1 t) W)
    (m : ℝ) (hm : 0≤ m) :
    ∃B : ℝ≥0∞,B<∞ ∧ ∀ᶠ n in atTop,(∫⁻b,M.costBound m n b∂W)≤B := by
  obtain ⟨C,hC,hbound⟩ := M.cleanupCost_uniform_bound hW m hm
  have hmean : (∫⁻b,M.spatialMass b (region m)∂W)<∞ := by
    simp_rw [M.spatialMass_apply _ _ (region_measurable m),preimage_region]
    exact (BoundaryGreen.canonical_rectangle_mean M.canonical _ _ _ (by linarith)).2.1
  refine ⟨ENNReal.ofReal ((6*M.candidateScale)^2/M.candidateLower)*
    (∫⁻b,M.spatialMass b (region m)∂W)+C,
    ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmean,hC⟩,?_⟩
  filter_upwards [hbound] with n hn
  simp only [costBound]
  have hf : Measurable (fun b=>ENNReal.ofReal ((6*M.candidateScale)^2/M.candidateLower)*
      M.spatialMass b (region m)) := measurable_const.mul (M.spatialMass_measurable _ (region_measurable m))
  rw [lintegral_add_left hf,
    lintegral_const_mul _ (M.spatialMass_measurable _ (region_measurable m))]
  exact add_le_add le_rfl hn

lemma finalRadius_le_one (n : ℕ) : M.finalRadius n≤1 :=
  (M.finalRadius_le n).trans (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _)))

lemma gauge_admissible_actual : Target.IsHausdorffGauge (M.gauge (2-alpha a)) :=
  M.gauge_admissible (by linarith [alpha_lt_one (ha:=ha)]) (by linarith [alpha_pos ha])

lemma cleanup_ball_cost (n : ℕ) (hn : 0<n) (z : ℂ) :
    diameterCost (M.gauge (2-alpha a)) (ediam (closedBall z (M.finalRadius n))) ≤
      ENNReal.ofReal (4*(n:ℝ)*(M.finalRadius n)^(2-alpha a)) := by
  apply (diameterCost_le_radius M.gauge_admissible_actual
    (by have := M.finalRadius_pos n; positivity)
    (ediam_closedBall_le_of_nonneg z (M.finalRadius n))).trans
  apply ENNReal.ofReal_le_ofReal
  rw [M.gauge_eq_quadratic]
  have h := quadratic_multiple_le (2-alpha a) M.entryThreshold M.entryRadius
    (fun i=>(M.entryThreshold_pos i).le) M.entryRadius_pos 2 (by norm_num)
    (cleanupIndex (moment M.law sequenceMassReal) n hn)
  rw [M.cleanup_radius n hn,show M.entryThreshold (cleanupIndex (moment M.law sequenceMassReal) n hn)=
    (n:ℝ) from cleanup_threshold ..] at h
  norm_num only [show (2:ℝ)^2=4 by norm_num] at h
  exact h

 

lemma finite_cover (m : ℝ) (hm : 0≤ m) (n : ℕ) (hn : 0<n)
    (hsmall : M.candidateScale*Real.exp (-(n:ℝ)^2)≤1) :
    ∀ᵐ b∂W,∃U : M.CoverIndices m n→Set ℂ,
      (∀i,ediam (U i)≤ENNReal.ofReal (6*M.candidateScale*Real.exp (-(n:ℝ)^2))) ∧
      allFrontiers a b∩box m ⊆ ⋃i,U i ∧
      (∑i,diameterCost (M.gauge (2-alpha a)) (ediam (U i)))≤M.costBound m n b := by
  have hcover : ∀ᵐ b∂W,∀k : M.GridCells m n,∀T : ℝ≥0,∀v∈closedBall (M.gridCenter m n k) (M.finalRadius n),
      v∈frontier {z | alive a b.1 T z} →
        (∃i<M.testCount n,M.candidate n i (M.gridCenter m n k) b) ∨
          b∈M.cleanupEvent (M.gridCenter m n k) n :=
    ae_all_iff.mpr (fun k=>M.cleanup_covers _
      (center_im_pos m _ (M.finalRadius_pos n) _ _) n)
  filter_upwards [hcover] with b hb
  let s : Finset (M.CandidateIndices m n) := Finset.univ.filter
    (fun j=>M.candidate n j.2 (M.gridCenter m n j.1) b)
  let e : M.CandidateIndices m n→M.Entries := fun j=>M.testIndex n hn j.2 j.2.2
  have her (j : M.CandidateIndices m n) : M.entryRadius (e j)=batchRadius a (M.batchLevel n) n j.2 := rfl
  have het (j : M.CandidateIndices m n) : M.entryThreshold (e j)=M.testThreshold n j.2 :=
    M.testIndex_threshold n hn j.2 j.2.2
  have hrbound (j : M.CandidateIndices m n) : M.entryRadius (e j)≤Real.exp (-(n:ℝ)^2) := by
    rw [her,←batchRadius_zero a (M.batchLevel n) n]
    exact batchRadius_antitone a (by linarith) _ _ (Nat.zero_le _)
  have hrball (j : M.CandidateIndices m n) : M.candidateScale*M.entryRadius (e j)≤1 :=
    (mul_le_mul_of_nonneg_left (hrbound j) M.candidateScale_pos.le).trans hsmall
  have hqual (j : M.CandidateIndices m n) (hj : j∈s) :
      ENNReal.ofReal (M.candidateLower*M.entryThreshold (e j)*(M.entryRadius (e j))^(2-alpha a)) ≤
        M.spatialMass b (closedBall (M.gridCenter m n j.1) (M.candidateScale*M.entryRadius (e j))∩univ) := by
    rw [inter_univ,her,het]
    exact (Finset.mem_filter.mp hj).2
  obtain ⟨t,ht,hd,hcov,hcost⟩ := finite_quadratic_candidates (2-alpha a) M.entryThreshold M.entryRadius
    (fun j=>(M.entryThreshold_pos j).le) M.entryRadius_pos M.gauge_admissible_actual
    (M.spatialMass b) s (fun j=>M.gridCenter m n j.1) e univ (region m) MeasurableSet.univ
    M.candidateScale M.candidateLower M.candidateScale_one M.candidateLower_pos
    (fun j _=>(inter_subset_left.trans (ball_subset_region m _ _ hm (M.finalRadius_pos n)
      (M.finalRadius_le_one n) (hrball j) j.1))) hqual
  let U : M.CoverIndices m n→Set ℂ := Sum.elim
    (fun j=>if j∈t then closedBall (M.gridCenter m n j.1) (3*(M.candidateScale*M.entryRadius (e j))) else ∅)
    (fun k=>if b∈M.cleanupEvent (M.gridCenter m n k) n then
      closedBall (M.gridCenter m n k) (M.finalRadius n) else ∅)
  have hδ : 0≤6*M.candidateScale*Real.exp (-(n:ℝ)^2) := by have := M.candidateScale_pos; positivity
  refine ⟨U,?_,?_,?_⟩
  · intro i
    cases i with
    | inl j =>
      dsimp [U]
      split_ifs with hj
      · apply (ediam_closedBall_le_of_nonneg _ _).trans
        apply ENNReal.ofReal_le_ofReal
        nlinarith [mul_le_mul_of_nonneg_left (hrbound j) M.candidateScale_pos.le]
      · simp
    | inr k =>
      dsimp [U]
      split_ifs
      · apply (ediam_closedBall_le_of_nonneg _ _).trans
        apply ENNReal.ofReal_le_ofReal
        have he := Real.exp_pos (-(n:ℝ)^2)
        nlinarith [M.finalRadius_le n,M.candidateScale_one]
      · simp
  · intro v hv
    obtain ⟨T,hT⟩ := mem_iUnion.mp hv.1
    obtain ⟨k,hk⟩ := mem_iUnion.mp (covered m _ hm (M.finalRadius_pos n) hv.2)
    rcases hb k T v hk hT with hc | hc
    · obtain ⟨i,hi,hc⟩ := hc
      let j : M.CandidateIndices m n := (k,⟨i,hi⟩)
      have hjs : j∈s := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩
      obtain ⟨q,hqt,hq⟩ := hcov j hjs
      refine mem_iUnion.mpr ⟨Sum.inl q,?_⟩
      change v∈if q∈t then _ else ∅
      rw [ite_eq_left hqt]
      apply hq
      apply closedBall_subset_closedBall (ε₁:=M.finalRadius n) (ε₂:=M.candidateScale*M.entryRadius (e j)) _ hk
      have hri : M.finalRadius n≤M.entryRadius (e j) :=
        batchRadius_antitone a (by linarith) _ _ hi.le
      exact hri.trans (le_mul_of_one_le_left (M.entryRadius_pos _).le M.candidateScale_one)
    · refine mem_iUnion.mpr ⟨Sum.inr k,?_⟩
      change v∈if b∈M.cleanupEvent (M.gridCenter m n k) n then _ else ∅
      rw [ite_eq_left hc]
      exact hk
  · rw [Fintype.sum_sum_type]
    unfold costBound
    apply add_le_add
    · change (∑j,diameterCost (M.gauge (2-alpha a)) (ediam
        (if j∈t then closedBall (M.gridCenter m n j.1) (3*(M.candidateScale*M.entryRadius (e j))) else ∅))) ≤ _
      simp only [apply_ite,ediam_empty,diameterCost_zero M.gauge_admissible_actual.2.2.1,
        ←Finset.sum_filter]
      simpa only [Finset.filter_mem_eq_inter,Finset.univ_inter,M.gauge_eq_quadratic] using hcost
    · change (∑k,diameterCost (M.gauge (2-alpha a)) (ediam
        (if b∈M.cleanupEvent (M.gridCenter m n k) n then closedBall (M.gridCenter m n k) (M.finalRadius n) else ∅))) ≤ _
      unfold cleanupCost
      apply Finset.sum_le_sum
      intro k hk
      change diameterCost (M.gauge (2-alpha a)) (ediam (if b∈M.cleanupEvent (M.gridCenter m n k) n then
        closedBall (M.gridCenter m n k) (M.finalRadius n) else ∅)) ≤
        (M.cleanupEvent (M.gridCenter m n k) n).indicator
          (fun _=>ENNReal.ofReal (4*(n:ℝ)*(M.finalRadius n)^(2-alpha a))) b
      by_cases hc : b∈M.cleanupEvent (M.gridCenter m n k) n
      · simp only [ite_eq_left hc,indicator_of_mem hc]
        exact M.cleanup_ball_cost n hn _
      · simp only [ite_eq_right hc,ediam_empty,diameterCost_zero M.gauge_admissible_actual.2.2.1]
        exact bot_le

end CenteredMomentModel
end SLEExactGauge.CenteredMoments
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped NNReal ENNReal Topology
namespace SLEExactGauge.CenteredMoments
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator
open LoewnerRestart CompactSequence MomentBatches BoxGrid Deterministic

namespace CenteredMomentModel
variable {κ a : ℝ} {ha : 1/4<a} {W : Measure GDriver} (M : CenteredMomentModel κ a ha W)

 

theorem frontier_box_finite [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : GDriver)=>b.1 t) W)
    (m : ℝ) (hm : 0≤ m) :
    ∀ᵐ b∂W,Target.hausdorff (M.gauge (2-alpha a)) (allFrontiers a b∩box m)<∞ := by
  obtain ⟨B,hB,hbound⟩ := M.costBound_uniform hW m hm
  have hfin := (CoverCost.liminf_cost_bound W (M.costBound m)
    (M.costBound_measurable m) B hB hbound).2.2
  have hc : ∀ᵐ b∂W,∀n : ℕ,0<n → M.candidateScale*Real.exp (-(n:ℝ)^2)≤1 →
      ∃U : M.CoverIndices m n→Set ℂ,
        (∀i,ediam (U i)≤ENNReal.ofReal (6*M.candidateScale*Real.exp (-(n:ℝ)^2))) ∧
        allFrontiers a b∩box m⊆⋃i,U i ∧
        (∑i,diameterCost (M.gauge (2-alpha a)) (ediam (U i)))≤M.costBound m n b := by
    apply ae_all_iff.mpr
    intro n
    by_cases hn : 0<n
    · by_cases hs : M.candidateScale*Real.exp (-(n:ℝ)^2)≤1
      · exact (M.finite_cover m hm n hn hs).mono (fun b hb _ _=>hb)
      · exact Eventually.of_forall (fun _ _ h=>(hs h).elim)
    · exact Eventually.of_forall (fun _ h _=>(hn h).elim)
  have he : Tendsto (fun n : ℕ=>M.candidateScale*Real.exp (-(n:ℝ)^2)) atTop (𝓝 0) := by
    simpa only [mul_zero] using exp_neg_nat_sq_tendsto.const_mul M.candidateScale
  have hsmall : ∀ᶠ n : ℕ in atTop,M.candidateScale*Real.exp (-(n:ℝ)^2)≤1 :=
    (he.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))).mono (fun _ h=>h.le)
  have hδ : Tendsto (fun n : ℕ=>ENNReal.ofReal (6*M.candidateScale*Real.exp (-(n:ℝ)^2))) atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ=>6*M.candidateScale*Real.exp (-(n:ℝ)^2)) atTop (𝓝 0) := by
      simpa only [mul_zero] using exp_neg_nat_sq_tendsto.const_mul (6*M.candidateScale)
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hh
  filter_upwards [hc,hfin] with b hb hf
  apply lt_of_le_of_lt _ hf
  apply CoverCost.hausdorff_le_liminf_of_exists
    (ι:=fun n=>M.CoverIndices m n) _ _ _ hδ _
  filter_upwards [hsmall,eventually_gt_atTop (0:ℕ)] with n hs hn
  obtain ⟨U,hd,hcov,hcost⟩ := hb n hn hs
  exact ⟨U,hd,hcov,by simpa only [tsum_fintype] using hcost⟩

 
theorem frontier_boxes_finite [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : GDriver)=>b.1 t) W) :
    ∀ᵐ b∂W,∀m : ℕ,Target.hausdorff (M.gauge (2-alpha a)) (allFrontiers a b∩box m)<∞ :=
  ae_all_iff.mpr (fun m=>M.frontier_box_finite hW m (Nat.cast_nonneg m))

end CenteredMomentModel
end SLEExactGauge.CenteredMoments
end
end
 

 
section
 

noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
namespace SLEExactGauge.CenteredMoments
open FlowIdentification TraceMassIntegration

 
def dimension (κ : ℝ) : ℝ := 1+κ/8

lemma parameterDimension_pos {κ : ℝ} (hκ : 0<κ) : 0<dimension κ := by
  unfold dimension
  linarith

lemma dimension_lt_two {κ : ℝ} (hκ8 : κ<8) : dimension κ<2 := by
  unfold dimension
  linarith

 

theorem exists_parameter_moment_gauge (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8) :
    ∃h : ℝ→ℝ, Target.IsHausdorffGauge h ∧
      (∀C r : ℝ, 1≤C → 0≤r → h (C*r)≤C^2*h r) ∧
      ∀W : Target.WienerLaw, Target.IsWiener W →
        ∃M : CenteredMomentModel κ (Target.a κ) (a_gt_quarter hκ hκ8)
          (W.map driverHomeomorph), h=M.gauge (dimension κ) := by
  classical
  by_cases h : ∃W : Target.WienerLaw, Target.IsWiener W
  · obtain ⟨W,hW⟩ := h
    obtain ⟨M⟩ := actual_centered_moment_model κ hκ hκ8 W hW
    refine ⟨M.gauge (dimension κ),
      M.gauge_admissible (parameterDimension_pos hκ) (dimension_lt_two hκ8).le,
      M.gauge_doubling (parameterDimension_pos hκ) (dimension_lt_two hκ8).le,?_⟩
    intro V hV
    have e : V=W := BrownianLaw.evaluation_law_unique hV hW
    subst V
    exact ⟨M,rfl⟩
  · refine ⟨id,⟨continuous_id.continuousOn,monotone_id.monotoneOn _,rfl,fun _ hr=>hr⟩,?_,?_⟩
    · intro C r hC hr
      change C*r ≤ C^2*r
      exact mul_le_mul_of_nonneg_right (by nlinarith : C≤C^2) hr
    · intro W hW
      exact (h ⟨W,hW⟩).elim

 
def parameterMomentGauge (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8) : ℝ→ℝ :=
  Classical.choose (exists_parameter_moment_gauge κ hκ hκ8)

lemma parameterMomentGauge_admissible (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8) :
    Target.IsHausdorffGauge (parameterMomentGauge κ hκ hκ8) :=
  (Classical.choose_spec (exists_parameter_moment_gauge κ hκ hκ8)).1

lemma parameterMomentGauge_doubling (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8)
    (C r : ℝ) (hC : 1≤C) (hr : 0≤r) :
    parameterMomentGauge κ hκ hκ8 (C*r) ≤ C^2*parameterMomentGauge κ hκ hκ8 r :=
  (Classical.choose_spec (exists_parameter_moment_gauge κ hκ hκ8)).2.1 C r hC hr

lemma parameterMomentGauge_model (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8)
    (W : Target.WienerLaw) (hW : Target.IsWiener W) :
    ∃M : CenteredMomentModel κ (Target.a κ) (a_gt_quarter hκ hκ8)
      (W.map driverHomeomorph), parameterMomentGauge κ hκ hκ8=M.gauge (dimension κ) :=
  (Classical.choose_spec (exists_parameter_moment_gauge κ hκ hκ8)).2.2 W hW

end SLEExactGauge.CenteredMoments
end
end

end OAI
