import OAI.NumberTheory.Jacobsthal.Estimates.BoundaryRadialCoefficient
import OAI.NumberTheory.Jacobsthal.Estimates.CorrectionStateSections
import OAI.NumberTheory.Jacobsthal.Estimates.CorrectionUniformTruncation

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Set _root_.MeasureTheory
open scoped Interval
namespace ErdosBoundaryIntegral
open ErdosContinuousAnomaly

theorem even_ratio_integral (r : ℝ) : (∫ _t : ℝ in 2..r/2,1)=r/2-2 := by simp

theorem odd_ratio_integral {r : ℝ} (hr : 2 ≤ r) :
    (∫ t : ℝ in 1..r/2,(1-(t^2)⁻¹))=r/2+2/r-2 := by
  have hab : (1:ℝ) ≤ r/2 := by linarith
  have hn : ∀ t ∈ uIcc (1:ℝ) (r/2),t ≠ 0 := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have hh := ht.1
    linarith
  have hd : ∀ t ∈ uIcc (1:ℝ) (r/2),
      HasDerivAt (fun x : ℝ => x+x⁻¹) (1-(t^2)⁻¹) t := by
    intro t ht
    convert! (hasDerivAt_id t).add (hasDerivAt_inv (hn t ht)) using 1
  have hc : ContinuousOn (fun t : ℝ => 1-(t^2)⁻¹) (uIcc (1:ℝ) (r/2)) :=
    continuousOn_const.sub ((continuous_id.pow 2).continuousOn.inv₀ (by
      intro t ht; exact pow_ne_zero 2 (hn t ht)))
  have hi := hc.intervalIntegrable (μ := volume)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [h]
  simp only [inv_one]
  have hr0 : r ≠ 0 := by linarith
  field_simp
  ring

theorem nested_ratio_coefficient_eq_twice_I :
    ((∫ r in Ioi 4,r*continuousAnomaly .even r*(∫ _t : ℝ in 2..r/2,1))-
      ∫ r in Ioi 2,r*continuousAnomaly .odd r*(∫ t : ℝ in 1..r/2,(1-(t^2)⁻¹)))=
        2*signedCoefficientI := by
  have he : (∫ r in Ioi 4,r*continuousAnomaly .even r*(∫ _t : ℝ in 2..r/2,1))=
      ∫ r in Ioi 4,r*(r/2-2)*continuousAnomaly .even r := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r _hr
    dsimp only
    rw [even_ratio_integral]
    ring
  have ho : (∫ r in Ioi 2,r*continuousAnomaly .odd r*(∫ t : ℝ in 1..r/2,(1-(t^2)⁻¹)))=
      ∫ r in Ioi 2,(r^2/2-2*r+2)*continuousAnomaly .odd r := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hr2 : 2 < r := hr
    dsimp only
    rw [odd_ratio_integral hr2.le]
    have hr0 : r ≠ 0 := by linarith
    field_simp
    ring
  rw [he,ho]
  exact radial_coefficient_eq_twice_I

end ErdosBoundaryIntegral

end

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology ENNReal
namespace ErdosCorrectionLimit
open ErdosContinuousAnomaly ErdosBoundaryIntegral
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PrimeOccupationDensity
open NumberTheoryLean.OccupationDensityIntegral
open Erdos970Dependency.InvariantCostBound

theorem anomaly_moment_integrable (i : Side) (n : ℕ) :
    IntegrableOn (fun r : ℝ => r^n*continuousAnomaly i r) (Ioi 2) := by
  obtain ⟨C,c,_w,hC,hc,_hw,_hd,ha⟩ := common_anomaly_exponential
  have hg : IntegrableOn (fun r : ℝ => r^n*Real.exp (-c*r)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n:ℝ)) (p := 1)
      (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) hc
    simpa only [Real.rpow_natCast,Real.rpow_one] using! h
  have hm : ContinuousOn (fun r : ℝ => r^n*continuousAnomaly i r) (Ioi 2) :=
    (continuous_id.pow n).continuousOn.mul ((continuousAnomaly_continuousOn i).mono Ioi_subset_Ici_self)
  apply ((hg.mono_set (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤2))).const_mul C).mono'
    (hm.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hr2 : 2 < r := hr
  change ‖r^n*continuousAnomaly i r‖ ≤ C*(r^n*Real.exp (-c*r))
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg (by linarith) n)]
  have hb := mul_le_mul_of_nonneg_left (ha r hr2.le i) (pow_nonneg (by linarith : 0≤r) n)
  nlinarith

theorem exp_cutoff_integral {a : ℝ} (ha : 0 < a) (g : ℝ → ℝ) :
    ((∫ u : ℝ,if a < Real.exp u then Real.exp u*g (Real.exp u) else 0)=∫ r in Ioi a,g r) ∧
    (Integrable (fun u : ℝ => if a < Real.exp u then Real.exp u*g (Real.exp u) else 0) ↔
      IntegrableOn g (Ioi a)) := by
  have him : Real.exp '' Ioi (Real.log a)=Ioi a := by
    ext r
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact (Real.log_lt_iff_lt_exp ha).mp hu
    · intro hr
      have hra : a < r := hr
      have hr0 : 0 < r := ha.trans hra
      exact ⟨Real.log r,Real.log_lt_log ha hra,Real.exp_log hr0⟩
  have hd : ∀ u ∈ Ioi (Real.log a), HasDerivWithinAt Real.exp (Real.exp u) (Ioi (Real.log a)) u :=
    fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt
  have hf : (fun u : ℝ => if a < Real.exp u then Real.exp u*g (Real.exp u) else 0)=
      (Ioi (Real.log a)).indicator (fun u => Real.exp u*g (Real.exp u)) := by
    funext u
    simp only [indicator_apply,mem_Ioi,Real.log_lt_iff_lt_exp ha]
  constructor
  · rw [hf,integral_indicator measurableSet_Ioi]
    have hh := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd Real.exp_injective.injOn g
    simpa only [him,abs_of_pos (Real.exp_pos _),smul_eq_mul] using! hh.symm
  · rw [hf,integrable_indicator_iff measurableSet_Ioi]
    have hh := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hd Real.exp_injective.injOn g
    simpa only [him,abs_of_pos (Real.exp_pos _),smul_eq_mul] using! hh.symm

noncomputable def evenRadial (r : ℝ) : ℝ := r*(r/2-2)*continuousAnomaly .even r
noncomputable def oddRadial (r : ℝ) : ℝ := (r^2/2-2*r+2)*continuousAnomaly .odd r

theorem radial_parts_integrable : IntegrableOn evenRadial (Ioi 4) ∧ IntegrableOn oddRadial (Ioi 2) := by
  have h1 (i : Side) : IntegrableOn (fun r : ℝ => r*continuousAnomaly i r) (Ioi 2) := by
    simpa only [pow_one] using anomaly_moment_integrable i 1
  have h0 (i : Side) : IntegrableOn (continuousAnomaly i) (Ioi 2) := by
    simpa only [pow_zero,one_mul] using anomaly_moment_integrable i 0
  constructor
  · have hh : IntegrableOn (fun r : ℝ => (r^2*continuousAnomaly .even r)/2-2*(r*continuousAnomaly .even r)) (Ioi 2) :=
      ((anomaly_moment_integrable .even 2).div_const 2).sub ((h1 .even).const_mul 2)
    apply (hh.mono_set (Ioi_subset_Ioi (by norm_num : (2:ℝ)≤4))).congr_fun _ measurableSet_Ioi
    intro r _
    dsimp only [evenRadial]
    ring
  · have hh : IntegrableOn (fun r : ℝ => ((r^2*continuousAnomaly .odd r)/2-2*(r*continuousAnomaly .odd r))+2*continuousAnomaly .odd r) (Ioi 2) :=
      (((anomaly_moment_integrable .odd 2).div_const 2).sub ((h1 .odd).const_mul 2)).add ((h0 .odd).const_mul 2)
    apply hh.congr_fun _ measurableSet_Ioi
    intro r _
    dsimp only [oddRadial]
    ring

theorem full_limiting_integral_eq :
    (∫ x,rawTest fullAnomalyTest x ∂limitingMeasure 2)=2*signedCoefficientI/costMass := by
  have he := exp_cutoff_integral (by norm_num : (0:ℝ)<4) evenRadial
  have ho := exp_cutoff_integral (by norm_num : (0:ℝ)<2) oddRadial
  have hie := he.2.mpr radial_parts_integrable.1
  have hio := ho.2.mpr radial_parts_integrable.2
  rw [full_limiting_integral_fubini]
  simp_rw [fullWeighted_section_radial]
  have hfun : (fun u : ℝ => Real.exp u/costMass*radialNumerator (Real.exp u))=
      (fun u => ((if 4 < Real.exp u then Real.exp u*evenRadial (Real.exp u) else 0)-
        (if 2 < Real.exp u then Real.exp u*oddRadial (Real.exp u) else 0))/costMass) := by
    funext u
    unfold radialNumerator evenRadial oddRadial
    split_ifs <;> ring
  rw [hfun,integral_div,integral_sub hie hio,he.1,ho.1]
  have hh : (∫ r in Ioi 4,evenRadial r)-(∫ r in Ioi 2,oddRadial r)=2*signedCoefficientI :=
    radial_coefficient_eq_twice_I
  rw [hh]

end ErdosCorrectionLimit

end

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open scoped Topology
namespace ErdosCorrectionLimit
open ErdosCorrectionOccupation ErdosContinuousAnomaly ErdosBoundaryIntegral
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.PrimeHistories
open NumberTheoryLean.CompactLogOccupationTest NumberTheoryLean.NormalizedOccupationLimit
open NumberTheoryLean.PrimeBinMembership
open NumberTheoryLean.SourceNodeCoordinates NumberTheoryLean.SourceLowRemoval
open Erdos970Dependency.InvariantCostBound

theorem compact_invariant_coefficient_tendsto :
    Tendsto (fun K : ℝ => invariantAverage (arrivalTest 2 (compactAnomalyTest K))) atTop
      (𝓝 (2*signedCoefficientI/costMass)) := by
  simpa only [full_limiting_integral_eq] using compact_invariant_tendsto

theorem full_continuous_correction_limit (d eps : ℝ) (hd : 0 < d) (heps : 0 < eps) :
    ∃ B₀ w₀ : ℝ,0 < B₀ ∧ 1 < w₀ ∧ ∀ B w : ℝ,B₀ ≤ B → w₀ ≤ w →
      Real.log B ≤ d*Real.log w → ∀ start : Node,
        start.side=.even → 199/100 ≤ start.ratio → start.ratio ≤ 23/10 →
        Consistent start → start.cutoff=B →
        |(start.gap^2/weight start.side start.ratio)*continuousBoundaryCorrection w 2 start-
          2*signedCoefficientI/costMass| ≤ eps := by
  have he3 : 0 < eps/3 := by linarith
  obtain ⟨Kmin,hKmin⟩ := eventually_atTop.mp
    (compact_invariant_coefficient_tendsto.eventually
      (Metric.ball_mem_nhds (2*signedCoefficientI/costMass) he3))
  obtain ⟨K,BT,wT,hK,hKK,hBT,hwT,hT⟩ :=
    uniform_compact_correction_above Kmin 2 d (eps/(3*scaleConstant))
      le_rfl hd (div_pos heps (mul_pos (by norm_num) scaleConstant_pos))
  obtain ⟨BF,wF,hBF,hwF,hF⟩ := fixed_compact_correction_limit K 2 d (eps/3) hK le_rfl hd he3
  refine ⟨max BT BF,max wT wF,hBT.trans_le (le_max_left _ _),hwT.trans_le (le_max_left _ _),?_⟩
  intro B w hB hw hcomp start hi h199 h23 hcons hcut
  have hBT' : BT ≤ B := (le_max_left _ _).trans hB
  have hBF' : BF ≤ B := (le_max_right _ _).trans hB
  have hwT' : wT ≤ w := (le_max_left _ _).trans hw
  have hwF' : wF ≤ w := (le_max_right _ _).trans hw
  have hBpos : 0 < B := hBT.trans_le hBT'
  have ht := hT B w hBT' hwT' hcomp start hi h199 h23 hcons hcut
  have hf := hF B w hBF' hwF' hcomp start hi h199 h23 hcons hcut
  have hk : |invariantAverage (arrivalTest 2 (compactAnomalyTest K))-2*signedCoefficientI/costMass| < eps/3 := by
    simpa only [Metric.mem_ball,Real.dist_eq] using hKmin K hKK
  have hs : Valid start.side start.ratio := by rw [hi]; change 198/100 ≤ start.ratio; linarith
  have hn : 0 ≤ start.gap^2/weight start.side start.ratio := div_nonneg (sq_nonneg _) (weight_pos hs).le
  have hscale := node_scale_upper hBpos start hi h199 h23 hcons hcut
  have herr : |(start.gap^2/weight start.side start.ratio)*
      (continuousBoundaryCorrection w 2 start-compactCorrection K w 2 start)| ≤ eps/3 := by
    rw [abs_mul,abs_of_nonneg hn]
    have hh := mul_le_mul_of_nonneg_right hscale
      (abs_nonneg (continuousBoundaryCorrection w 2 start-compactCorrection K w 2 start))
    have ht' := mul_le_mul_of_nonneg_left ht scaleConstant_pos.le
    have hcancel : scaleConstant*(eps/(3*scaleConstant))=eps/3 := by
      field_simp [scaleConstant_pos.ne']
    rw [hcancel] at ht'
    nlinarith
  have hsum := abs_add_le ((start.gap^2/weight start.side start.ratio)*
    (continuousBoundaryCorrection w 2 start-compactCorrection K w 2 start))
    ((start.gap^2/weight start.side start.ratio)*compactCorrection K w 2 start-
      invariantAverage (arrivalTest 2 (compactAnomalyTest K)))
  have hsum' := abs_add_le
    (((start.gap^2/weight start.side start.ratio)*
      (continuousBoundaryCorrection w 2 start-compactCorrection K w 2 start))+
      ((start.gap^2/weight start.side start.ratio)*compactCorrection K w 2 start-
        invariantAverage (arrivalTest 2 (compactAnomalyTest K))))
    (invariantAverage (arrivalTest 2 (compactAnomalyTest K))-2*signedCoefficientI/costMass)
  have heq : ((start.gap^2/weight start.side start.ratio)*
      (continuousBoundaryCorrection w 2 start-compactCorrection K w 2 start))+
      ((start.gap^2/weight start.side start.ratio)*compactCorrection K w 2 start-
        invariantAverage (arrivalTest 2 (compactAnomalyTest K)))+
      (invariantAverage (arrivalTest 2 (compactAnomalyTest K))-2*signedCoefficientI/costMass)=
      (start.gap^2/weight start.side start.ratio)*continuousBoundaryCorrection w 2 start-
        2*signedCoefficientI/costMass := by ring
  rw [heq] at hsum'
  linarith

end ErdosCorrectionLimit

end

end Erdos970

end OAI
