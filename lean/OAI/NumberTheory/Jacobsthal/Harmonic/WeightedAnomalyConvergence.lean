import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import OAI.NumberTheory.Jacobsthal.Analysis.BoundaryProductLimit
import OAI.NumberTheory.Jacobsthal.Estimates.BoundaryReferenceConvergence
import OAI.NumberTheory.Jacobsthal.Estimates.OmissionTiltDecay

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.BoundaryAnomaly

open FinitePathGeometry ReferenceAdmission ReferencePruning
open VariablePrimeTilt OmissionTiltDecay ReferenceBenchmarkDecay

noncomputable def anomaly (w : ℝ) (i : Side) (r : ℝ) : ℝ :=
  referencePolynomial w (boundaryPrimes w) i r-
    survivorProduct (boundaryPrimes w)*benchmark i (r/2)

theorem boundary_product_bounds (w : ℝ) :
    0 ≤ survivorProduct (boundaryPrimes w) ∧ survivorProduct (boundaryPrimes w) ≤ 1 := by
  apply survivorProduct_bounds
  intro p hp
  obtain ⟨hpp,_⟩ := Finset.mem_filter.mp hp
  exact (by norm_num : 1 ≤ 2).trans (Nat.mem_primesLE.mp hpp).2.two_le

theorem anomaly_le_omission_and_benchmark (w r : ℝ) (i : Side) :
    |anomaly w i r| ≤ omissionMass w r i+|benchmark i (r/2)-1| := by
  have hp := boundary_product_bounds w
  have hd := boundary_reference_discrepancy w r i
  have he : anomaly w i r =
      (referencePolynomial w (boundaryPrimes w) i r-survivorProduct (boundaryPrimes w))-
        survivorProduct (boundaryPrimes w)*(benchmark i (r/2)-1) := by
    unfold anomaly
    ring
  rw [he]
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_of_nonneg hp.1]
  exact add_le_add hd (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hp.2 (abs_nonneg _))

theorem actual_boundary_anomaly_decay : ∃ C w₀ : ℝ,0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ r : ℝ,2 ≤ r → ∀ i : Side,
      |anomaly w i r| ≤ C*Real.exp (-(1/128:ℝ)*r*Real.log (r+2)) := by
  obtain ⟨CO,w₀,hCO,hw₀,hO⟩ := actual_omission_decay
  obtain ⟨CB,hCB,hB⟩ := boundary_benchmark_decay
  refine ⟨CO+CB,w₀,by positivity,hw₀,?_⟩
  intro w hw r hr i
  have hr0 : 0 ≤ r := by linarith
  have hl0 : 0 ≤ Real.log (r+2) := Real.log_nonneg (by linarith)
  have he : Real.exp (-(1/32:ℝ)*r*Real.log (r+2)) ≤
      Real.exp (-(1/128:ℝ)*r*Real.log (r+2)) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_nonneg hr0 hl0])
  calc
    _ ≤ omissionMass w r i+|benchmark i (r/2)-1| := anomaly_le_omission_and_benchmark w r i
    _ ≤ CO*Real.exp (-(1/32:ℝ)*r*Real.log (r+2))+
        CB*Real.exp (-(1/128:ℝ)*r*Real.log (r+2)) := add_le_add (hO w hw r hr i) (hB r hr i)
    _ ≤ CO*Real.exp (-(1/128:ℝ)*r*Real.log (r+2))+
        CB*Real.exp (-(1/128:ℝ)*r*Real.log (r+2)) :=
      add_le_add_left (mul_le_mul_of_nonneg_left he hCO.le) _
    _ = _ := by ring

theorem actual_boundary_anomaly_exponential : ∃ C c w₀ : ℝ,0 < C ∧ 0 < c ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ r : ℝ,2 ≤ r → ∀ i : Side,
      |anomaly w i r| ≤ C*Real.exp (-c*r) := by
  obtain ⟨C,w₀,hC,hw₀,h⟩ := actual_boundary_anomaly_decay
  refine ⟨C,Real.log 4/128,w₀,hC,div_pos (Real.log_pos (by norm_num)) (by norm_num),hw₀,?_⟩
  intro w hw r hr i
  have hl : Real.log 4 ≤ Real.log (r+2) := Real.log_le_log (by norm_num) (by linarith)
  apply (h w hw r hr i).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hl (by linarith : 0 ≤ r)]

end NumberTheoryLean.BoundaryAnomaly

end

section

open _root_.MeasureTheory _root_.Set _root_.Filter
open _root_.Erdos970.MeasureTheory _root_.Erdos970.Set _root_.Erdos970.Filter
open scoped Topology
namespace ErdosContinuousAnomaly
open ErdosContinuousBoundary
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.ReferenceAdmission
open NumberTheoryLean.ReferenceBenchmarkDecay NumberTheoryLean.BoundaryAnomaly
open NumberTheoryLean.LinearSieveFunctions NumberTheoryLean.BuchstabBridge

noncomputable def continuousAnomaly (i : Side) (r : ℝ) : ℝ :=
  boundaryReference i r 2-(1/2)*benchmark i (r/2)

theorem boundary_benchmark_bound (i : Side) {r : ℝ} (hr : 2 ≤ r) :
    |benchmark i (r/2)| ≤ sieveA+1 := by
  have hs : 1 ≤ r/2 := by linarith
  have h := (benchmark_deviation_le_gap i hs).trans (gap_le_constant hs)
  calc
    _ = |(benchmark i (r/2)-1)+1| := by congr 1; ring
    _ ≤ |benchmark i (r/2)-1|+|1| := abs_add_le _ _
    _ ≤ sieveA+1 := by simpa only [abs_one] using add_le_add h (le_refl (1:ℝ))

theorem continuousAnomaly_continuousOn (i : Side) : ContinuousOn (continuousAnomaly i) (Ici 2) := by
  intro r hr
  have hq : ContinuousAt (fun x : ℝ => boundaryReference i x 2) r :=
    ((boundaryReference_continuous i).comp (continuous_id.prodMk continuous_const)).continuousAt
  have hb : ContinuousAt (fun x : ℝ => benchmark i (x/2)) r := by
    cases i with
    | even => exact (f_continuous sieveA).continuousAt.comp (continuousAt_id.div_const 2)
    | odd =>
      have hx : r/2 ≠ 0 := by have h := hr; change 2 ≤ r at h; linarith
      have hg : ContinuousAt (fun x : ℝ => x/2) r := continuousAt_id.div_const 2
      have hF : ContinuousAt (F sieveA) ((fun x : ℝ => x/2) r) := F_continuousAt sieveA hx
      simpa only [Function.comp_def,benchmark] using hF.comp (f := fun x : ℝ => x/2) hg
  exact (hq.sub (continuousAt_const.mul hb)).continuousWithinAt

theorem anomaly_difference (w r : ℝ) (i : Side) :
    anomaly w i r-continuousAnomaly i r =
      (referencePolynomial w (boundaryPrimes w) i r-boundaryReference i r 2)-
        (boundaryProduct w-1/2)*benchmark i (r/2) := by
  unfold anomaly continuousAnomaly boundaryProduct
  ring

theorem uniform_anomaly_convergence (R eps : ℝ) (heps : 0 < eps) :
    ∃ w₀ : ℝ,1 < w₀ ∧ ∀ w : ℝ,w₀ ≤ w → ∀ (i : Side) (r : ℝ),2 ≤ r → r ≤ R →
      |anomaly w i r-continuousAnomaly i r| ≤ eps := by
  let A : ℝ := sieveA+1
  have hA : 0 < A := by dsimp [A]; linarith [sieveA_pos]
  obtain ⟨wQ,hwQ,hQ⟩ := boundary_two_convergence R (eps/2) (by positivity)
  have ht := (boundaryProduct_tendsto_half.sub_const (1/2)).abs
  have he := ht.eventually (Iio_mem_nhds (by simpa only [sub_self,abs_zero] using
    (div_pos heps (by positivity : 0 < 2*A))))
  obtain ⟨wP,hwP⟩ := eventually_atTop.mp he
  refine ⟨max wQ wP,hwQ.trans_le (le_max_left _ _),?_⟩
  intro w hw i r hr hrR
  have hqw := hQ w ((le_max_left _ _).trans hw) i r hrR
  have hpw := hwP w ((le_max_right _ _).trans hw)
  have hb : |benchmark i (r/2)| ≤ A := boundary_benchmark_bound i hr
  have hp : |boundaryProduct w-1/2| * |benchmark i (r/2)| ≤ (eps/(2*A))*A := by
    exact mul_le_mul hpw.le hb (abs_nonneg _) (by positivity)
  rw [anomaly_difference]
  apply (abs_sub _ _).trans
  rw [abs_mul]
  calc
    _ ≤ eps/2+(eps/(2*A))*A := add_le_add hqw hp
    _ = eps := by field_simp [ne_of_gt hA]; ring

end ErdosContinuousAnomaly

end

section

open _root_.Set _root_.Filter _root_.Erdos970.Set _root_.Erdos970.Filter
open scoped Topology
namespace ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.BoundaryAnomaly

theorem anomaly_tendsto (i : Side) {r : ℝ} (hr : 2 ≤ r) :
    Tendsto (fun w : ℝ => anomaly w i r) atTop (𝓝 (continuousAnomaly i r)) := by
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  obtain ⟨w₀,_hw₀,h⟩ := uniform_anomaly_convergence r (eps/2) (by positivity)
  refine ⟨w₀,fun w hw => ?_⟩
  rw [Real.dist_eq]
  exact (h w hw i r hr le_rfl).trans_lt (by linarith)

theorem common_anomaly_decay : ∃ C w₀ : ℝ,0 < C ∧ 1 < w₀ ∧
    (∀ w : ℝ,w₀ ≤ w → ∀ r : ℝ,2 ≤ r → ∀ i : Side,
      |anomaly w i r| ≤ C*Real.exp (-(1/128:ℝ)*r*Real.log (r+2))) ∧
    (∀ r : ℝ,2 ≤ r → ∀ i : Side,
      |continuousAnomaly i r| ≤ C*Real.exp (-(1/128:ℝ)*r*Real.log (r+2))) := by
  obtain ⟨C,w₀,hC,hw₀,h⟩ := actual_boundary_anomaly_decay
  refine ⟨C,w₀,hC,hw₀,h,?_⟩
  intro r hr i
  apply le_of_tendsto (anomaly_tendsto i hr).abs
  filter_upwards [eventually_ge_atTop w₀] with w hw
  exact h w hw r hr i

theorem common_anomaly_exponential : ∃ C c w₀ : ℝ,0 < C ∧ 0 < c ∧ 1 < w₀ ∧
    (∀ w : ℝ,w₀ ≤ w → ∀ r : ℝ,2 ≤ r → ∀ i : Side,
      |anomaly w i r| ≤ C*Real.exp (-c*r)) ∧
    (∀ r : ℝ,2 ≤ r → ∀ i : Side,
      |continuousAnomaly i r| ≤ C*Real.exp (-c*r)) := by
  obtain ⟨C,c,w₀,hC,hc,hw₀,h⟩ := actual_boundary_anomaly_exponential
  refine ⟨C,c,w₀,hC,hc,hw₀,h,?_⟩
  intro r hr i
  apply le_of_tendsto (anomaly_tendsto i hr).abs
  filter_upwards [eventually_ge_atTop w₀] with w hw
  exact h w hw r hr i

end ErdosContinuousAnomaly

end

section

open _root_.Set _root_.Filter _root_.MeasureTheory
open _root_.Erdos970.Set _root_.Erdos970.Filter _root_.Erdos970.MeasureTheory
open scoped Topology
namespace ErdosBoundaryIntegral
open ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry

noncomputable def shiftedAnomaly (i : Side) (y : ℝ) : ℝ := continuousAnomaly i (2*y+2)

theorem shiftedAnomaly_continuousOn (i : Side) : ContinuousOn (shiftedAnomaly i) (Ici 0) := by
  have hc : Continuous (fun y : ℝ => 2*y+2) := continuous_const.mul continuous_id |>.add continuous_const
  exact (continuousAnomaly_continuousOn i).comp' hc.continuousOn (by
    intro y hy; change 0 ≤ y at hy; change 2 ≤ 2*y+2; linarith)

theorem shifted_anomaly_moment_integrable (i : Side) (n : ℕ) :
    IntegrableOn (fun y : ℝ => y^n*shiftedAnomaly i y) (Ioi 0) := by
  obtain ⟨C,c,_w₀,hC,hc,_hw₀,_hD,hA⟩ := common_anomaly_exponential
  have hg : IntegrableOn (fun y : ℝ => y^n*Real.exp (-c*y)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (n:ℝ)) (p := 1)
      (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) hc
    simpa only [Real.rpow_natCast,Real.rpow_one] using! h
  have hcont : ContinuousOn (fun y : ℝ => y^n*shiftedAnomaly i y) (Ioi 0) :=
    (continuous_id.pow n).continuousOn.mul ((shiftedAnomaly_continuousOn i).mono Ioi_subset_Ici_self)
  apply (hg.const_mul C).mono' (hcont.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hy0 : 0 < y := hy
  have ha : |shiftedAnomaly i y| ≤ C*Real.exp (-c*y) := by
    apply (hA (2*y+2) (by linarith) i).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (pow_nonneg hy0.le n)]
  calc
    _ ≤ y^n*(C*Real.exp (-c*y)) := mul_le_mul_of_nonneg_left ha (pow_nonneg hy0.le n)
    _ = C*(y^n*Real.exp (-c*y)) := by ring

end ErdosBoundaryIntegral

end

section

open _root_.Set _root_.Filter _root_.Erdos970.Set _root_.Erdos970.Filter
open scoped Topology
namespace ErdosContinuousAnomaly
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.BoundaryAnomaly

theorem weighted_anomaly_convergence : ∃ c : ℝ,0 < c ∧
    ∀ eps : ℝ,0 < eps → ∃ w₀ : ℝ,1 < w₀ ∧
      ∀ w : ℝ,w₀ ≤ w → ∀ r : ℝ,2 ≤ r → ∀ i : Side,
        |anomaly w i r-continuousAnomaly i r| ≤ eps*Real.exp (-c*r) := by
  obtain ⟨C,c₀,wA,hC,hc₀,hwA,hdiscrete,hcontinuous⟩ := common_anomaly_exponential
  let c := c₀/2
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c,hc,?_⟩
  intro eps heps
  have ht : Tendsto (fun r : ℝ => (2*C)*Real.exp (-c*r)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0:ℝ) c hc).const_mul (2*C)
    simpa only [Real.rpow_zero,one_mul,mul_zero] using h
  obtain ⟨R₁,hR₁⟩ := eventually_atTop.mp (ht.eventually (Iio_mem_nhds heps))
  let R := max 2 R₁
  obtain ⟨wQ,hwQ,hQ⟩ := uniform_anomaly_convergence R (eps*Real.exp (-c*R)) (by positivity)
  refine ⟨max wA wQ,hwA.trans_le (le_max_left _ _),?_⟩
  intro w hw r hr i
  have hwa : wA ≤ w := (le_max_left _ _).trans hw
  have hwq : wQ ≤ w := (le_max_right _ _).trans hw
  by_cases hrR : r ≤ R
  · apply (hQ w hwq i r hr hrR).trans
    apply mul_le_mul_of_nonneg_left _ heps.le
    apply Real.exp_le_exp.mpr
    nlinarith
  · have htail : 2*C*Real.exp (-c*r) ≤ eps :=
      (hR₁ r ((le_max_right 2 R₁).trans (le_of_not_ge hrR))).le
    have hbound : |anomaly w i r-continuousAnomaly i r| ≤ 2*C*Real.exp (-c₀*r) := by
      calc
        _ ≤ |anomaly w i r|+|continuousAnomaly i r| := abs_sub _ _
        _ ≤ C*Real.exp (-c₀*r)+C*Real.exp (-c₀*r) :=
          add_le_add (hdiscrete w hwa r hr i) (hcontinuous r hr i)
        _ = _ := by ring
    have he : -c₀*r=(-c*r)+(-c*r) := by dsimp [c]; ring
    rw [he,Real.exp_add] at hbound
    calc
      _ ≤ 2*C*(Real.exp (-c*r)*Real.exp (-c*r)) := hbound
      _ = (2*C*Real.exp (-c*r))*Real.exp (-c*r) := by ring
      _ ≤ eps*Real.exp (-c*r) := mul_le_mul_of_nonneg_right htail (Real.exp_pos _).le

end ErdosContinuousAnomaly

end

end Erdos970

end OAI
