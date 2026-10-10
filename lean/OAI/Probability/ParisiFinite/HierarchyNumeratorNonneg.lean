import Mathlib
import OAI.Probability.ParisiFinite.LogSeriesTermBound

namespace OAI

/-! Hierarchy Numerator Nonneg. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped Topology
open Filter Asymptotics
open scoped InnerProductSpace Topology
open scoped InnerProductSpace BigOperators
open scoped InnerProductSpace Topology BigOperators
open scoped Topology BigOperators
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace
open scoped Matrix Matrix.Norms.L2Operator InnerProductSpace BigOperators
open Filter ContinuousLinearMap
open ContinuousLinearMap
open scoped InnerProductSpace BigOperators Topology
open ContinuousLinearMap InnerProductSpace
open ContinuousLinearMap Filter
open Filter MeasureTheory
open scoped Topology ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology RealInnerProductSpace
open scoped BigOperators TensorProduct
open scoped Topology InnerProductSpace
open MeasureTheory Filter
open MeasureTheory ProbabilityTheory Complex
open scoped BigOperators Topology InnerProductSpace ComplexConjugate
open scoped BigOperators Topology NNReal
open scoped BigOperators NNReal Topology
open scoped BigOperators NNReal
open scoped NNReal Topology
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set MeasurableSpace
open MeasureTheory ProbabilityTheory Filter TopologicalSpace Set MeasurableSpace
open scoped BigOperators Topology NNReal ENNReal MatrixOrder
open scoped BigOperators Topology NNReal ENNReal ContDiff
open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal ContDiff
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite
variable {ι : Type*} [Fintype ι]

lemma hierarchyNumerator_nonneg {d r : ℕ} {a : Fin (d+1) → ℝ}
    (ha : ∀ k,0≤a k) (hm : Monotone a) (h1 : a (Fin.last d)≤1)
    (c : Fin (d+1) → Fin r → ℕ) : 0≤hierarchyNumerator a c := by
  unfold hierarchyNumerator edgeFactor leafFactor branchFactor blockFactor
  apply mul_nonneg
  · apply Finset.prod_nonneg
    intro k _
    apply Finset.prod_nonneg
    intro x _
    apply Finset.prod_nonneg
    intro j _
    have hh := hm (show k.castSucc≤k.succ by exact Fin.castSucc_le_succ k)
    have hj : (0:ℝ)≤j := Nat.cast_nonneg j
    nlinarith [ha k.succ]
  · apply Finset.prod_nonneg
    intro x _
    apply Finset.prod_nonneg
    intro j _
    have hj : (0:ℝ)≤j := Nat.cast_nonneg j
    linarith

def parameterHierarchyMoment {d : ℕ} (a : Fin (d+1) → ℝ) (w : ι → ℝ)
    (x : (Fin (d+1) → ι) → ℝ) (n : ℕ) : ℝ :=
  if n=0 then 1 else hierarchyCoefficient w (Fin.cons 0 a) x n/((n-1).factorial:ℝ)

lemma parameterHierarchyMoment_mem_unit {d : ℕ} {a : Fin (d+1) → ℝ}
    (ha : ∀ k,0≤a k) (hm : Monotone a) (h1 : a (Fin.last d)≤1)
    {w : ι → ℝ} (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1)
    {x : (Fin (d+1) → ι) → ℝ} (hx : ∀ s,0≤x s ∧ x s≤1) (n : ℕ) :
    0≤parameterHierarchyMoment a w x n ∧ parameterHierarchyMoment a w x n≤1 := by
  classical
  by_cases hn : n=0
  · simp [parameterHierarchyMoment,hn]
  have hnon : ∀ k : Fin (d+2),0≤Fin.cons (α:=fun _ => ℝ) 0 a k := by intro k; induction k using Fin.cases <;> simp [ha]
  have hmono : Monotone (Fin.cons 0 a) := by
    intro i j hij
    induction i using Fin.cases with
    | zero => simpa using hnon j
    | succ i =>
      induction j using Fin.cases with
      | zero => exact (False.elim (by exact not_le_of_gt (Fin.succ_pos i) hij))
      | succ j => exact hm (Fin.succ_le_succ_iff.mp hij)
  have hn1 : Fin.cons (α:=fun _ => ℝ) 0 a (Fin.last (d+1))≤1 := by simpa using h1
  have hT (T : PartitionTree (d+1) n) := hierarchyNumerator_nonneg hnon hmono hn1 (treeCodes T)
  have hmass := hierarchy_numerator_mass a ha (Nat.pos_of_ne_zero hn)
  simp only [parameterHierarchyMoment,hn,↓reduceIte,hierarchyCoefficient]
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun T _ => mul_nonneg (hT T)
      (treeMarkMoment_mem_unit hw hs hx T).1)) (Nat.cast_nonneg _)
  · rw [div_le_one (by positivity)]
    calc
      _ ≤ ∑ T : PartitionTree (d+1) n,hierarchyNumerator (Fin.cons 0 a) (treeCodes T) :=
        Finset.sum_le_sum (fun T _ => mul_le_of_le_one_right (hT T) (treeMarkMoment_mem_unit hw hs hx T).2)
      _ = _ := hmass

lemma parameterHierarchyMoment_continuous {d : ℕ} (w : ι → ℝ)
    (x : (Fin (d+1) → ι) → ℝ) (n : ℕ) : Continuous (fun a => parameterHierarchyMoment a w x n) := by
  classical
  unfold parameterHierarchyMoment
  split_ifs
  · exact continuous_const
  · apply Continuous.div_const
    unfold hierarchyCoefficient
    apply continuous_finsetSum
    intro T _
    apply Continuous.mul_const
    apply (continuous_hierarchyNumerator (treeCodes T)).comp
    exact continuous_finCons continuous_const continuous_id

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal ContDiff
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite
variable {ι : Type*} [Fintype ι]

def parameterHierarchyLogSeries {d : ℕ} (a : Fin (d+1) → ℝ)
    (w : ι → ℝ) (x : (Fin (d+1) → ι) → ℝ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ (fun n => -parameterHierarchyMoment a w x n/(n:ℝ))

lemma parameterHierarchyLogSeries_radius {d : ℕ} {a : Fin (d+1) → ℝ}
    (ha : ∀ k,0≤a k) (hm : Monotone a) (h1 : a (Fin.last d)≤1)
    {w : ι → ℝ} (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1)
    {x : (Fin (d+1) → ι) → ℝ} (hx : ∀ s,0≤x s ∧ x s≤1) :
    (1:ℝ≥0∞)≤(parameterHierarchyLogSeries a w x).radius := by
  apply FormalMultilinearSeries.le_radius_of_bound (C:=1) (r:=1)
  intro n
  simp only [parameterHierarchyLogSeries,FormalMultilinearSeries.ofScalars,norm_smul,
    NNReal.coe_one,one_pow,mul_one,Real.norm_eq_abs,abs_div,abs_neg]
  rw [show |(n:ℝ)|=(n:ℝ) from abs_of_nonneg (Nat.cast_nonneg n)]
  by_cases hn : n=0
  · simp [hn]
  have hm := parameterHierarchyMoment_mem_unit ha hm h1 hw hs hx n
  rw [abs_of_nonneg hm.1]
  have hn1 : (1:ℝ)≤n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnorm : ‖ContinuousMultilinearMap.mkPiAlgebraFin ℝ n ℝ‖≤1 := by
    apply le_trans ContinuousMultilinearMap.norm_mkPiAlgebraFin_le
    norm_num
  calc
    _ ≤ (1:ℝ)/(n:ℝ)*1 := mul_le_mul (div_le_div_of_nonneg_right hm.2 (Nat.cast_nonneg _)) hnorm
      (norm_nonneg _) (by positivity)
    _ ≤ 1 := by rw [mul_one]; exact (div_le_one (by positivity)).mpr hn1

lemma parameterHierarchyLog_hasFPowerSeriesAt
    {d : ℕ} (a : Fin (d+1) → ℝ) (ha : ∀ k,a k≠0)
    (w : ι → ℝ) (hw : ∑ i,w i=1) (x : (Fin (d+1) → ι) → ℝ) :
    HasFPowerSeriesAt (hierarchyLog w a x)
      (parameterHierarchyLogSeries a w x) 0 := by
  have hz : (∑ i,w i*hierarchyMark w d a (fun s => x (Fin.cons i s)) 0)=1 := by
    simp [hierarchyMark_zero w hw,hw]
  have hf : ContDiffAt ℝ ω (hierarchyLog w a x) 0 := by
    apply contDiffAt_const.mul
    apply (Real.contDiffAt_log.mpr _).comp 0
      (ContDiffAt.sum fun i _ => contDiffAt_const.mul (hierarchyMark_contDiffAt_zero w hw _ _ ω))
    rw [hz]; norm_num
  have h := hf.analyticAt.hasFPowerSeriesAt
  have he : (fun n => iteratedDeriv n (hierarchyLog w a x) 0/(n.factorial:ℝ))=
      (fun n => -parameterHierarchyMoment a w x n/(n:ℝ)) := by
    funext n
    by_cases hn : n=0
    · subst n
      simp only [iteratedDeriv_zero,hierarchyLog_zero w hw,Nat.factorial_zero,Nat.cast_one,
        div_one,Nat.cast_zero,div_zero]
    · have hn' := Nat.pos_of_ne_zero hn
      rw [hierarchyLog_derivative w hw a ha x hn']
      simp only [parameterHierarchyMoment,hn,↓reduceIte]
      have hf : (n.factorial:ℝ)=(n:ℝ)*((n-1).factorial:ℝ) := by
        exact_mod_cast (Nat.mul_factorial_pred hn).symm
      have hf0 : ((n-1).factorial:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hn0 : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr hn
      rw [hf]
      field_simp
  rw [he] at h
  exact h

 
theorem parameterHierarchy_log_identity
    {d : ℕ} {a : Fin (d+1) → ℝ} (han : ∀ k,0≤a k) (ham : Monotone a)
    (ha1 : a (Fin.last d)≤1) (ha : ∀ k,a k≠0)
    {w : ι → ℝ} (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1)
    {x : (Fin (d+1) → ι) → ℝ} (hx : ∀ s,0≤x s ∧ x s≤1)
    {z : ℝ} (hz : |z|<1) :
    hierarchyLog w a x z=
      (parameterHierarchyLogSeries a w x).sum z := by
  let f := hierarchyLog w a x
  let p := parameterHierarchyLogSeries a w x
  have hr : (1:ℝ≥0∞)≤p.radius := parameterHierarchyLogSeries_radius han ham ha1 hw hs hx
  have hf : AnalyticOnNhd ℝ f (Set.Ioo (-1) 1) := by
    intro t ht
    exact (hierarchyLog_contDiffAt hw hs _ hx (abs_lt.mpr ht) ω).analyticAt
  have hp : AnalyticOnNhd ℝ p.sum (Set.Ioo (-1) 1) := by
    intro t ht
    apply p.analyticOnNhd
    apply lt_of_lt_of_le _ hr
    rw [edist_zero_right,← ofReal_norm]
    exact ENNReal.ofReal_lt_one.mpr (abs_lt.mpr ht)
  have he : f=ᶠ[𝓝 0] p.sum := by
    filter_upwards [(parameterHierarchyLog_hasFPowerSeriesAt a ha w hs x).eventually_hasSum] with t ht
    simpa only [zero_add,f,p,FormalMultilinearSeries.sum] using ht.tsum_eq.symm
  exact hf.eqOn_of_preconnected_of_eventuallyEq hp isPreconnected_Ioo (by constructor <;> norm_num)
    he (abs_lt.mp hz)

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite
variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

 
theorem parameterHierarchy_finiteRisk_identity_all (ν : Measure ι) [IsProbabilityMeasure ν]
    {d : ℕ} {a : Fin (d+1) → ℝ} (ha : ∀ k,0≤a k) (hm : Monotone a)
    (h1 : a (Fin.last d)≤1)
    {x : (Fin (d+1) → ι) → ℝ} (hx : ∀ s,0≤x s ∧ x s≤1)
    {z : ℝ} (hz : |z|<1) :
    finiteHierarchyRisk (fun i => ν.real {i}) a (fun s => Real.log (1-z*x s))=
      ∑' n,-parameterHierarchyMoment a (fun i => ν.real {i}) x n/(n:ℝ)*z^n := by
  let δ (m : ℕ) : ℝ := 1/(m+1:ℕ)
  have hd (m : ℕ) : 0<δ m ∧ δ m≤1 := by
    constructor
    · positivity
    · exact (div_le_one (by positivity)).mpr (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m))
  let b (m : ℕ) (k : Fin (d+1)) : ℝ := (1-δ m)*a k+δ m
  have hb (m : ℕ) (k : Fin (d+1)) : 0<b m k :=
    add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr (hd m).2) (ha k)) (hd m).1
  have hbm (m : ℕ) : Monotone (b m) := by
    intro i j hij
    exact add_le_add (mul_le_mul_of_nonneg_left (hm hij) (sub_nonneg.mpr (hd m).2)) le_rfl
  have hb1 (m : ℕ) : b m (Fin.last d)≤1 := by
    have hh := mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr (hd m).2)
    dsimp only [b]
    nlinarith
  have ht : Tendsto b atTop (𝓝 a) := by
    apply tendsto_pi_nhds.mpr
    intro k
    have hdlim : Tendsto δ atTop (𝓝 0) := tendsto_succ_reciprocal
    simpa only [sub_zero,one_mul,add_zero] using (((tendsto_const_nhds (x:=(1:ℝ))).sub hdlim).mul_const (a k)).add hdlim
  have hw : ∀ i,0≤ν.real {i} := fun i => measureReal_nonneg
  have hs : (∑ i,ν.real {i})=1 := by
    simp
  have he (m : ℕ) : finiteHierarchyRisk (fun i => ν.real {i}) (b m) (fun s => Real.log (1-z*x s))=
      ∑' n,-parameterHierarchyMoment (b m) (fun i => ν.real {i}) x n/(n:ℝ)*z^n := by
    rw [← hierarchyLog_eq_finiteHierarchyRisk hw hs (b m) (fun k => (hb m k).ne')
      (fun s => affine_mark_pos (hx s) hz)]
    rw [parameterHierarchy_log_identity (fun k => (hb m k).le) (hbm m) (hb1 m)
      (fun k => (hb m k).ne') hw hs hx hz]
    simp only [FormalMultilinearSeries.sum,parameterHierarchyLogSeries,
      FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul]
  have hleft := finiteHierarchyRisk_coefficient_tendsto ν (fun m k => (hb m k).le)
    (tendsto_pi_nhds.mp ht) (fun s => Real.log (1-z*x s))
  have hright : Tendsto (fun m => ∑' n,-parameterHierarchyMoment (b m) (fun i => ν.real {i}) x n/(n:ℝ)*z^n)
      atTop (𝓝 (∑' n,-parameterHierarchyMoment a (fun i => ν.real {i}) x n/(n:ℝ)*z^n)) := by
    apply tendsto_tsum_of_dominated_convergence (summable_geometric_of_lt_one (abs_nonneg z) hz)
    · intro n
      exact ((((parameterHierarchyMoment_continuous (fun i => ν.real {i}) x n).continuousAt.tendsto.comp ht).neg).div_const (n:ℝ)).mul_const (z^n)
    · exact Eventually.of_forall fun m n => normalized_moment_bound
        (parameterHierarchyMoment_mem_unit (fun k => (hb m k).le) (hbm m) (hb1 m) hw hs hx n) z n
  simp_rw [he] at hleft
  exact tendsto_nhds_unique hleft hright

 
theorem GG_finiteRisk_identity_all {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {d : ℕ} (q : Fin (d+2) → ℝ) (hq : Monotone q) (h0 : q 0 < -1)
    (h1 : q (Fin.last (d+1))<1) (ν : Measure ι) [IsProbabilityMeasure ν]
    {x : (Fin (d+1) → ι) → ℝ} (hx : ∀ s,0≤x s ∧ x s≤1)
    {z : ℝ} (hz : |z|<1) :
    finiteHierarchyRisk (fun i => ν.real {i}) (fun k => overlapDiscount μ (q k.succ))
      (fun s => Real.log (1-z*x s))=
      ∑' n,-hierarchyMarkedMoment μ q (fun i => ν.real {i}) x n/(n:ℝ)*z^n := by
  let := entryLaw_probability μ 0 1
  let a := fun k : Fin (d+1) => overlapDiscount μ (q k.succ)
  have ha : ∀ k,0≤a k := fun k => measureReal_nonneg
  have hm : Monotone a := by
    intro i j hij
    apply measureReal_mono
    · exact fun u hu => le_trans hu (hq (Fin.succ_le_succ_iff.mpr hij))
    · exact measure_ne_top _ _
  have ha1 : a (Fin.last d)≤1 := measureReal_le_one
  rw [parameterHierarchy_finiteRisk_identity_all ν ha hm ha1 hx hz]
  apply tsum_congr
  intro n
  by_cases hn : n=0
  · simp [hn]
  have he : Fin.cons 0 a=(fun k => overlapDiscount μ (q k)) := by
    funext k
    induction k using Fin.cases with
    | zero => exact (overlapDiscount_below μ h0).symm
    | succ k => rfl
  simp only [parameterHierarchyMoment,hn,↓reduceIte,he]
  rw [GG_hierarchy_coefficient hG hgg hu q hq h1 _ x (Nat.pos_of_ne_zero hn)]
  rw [mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite

 

theorem GG_gaussian_hierarchy_log_identity_all {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {d : ℕ} (q : Fin (d+2) → ℝ) (hq : Monotone q) (h0 : q 0 < -1)
    (h1 : q (Fin.last (d+1))<1)
    {x : (Fin (d+1) → ℝ) → ℝ} (hx : Continuous x) (hb : ∀ s,0≤x s ∧ x s≤1)
    {z : ℝ} (hz : |z|<1) :
    gaussianHierarchyRisk (fun k => overlapDiscount μ (q k.succ))
      (fun s => Real.log (1-z*x s))=
      ∑' n,-gaussianHierarchyMoment μ q x n/(n:ℝ)*z^n := by
  let a : Fin (d+1) → ℝ := fun k => overlapDiscount μ (q k.succ)
  let f : (Fin (d+1) → ℝ) → ℝ := fun s => Real.log (1-z*x s)
  have hf : Continuous f := (continuous_const.sub (hx.const_mul z)).log
    (fun s => ne_of_gt (affine_mark_pos (hb s) hz))
  have hfB (s : Fin (d+1) → ℝ) : |f s|≤|Real.log (1-|z|)|+|Real.log (1+|z|)| :=
    affine_log_bounded hb hz s
  have hleft := quantizedHierarchyRisk_tendsto (E:=Unit) (a:=a) (f:=fun _ s => f s)
    (fun k => measureReal_nonneg) (hf.comp continuous_snd) (fun _ s => hfB s)
    (u:=fun _ => ()) (e:=()) tendsto_const_nhds
  have heq (m : ℕ) : finiteHierarchyRisk (gaussianQuantizerWeight m) a
      (fun s : Fin (d+1) → GaussianQuantizerLabel m => f (fun k => (s k).val))=
      ∑' n,-hierarchyMarkedMoment μ q (gaussianQuantizerWeight m)
        (fun s : Fin (d+1) → GaussianQuantizerLabel m => x (fun k => (s k).val)) n/(n:ℝ)*z^n := by
    exact GG_finiteRisk_identity_all hG hgg hu q hq h0 h1
      (gaussianQuantizerLaw m) (fun s => hb _) hz
  have hright : Tendsto (fun m => ∑' n,-hierarchyMarkedMoment μ q (gaussianQuantizerWeight m)
      (fun s : Fin (d+1) → GaussianQuantizerLabel m => x (fun k => (s k).val)) n/(n:ℝ)*z^n)
      atTop (𝓝 (∑' n,-gaussianHierarchyMoment μ q x n/(n:ℝ)*z^n)) := by
    apply tendsto_tsum_of_dominated_convergence (summable_geometric_of_lt_one (abs_nonneg z) hz)
    · intro n
      exact (((hierarchyMarkedMoment_tendsto_gaussian μ q hx hb n).neg).div_const (n:ℝ)).mul_const (z^n)
    · exact Eventually.of_forall fun m n => normalized_moment_bound
        (hierarchyMarkedMoment_mem_unit μ q (gaussianQuantizerWeight_nonneg m)
          (gaussianQuantizerWeight_sum m) (fun s => hb _) n) z n
  simp_rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite

theorem hierarchy_empirical_log_tendsto_all {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1) (hex : FiniteExchangeable μ)
    {d : ℕ} (q : Fin (d+2) → ℝ) (hq : Monotone q) (h0 : q 0 < -1)
    (h1 : q (Fin.last (d+1))<1)
    {x : (Fin (d+1) → ℝ) → ℝ} (hx : Continuous x) (hb : ∀ s,0≤x s ∧ x s≤1)
    {z : ℝ} (hz : |z|<1) :
    Tendsto (fun r => ∫ s,Real.log (1-z*((∑ i : Fin (r+1),x (s i))/(r+1:ℕ)))
      ∂hierarchySampleLaw μ q (r+1)) atTop
      (𝓝 (gaussianHierarchyRisk (fun k => overlapDiscount μ (q k.succ))
        (fun s => Real.log (1-z*x s)))) := by
  let ν (r : ℕ) := hierarchySampleLaw μ q (r+1)
  let (r : ℕ) : IsProbabilityMeasure (ν r) :=
    hierarchySampleLaw_probability hG hgg hu q hq h0 h1 (Nat.succ_pos r)
  let M (k : ℕ) := if k=0 then 1 else gaussianHierarchyMoment μ q x k
  have hM (k : ℕ) : 0≤M k ∧ M k≤1 := by
    by_cases hk : k=0
    · simp [M,hk]
    · simpa [M,hk] using gaussianHierarchyMoment_mem_unit μ q hx hb k
  have he (r k : ℕ) (e : Fin k → Fin (r+1)) (he : Function.Injective e) :
      (∫ s,∏ i,x (s (e i)) ∂ν r)=M k := by
    by_cases hk : k=0
    · subst k
      simp [M]
    have hk' := Nat.pos_of_ne_zero hk
    rw [hierarchySampleLaw_marginal_integral hG hgg hu hex q hq h0 h1 (Nat.succ_pos r) hk'
      e he (f:=fun s => ∏ i,x (s i)) (by fun_prop) (C:=1)]
    · simpa [M,hk] using hierarchySampleLaw_product μ q hx hb
    · intro s
      rw [abs_of_nonneg (Finset.prod_nonneg (fun i _ => (hb (s i)).1))]
      exact Finset.prod_le_one₀ (fun i _ => (hb (s i)).1) (fun i _ => (hb (s i)).2)
  have ht := empirical_log_limit_of_distinct_moments ν (fun _ s i => x (s i))
    (fun _ i => hx.measurable.comp (measurable_pi_apply i)) (fun _ s i => hb (s i)) M hM he hz
  rw [GG_gaussian_hierarchy_log_identity_all hG hgg hu q hq h0 h1 hx hb hz]
  have hs : Summable (fun n => -gaussianHierarchyMoment μ q x n/(n:ℝ)*z^n) := by
    apply Summable.of_norm_bounded_eventually (summable_geometric_of_lt_one (abs_nonneg z) hz)
    exact Eventually.of_forall (fun n => normalized_moment_bound (gaussianHierarchyMoment_mem_unit μ q hx hb n) z n)
  rw [hs.tsum_eq_zero_add]
  simp only [Nat.cast_zero,div_zero,zero_mul,zero_add]
  convert ht using 2
  apply tsum_congr
  intro n
  simp only [M,Nat.add_one_ne_zero,↓reduceIte]
  ring

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite

 

theorem hierarchy_empirical_positive_tendsto_all {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1) (hex : FiniteExchangeable μ)
    {d : ℕ} (q : Fin (d+2) → ℝ) (hq : Monotone q) (h0 : q 0 < -1)
    (h1 : q (Fin.last (d+1))<1)
    {y : (Fin (d+1) → ℝ) → ℝ} (hy : Continuous y) {l b : ℝ} (hl : 0<l) (hlb : l<b)
    (hb : ∀ s,l≤y s ∧ y s≤b) :
    Tendsto (fun r => ∫ s,Real.log ((∑ i : Fin (r+1),y (s i))/(r+1:ℕ))
      ∂hierarchySampleLaw μ q (r+1)) atTop
      (𝓝 (gaussianHierarchyRisk (fun k => overlapDiscount μ (q k.succ)) (fun s => Real.log (y s)))) := by
  let x (s : Fin (d+1) → ℝ) := (b-y s)/(b-l)
  let z := (b-l)/b
  have hbp : 0<b := hl.trans hlb
  have hbl : 0<b-l := sub_pos.mpr hlb
  have hx : Continuous x := by unfold x; fun_prop
  have hxb (s : Fin (d+1) → ℝ) : 0≤x s ∧ x s≤1 := by
    exact ⟨div_nonneg (sub_nonneg.mpr (hb s).2) hbl.le,
      (div_le_one hbl).mpr (by linarith [(hb s).1])⟩
  have hz : |z|<1 := by
    rw [abs_of_pos (div_pos hbl hbp)]
    exact (div_lt_one hbp).mpr (by linarith)
  have he (s : Fin (d+1) → ℝ) : y s=b*(1-z*x s) := by
    dsimp only [x,z]
    field_simp
    ring
  have hlog (s : Fin (d+1) → ℝ) : Real.log (y s)=Real.log (1-z*x s)+Real.log b := by
    rw [he,Real.log_mul hbp.ne' (affine_mark_pos (hxb s) hz).ne']
    ring
  have ht := hierarchy_empirical_log_tendsto_all hG hgg hu hex q hq h0 h1 hx hxb hz
  have hlogc : Continuous (fun s => Real.log (1-z*x s)) :=
    (continuous_const.sub (hx.const_mul z)).log (fun s => (affine_mark_pos (hxb s) hz).ne')
  have hrisk := gaussianHierarchyRisk_add_const (a:=fun k : Fin (d+1) => overlapDiscount μ (q k.succ)) (fun k => (measureReal_nonneg : 0≤overlapDiscount μ (q k.succ)))
    hlogc (affine_log_bounded hxb hz) (Real.log b)
  have hleft (r : ℕ) : (∫ s,Real.log ((∑ i : Fin (r+1),y (s i))/(r+1:ℕ)) ∂hierarchySampleLaw μ q (r+1))=
      (∫ s,Real.log (1-z*((∑ i : Fin (r+1),x (s i))/(r+1:ℕ))) ∂hierarchySampleLaw μ q (r+1))+Real.log b := by
    let := hierarchySampleLaw_probability hG hgg hu q hq h0 h1 (Nat.succ_pos r)
    have hrep : (fun s : Fin (r+1) → Fin (d+1) → ℝ => Real.log ((∑ i,y (s i))/(r+1:ℕ)))=
        (fun s => Real.log ((∑ i,b*(1-z*x (s i)))/(r+1:ℕ))) := by
      funext s
      congr 2
      exact Finset.sum_congr rfl (fun i _ => he (s i))
    rw [hrep]
    exact integral_affine_average_log _ (Nat.succ_pos r)
      (fun i => hx.measurable.comp (measurable_pi_apply i)) (fun s i => hxb (s i)) hbp hz
  simp_rw [hleft,hlog]
  rw [hrisk]
  exact ht.add_const _

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite

lemma treePathLaw_coordinate {d r : ℕ} (T : PartitionTree d r) (i : Fin r) :
    (treePathLaw T).map (fun s => s i)=gaussianLaw (Fin d) := by
  classical
  let A : Fin d → TreeNode T → ℝ := fun k => pathCoeff T (i,k)
  let B : Fin d → Fin d → ℝ := fun k l => if k=l then 1 else 0
  have hB : field B=id := by
    funext z k
    simp [field,B]
  have hA : field A=(fun z k => treePathVector T z i k) := by
    funext z k
    exact field_pathCoeff T z (i,k)
  have hk : kernel A=kernel B := by
    funext k l
    change kernel (pathCoeff T) (i,k) (i,l)=_
    rw [kernel_pathCoeff]
    have hh : treeNodePath T i k=treeNodePath T i l ↔ k=l :=
      ⟨fun h => treeNodePath_eq_levels T i i k l h,fun h => by rw [h]⟩
    simp only [hh]
    simp [kernel,B]
  have hh := field_law_eq_of_kernel A B hk
  rw [hB,Measure.map_id,hA] at hh
  unfold treePathLaw
  rw [Measure.map_map (by fun_prop) (treePathVector_continuous T).measurable]
  exact hh

 

lemma hierarchySampleLaw_coordinate {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {d : ℕ} (q : Fin (d+2) → ℝ) (hq : Monotone q) (h0 : q 0 < -1)
    (h1 : q (Fin.last (d+1))<1) {r : ℕ} (i : Fin r) :
    (hierarchySampleLaw μ q r).map (fun s => s i)=gaussianLaw (Fin (d+1)) := by
  have hp := hierarchySampleLaw_probability hG hgg hu q hq h0 h1 (i.pos)
  have hsum : (∑ T : PartitionTree (d+1) r,(μ:Measure OverlapArray) (hierarchyEvent (treeCodes T) q))=1 := by
    have hh := hp.measure_univ
    simpa only [hierarchySampleLaw,Measure.finsetSum_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one] using hh
  unfold hierarchySampleLaw
  rw [Measure.map_finset_sum' ((measurable_pi_apply i).aemeasurable)]
  simp_rw [Measure.map_smul _ ((measurable_pi_apply i).aemeasurable),treePathLaw_coordinate]
  rw [← Finset.sum_smul,hsum,one_smul]

lemma hierarchySampleLaw_integrable_coordinate {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {d : ℕ} (q : Fin (d+2) → ℝ) (hq : Monotone q) (h0 : q 0 < -1)
    (h1 : q (Fin.last (d+1))<1) {r : ℕ} (i : Fin r)
    {f : (Fin (d+1) → ℝ) → ℝ} (hf : Integrable f (gaussianLaw (Fin (d+1)))) :
    Integrable (fun s => f (s i)) (hierarchySampleLaw μ q r) := by
  have hh := hierarchySampleLaw_coordinate hG hgg hu q hq h0 h1 i
  rw [← hh] at hf
  exact hf.comp_measurable (by fun_prop)

lemma hierarchySampleLaw_integral_coordinate {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {d : ℕ} (q : Fin (d+2) → ℝ) (hq : Monotone q) (h0 : q 0 < -1)
    (h1 : q (Fin.last (d+1))<1) {r : ℕ} (i : Fin r)
    {f : (Fin (d+1) → ℝ) → ℝ} (hf : Measurable f) :
    (∫ s,f (s i) ∂hierarchySampleLaw μ q r)=∫ z,f z ∂gaussianLaw (Fin (d+1)) := by
  rw [← integral_map (by fun_prop : Measurable (fun s : Fin r → Fin (d+1) → ℝ => s i)).aemeasurable hf.aestronglyMeasurable]
  rw [hierarchySampleLaw_coordinate hG hgg hu q hq h0 h1 i]

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace ParisiFinite

 

theorem step_tendsto {L : ℝ≥0} {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ m,LipschitzWith L (F m)) (hf : LipschitzWith L f)
    (ht : ∀ x,Tendsto (fun m => F m x) atTop (𝓝 (f x))) (a s x : ℝ) :
    Tendsto (fun m => step a s (F m) x) atTop (𝓝 (step a s f x)) := by
  have hb : ∀ᶠ m in atTop,|F m x|≤|f x|+1 := by
    have hh := (ht x).abs.eventually (gt_mem_nhds (lt_add_one |f x|))
    exact hh.mono fun m hm => hm.le
  have hiabs : Integrable (fun z : ℝ => |z|) (gaussianReal 0 1) :=
    (MemLp.integrable (by norm_num) (memLp_id_gaussianReal (μ:=0) (v:=1) 1)).abs
  by_cases ha : a=0
  · simp only [step,ha,logMean_zero]
    apply tendsto_integral_filter_of_dominated_convergence
      (fun z : ℝ => |f x|+1+(L:ℝ)* |s| * |z|)
    · exact Eventually.of_forall fun m => ((hF m).continuous.comp (by fun_prop)).aestronglyMeasurable
    · filter_upwards [hb] with m hm
      exact ae_of_all _ fun z => by
        rw [Real.norm_eq_abs]
        exact (shift_norm_le (hF m) x s z).trans (by linarith)
    · exact (integrable_const _).add (hiabs.const_mul _)
    · exact ae_of_all _ fun z => ht _
  · have hi : Tendsto (fun m => ∫ z,Real.exp (a*F m (x+s*z)) ∂gaussianReal 0 1) atTop
        (𝓝 (∫ z,Real.exp (a*f (x+s*z)) ∂gaussianReal 0 1)) := by
      apply tendsto_integral_filter_of_dominated_convergence
        (fun z : ℝ => Real.exp (|a| *(|f x|+1))*Real.exp ((|a| *(L:ℝ)* |s|)* |z|))
      · exact Eventually.of_forall fun m => (integrable_exp_shift (hF m) a x s).aestronglyMeasurable
      · filter_upwards [hb] with m hm
        exact ae_of_all _ fun z => by
          rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),← Real.exp_add]
          apply Real.exp_le_exp.mpr
          have hh := shift_norm_le (hF m) x s z
          have hh' : a*F m (x+s*z)≤|a| * |F m (x+s*z)| := by
            simpa only [abs_mul] using le_abs_self (a*F m (x+s*z))
          nlinarith [abs_nonneg a]
      · exact (integrable_exp_abs _).const_mul _
      · exact ae_of_all _ fun z => Real.continuous_exp.continuousAt.tendsto.comp ((ht _).const_mul a)
    simp only [step,logMean,ha,↓reduceIte]
    exact (hi.log (integral_exp_pos (integrable_exp_shift hf a x s)).ne').div_const a

 
lemma clip_lipschitz {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f) (M : ℝ) :
    LipschitzWith L (fun x => max (-M) (min M (f x))) :=
  (hf.const_min M).const_max (-M)

lemma clip_tendsto (z : ℝ) :
    Tendsto (fun m : ℕ => max (-(m:ℝ)) (min (m:ℝ) z)) atTop (𝓝 z) := by
  have ht : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  apply tendsto_const_nhds.congr'
  filter_upwards [ht.eventually_ge_atTop |z|] with m hm
  rw [min_eq_right (le_abs_self z |>.trans hm),max_eq_right]
  linarith [neg_abs_le z]

end ParisiFinite

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open ParisiFinite

 

def scalarHierarchy : {d : ℕ} → (Fin d → ℝ) → (Fin d → ℝ) → (ℝ → ℝ) → ℝ → ℝ
  | 0,_,_,f => f
  | _+1,a,s,f => step (a 0) (s 0) (scalarHierarchy (fun k => a k.succ) (fun k => s k.succ) f)

lemma scalarHierarchy_lipschitz {d : ℕ} {a s : Fin d → ℝ} (ha : ∀ k,0≤a k)
    {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f) :
    LipschitzWith L (scalarHierarchy a s f) := by
  induction d with
  | zero => exact hf
  | succ d ih => exact step_lipschitz (ih (fun k => ha k.succ)) (ha 0) _

lemma gaussianHierarchyRisk_sum {d : ℕ} (a s : Fin d → ℝ) (f : ℝ → ℝ) (x : ℝ) :
    gaussianHierarchyRisk a (fun z => f (x+∑ k,s k*z k))=scalarHierarchy a s f x := by
  induction d generalizing x with
  | zero => simp [gaussianHierarchyRisk,scalarHierarchy]
  | succ d ih =>
    change logMean _ _ _=logMean _ _ _
    congr 1
    funext z
    rw [← ih (fun k => a k.succ) (fun k => s k.succ) (x+s 0*z)]
    congr 1
    funext t
    simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
    ring_nf

lemma scalarHierarchy_tendsto {d : ℕ} {a s : Fin d → ℝ} (ha : ∀ k,0≤a k)
    {L : ℝ≥0} {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ m,LipschitzWith L (F m)) (hf : LipschitzWith L f)
    (ht : ∀ x,Tendsto (fun m => F m x) atTop (𝓝 (f x))) (x : ℝ) :
    Tendsto (fun m => scalarHierarchy a s (F m) x) atTop (𝓝 (scalarHierarchy a s f x)) := by
  induction d generalizing x with
  | zero => exact ht x
  | succ d ih =>
    apply step_tendsto
    · intro m; exact scalarHierarchy_lipschitz (fun k => ha k.succ) (hF m)
    · exact scalarHierarchy_lipschitz (fun k => ha k.succ) hf
    · intro y; exact ih (fun k => ha k.succ) y

lemma scalarHierarchy_clip_tendsto {d : ℕ} {a s : Fin d → ℝ} (ha : ∀ k,0≤a k)
    {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzWith L f) (x : ℝ) :
    Tendsto (fun m : ℕ => scalarHierarchy a s (fun y => max (-(m:ℝ)) (min (m:ℝ) (f y))) x)
      atTop (𝓝 (scalarHierarchy a s f x)) :=
  scalarHierarchy_tendsto ha (fun _m => clip_lipschitz hf _) hf (fun y => clip_tendsto (f y)) x

lemma logMean_mul_const {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (a : ℝ) {c : ℝ} (hc : c≠0) (f : Ω → ℝ) :
    logMean ν a (fun z => c*f z)=c*logMean ν (a*c) f := by
  by_cases ha : a=0
  · simp [ha,logMean_zero,integral_const_mul]
  · have hac : a*c≠0 := mul_ne_zero ha hc
    simp only [logMean,ha,hac,↓reduceIte]
    simp_rw [← mul_assoc]
    field_simp

lemma scalarHierarchy_mul_const {d : ℕ} (a s : Fin d → ℝ) {c : ℝ} (hc : c≠0)
    (f : ℝ → ℝ) (x : ℝ) :
    scalarHierarchy a s (fun y => c*f y) x=c*scalarHierarchy (fun k => a k*c) s f x := by
  induction d generalizing x with
  | zero => rfl
  | succ d ih =>
    change logMean _ _ _=c*logMean _ _ _
    simp_rw [ih]
    exact logMean_mul_const _ _ hc _

end SKCavity

end

end OAI
