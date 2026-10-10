import Mathlib
import OAI.Probability.ParisiFinite.HierarchyNumerator

namespace OAI

/-! Weighted Sum Pos. -/

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
open SKQAOA SKGaussian ParisiInterpolation
variable {ι : Type*} [Fintype ι]

lemma weighted_sum_pos {w f : ι → ℝ} (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1) (hf : ∀ i,0<f i) :
    0<∑ i,w i*f i := by
  have hex : ∃ i,0<w i := by
    by_contra! h
    have hnon := Finset.sum_nonpos (s:=Finset.univ) (fun i _ => h i)
    rw [hs] at hnon
    linarith
  obtain ⟨i,hi⟩ := hex
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hw j) (le_of_lt (hf j)))
    ⟨i,Finset.mem_univ _,mul_pos hi (hf i)⟩

lemma hierarchyMark_pos {d : ℕ} {w : ι → ℝ} (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1)
    (a : Fin (d+1) → ℝ) {x : (Fin d → ι) → ℝ} (hx : ∀ s,0≤x s ∧ x s≤1)
    {z : ℝ} (hz : |z|<1) : 0<hierarchyMark w d a x z := by
  induction d with
  | zero => exact Real.rpow_pos_of_pos (affine_mark_pos (hx _) hz) _
  | succ d ih =>
    exact Real.rpow_pos_of_pos (weighted_sum_pos hw hs (fun i => ih _ (fun s => hx _) )) _

lemma hierarchyMark_contDiffAt {d : ℕ} {w : ι → ℝ} (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1)
    (a : Fin (d+1) → ℝ) {x : (Fin d → ι) → ℝ} (hx : ∀ s,0≤x s ∧ x s≤1)
    {z : ℝ} (hz : |z|<1) (n : ℕ∞ω) : ContDiffAt ℝ n (hierarchyMark w d a x) z := by
  induction d with
  | zero =>
    apply ContDiffAt.rpow_const_of_ne
    · fun_prop
    · exact ne_of_gt (affine_mark_pos (hx _) hz)
  | succ d ih =>
    apply ContDiffAt.rpow_const_of_ne
    · exact ContDiffAt.sum fun i _ => contDiffAt_const.mul (ih _ (fun s => hx _))
    · exact ne_of_gt (weighted_sum_pos hw hs (fun i => hierarchyMark_pos hw hs _ (fun s => hx _) hz))

lemma hierarchyLog_contDiffAt {d : ℕ} {w : ι → ℝ} (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1)
    (a : Fin (d+1) → ℝ) {x : (Fin (d+1) → ι) → ℝ} (hx : ∀ s,0≤x s ∧ x s≤1)
    {z : ℝ} (hz : |z|<1) (n : ℕ∞ω) : ContDiffAt ℝ n (hierarchyLog w a x) z := by
  apply contDiffAt_const.mul
  apply (Real.contDiffAt_log.mpr _).comp z
    (ContDiffAt.sum fun i _ => contDiffAt_const.mul (hierarchyMark_contDiffAt hw hs a (fun s => hx _) hz n))
  exact ne_of_gt (weighted_sum_pos hw hs (fun i => hierarchyMark_pos hw hs a (fun s => hx _) hz))

lemma treeMarkMoment_mem_unit {d r : ℕ} {w : ι → ℝ} (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1)
    {x : (Fin d → ι) → ℝ} (hx : ∀ s,0≤x s ∧ x s≤1) (T : PartitionTree d r) :
    0≤treeMarkMoment w x T ∧ treeMarkMoment w x T≤1 := by
  induction d generalizing r with
  | zero => exact ⟨pow_nonneg (hx _).1 _,pow_le_one₀ (hx _).1 (hx _).2⟩
  | succ d ih =>
    rcases T with ⟨P,T⟩
    have hb (j : Fin P.length) : 0≤(∑ i,w i*treeMarkMoment w (fun s => x (Fin.cons i s)) (T j)) ∧
        (∑ i,w i*treeMarkMoment w (fun s => x (Fin.cons i s)) (T j))≤1 := by
      refine ⟨Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (ih (fun s => hx _) (T j)).1),?_⟩
      calc
        _ ≤ ∑ i,w i*1 := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (ih (fun s => hx _) (T j)).2 (hw i)
        _ = 1 := by simp [hs]
    exact ⟨Finset.prod_nonneg (fun j _ => (hb j).1),Finset.prod_le_one₀ (fun j _ => (hb j).1) (fun j _ => (hb j).2)⟩

lemma hierarchyMarkedMoment_mem_unit {d : ℕ} (μ : ProbabilityMeasure OverlapArray)
    (q : Fin (d+1) → ℝ) {w : ι → ℝ} (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1)
    {x : (Fin d → ι) → ℝ} (hx : ∀ s,0≤x s ∧ x s≤1) (n : ℕ) :
    0≤hierarchyMarkedMoment μ q w x n ∧ hierarchyMarkedMoment μ q w x n≤1 := by
  have hs1 : (∑ T : PartitionTree d n,(μ:Measure OverlapArray).real (hierarchyEvent (treeCodes T) q))≤1 := by
    simpa using sum_measureReal_le_measureReal_univ (μ:=(μ:Measure OverlapArray))
      (s:=Finset.univ) (fun T _ => hierarchyEvent_measurable (treeCodes T) q)
      (fun T _ U _ hTU => tree_hierarchy_disjoint hTU q)
  refine ⟨Finset.sum_nonneg (fun T _ => mul_nonneg measureReal_nonneg
    (treeMarkMoment_mem_unit hw hs hx T).1),?_⟩
  exact le_trans (Finset.sum_le_sum fun T _ => mul_le_of_le_one_right measureReal_nonneg
    (treeMarkMoment_mem_unit hw hs hx T).2) hs1

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal ContDiff
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation
variable {ι : Type*} [Fintype ι]

def hierarchyLogSeries {d : ℕ} (μ : ProbabilityMeasure OverlapArray) (q : Fin (d+1) → ℝ)
    (w : ι → ℝ) (x : (Fin d → ι) → ℝ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ (fun n => -hierarchyMarkedMoment μ q w x n/(n:ℝ))

lemma hierarchyLog_zero {d : ℕ} (w : ι → ℝ) (hw : ∑ i,w i=1)
    (a : Fin (d+1) → ℝ) (x : (Fin (d+1) → ι) → ℝ) : hierarchyLog w a x 0=0 := by
  simp [hierarchyLog,hierarchyMark_zero w hw,hw]

lemma hierarchyLogSeries_radius {d : ℕ} (μ : ProbabilityMeasure OverlapArray) (q : Fin (d+1) → ℝ)
    {w : ι → ℝ} (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1)
    {x : (Fin d → ι) → ℝ} (hx : ∀ s,0≤x s ∧ x s≤1) :
    (1:ℝ≥0∞)≤(hierarchyLogSeries μ q w x).radius := by
  apply FormalMultilinearSeries.le_radius_of_bound (C:=1) (r:=1)
  intro n
  simp only [hierarchyLogSeries,FormalMultilinearSeries.ofScalars,norm_smul,
    NNReal.coe_one,one_pow,mul_one,Real.norm_eq_abs,abs_div,abs_neg]
  rw [show |(n:ℝ)|=(n:ℝ) from abs_of_nonneg (Nat.cast_nonneg n)]
  by_cases hn : n=0
  · simp [hn]
  have hm := hierarchyMarkedMoment_mem_unit μ q hw hs hx n
  rw [abs_of_nonneg hm.1]
  have hn1 : (1:ℝ)≤n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hnorm : ‖ContinuousMultilinearMap.mkPiAlgebraFin ℝ n ℝ‖≤1 := by
    apply le_trans ContinuousMultilinearMap.norm_mkPiAlgebraFin_le
    norm_num
  calc
    _ ≤ (1:ℝ)/(n:ℝ)*1 := mul_le_mul (div_le_div_of_nonneg_right hm.2 (Nat.cast_nonneg _)) hnorm
      (norm_nonneg _) (by positivity)
    _ ≤ 1 := by rw [mul_one]; exact (div_le_one (by positivity)).mpr hn1

lemma GG_hierarchyLog_hasFPowerSeriesAt {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {d : ℕ} (q : Fin (d+2) → ℝ) (hq : Monotone q) (h0 : q 0 < -1)
    (h1 : q (Fin.last (d+1))<1) (ha : ∀ k : Fin (d+1),overlapDiscount μ (q k.succ)≠0)
    (w : ι → ℝ) (hw : ∑ i,w i=1) (x : (Fin (d+1) → ι) → ℝ) :
    HasFPowerSeriesAt (hierarchyLog w (fun k => overlapDiscount μ (q k.succ)) x)
      (hierarchyLogSeries μ q w x) 0 := by
  let a := fun k : Fin (d+1) => overlapDiscount μ (q k.succ)
  have hz : (∑ i,w i*hierarchyMark w d a (fun s => x (Fin.cons i s)) 0)=1 := by
    simp [hierarchyMark_zero w hw,hw]
  have hf : ContDiffAt ℝ ω (hierarchyLog w a x) 0 := by
    apply contDiffAt_const.mul
    apply (Real.contDiffAt_log.mpr _).comp 0
      (ContDiffAt.sum fun i _ => contDiffAt_const.mul (hierarchyMark_contDiffAt_zero w hw _ _ ω))
    rw [hz]; norm_num
  have h := hf.analyticAt.hasFPowerSeriesAt
  have he : (fun n => iteratedDeriv n (hierarchyLog w a x) 0/(n.factorial:ℝ))=
      (fun n => -hierarchyMarkedMoment μ q w x n/(n:ℝ)) := by
    funext n
    by_cases hn : n=0
    · subst n
      simp only [iteratedDeriv_zero,hierarchyLog_zero w hw,Nat.factorial_zero,Nat.cast_one,
        div_one,Nat.cast_zero,div_zero]
    · have hn' := Nat.pos_of_ne_zero hn
      rw [GG_hierarchy_log_derivative hG hgg hu q hq h0 h1 ha w hw x hn']
      have hf : (n.factorial:ℝ)=(n:ℝ)*((n-1).factorial:ℝ) := by
        exact_mod_cast (Nat.mul_factorial_pred hn).symm
      have hf0 : ((n-1).factorial:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hn0 : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr hn
      rw [hf]
      field_simp
  rw [he] at h
  exact h

 

theorem GG_hierarchy_log_identity {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {d : ℕ} (q : Fin (d+2) → ℝ) (hq : Monotone q) (h0 : q 0 < -1)
    (h1 : q (Fin.last (d+1))<1) (ha : ∀ k : Fin (d+1),overlapDiscount μ (q k.succ)≠0)
    {w : ι → ℝ} (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1)
    {x : (Fin (d+1) → ι) → ℝ} (hx : ∀ s,0≤x s ∧ x s≤1)
    {z : ℝ} (hz : |z|<1) :
    hierarchyLog w (fun k => overlapDiscount μ (q k.succ)) x z=
      (hierarchyLogSeries μ q w x).sum z := by
  let f := hierarchyLog w (fun k => overlapDiscount μ (q k.succ)) x
  let p := hierarchyLogSeries μ q w x
  have hr : (1:ℝ≥0∞)≤p.radius := hierarchyLogSeries_radius μ q hw hs hx
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
    filter_upwards [(GG_hierarchyLog_hasFPowerSeriesAt hG hgg hu q hq h0 h1 ha w hs x).eventually_hasSum] with t ht
    simpa only [zero_add,f,p,FormalMultilinearSeries.sum] using ht.tsum_eq.symm
  exact hf.eqOn_of_preconnected_of_eventuallyEq hp isPreconnected_Ioo (by constructor <;> norm_num)
    he (abs_lt.mp hz)

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal ContDiff
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation
variable {ι : Type*} [Fintype ι]

lemma hierarchyMark_one {d : ℕ} (w : ι → ℝ) (hw : ∑ i,w i=1)
    (a : Fin (d+1) → ℝ) (ha : ∀ k : Fin d,a k.succ≠0) {z : ℝ} (hz : z<1) :
    hierarchyMark w d a (fun _ => 1) z=(1-z)^(a 0) := by
  induction d with
  | zero => simp [hierarchyMark]
  | succ d ih =>
    change (∑ i,w i*hierarchyMark w d (fun k => a k.succ) (fun _ => 1) z)^(a 0/a 1)=_
    simp_rw [ih (fun k : Fin (d+1) => a k.succ) (fun k => ha k.succ)]
    rw [← Finset.sum_mul,hw,one_mul,← Real.rpow_mul (sub_pos.mpr hz).le]
    congr 1
    have h := ha 0
    change a 1≠0 at h
    simp only [Fin.succ_zero_eq_one]
    field_simp

lemma hierarchyLog_one {d : ℕ} (w : ι → ℝ) (hw : ∑ i,w i=1)
    (a : Fin (d+1) → ℝ) (ha : ∀ k,a k≠0) {z : ℝ} (hz : z<1) :
    hierarchyLog w a (fun _ => 1) z=Real.log (1-z) := by
  unfold hierarchyLog
  simp_rw [hierarchyMark_one w hw a (fun k => ha k.succ) hz]
  rw [← Finset.sum_mul,hw,one_mul,Real.log_rpow (sub_pos.mpr hz)]
  field_simp [ha 0]

lemma treeMarkMoment_one {d r : ℕ} (w : ι → ℝ) (hw : ∑ i,w i=1) (T : PartitionTree d r) :
    treeMarkMoment w (fun _ => 1) T=1 := by
  induction d generalizing r with
  | zero => exact one_pow r
  | succ d ih =>
    rcases T with ⟨P,T⟩
    simp [treeMarkMoment,ih,hw]

lemma hierarchy_partition_mass {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {d : ℕ} (q : Fin (d+2) → ℝ) (hq : Monotone q) (h0 : q 0 < -1)
    (h1 : q (Fin.last (d+1))<1) (ha : ∀ k : Fin (d+1),overlapDiscount μ (q k.succ)≠0)
    {n : ℕ} (hn : 0<n) :
    (∑ T : PartitionTree (d+1) n,(μ:Measure OverlapArray).real (hierarchyEvent (treeCodes T) q))=1 := by
  let w : Fin 1 → ℝ := fun _ => 1
  have hw : ∑ i,w i=1 := by simp [w]
  let a := fun k : Fin (d+1) => overlapDiscount μ (q k.succ)
  have he : hierarchyLog w a (fun _ => 1)=ᶠ[𝓝 (0:ℝ)] (fun z => Real.log (1-z)) := by
    filter_upwards [isOpen_Iio.mem_nhds (show (0:ℝ)<1 by norm_num)] with z hz
    exact hierarchyLog_one w hw a ha hz
  have hd := GG_hierarchy_log_derivative hG hgg hu q hq h0 h1 ha w hw (fun _ => 1) hn
  change iteratedDeriv n (hierarchyLog w a (fun _ => 1)) 0=_ at hd
  rw [he.iteratedDeriv_eq n] at hd
  have hf : iteratedDeriv n (fun z : ℝ => Real.log (1-z)) 0= -((n-1).factorial:ℝ) := by
    have hh := log_power_affine_derivative (a:=1) (by norm_num) hn
    simpa only [inv_one,Real.rpow_one,one_mul] using hh
  rw [hf] at hd
  simp only [hierarchyMarkedMoment,treeMarkMoment_one w hw,mul_one] at hd
  have hf0 : -((n-1).factorial:ℝ)≠0 := neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  exact mul_left_cancel₀ hf0 (by simpa using hd.symm)

lemma hierarchy_partition_cover {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {d : ℕ} (q : Fin (d+2) → ℝ) (hq : Monotone q) (h0 : q 0 < -1)
    (h1 : q (Fin.last (d+1))<1) (ha : ∀ k : Fin (d+1),overlapDiscount μ (q k.succ)≠0)
    {n : ℕ} (hn : 0<n) :
    (μ:Measure OverlapArray) (⋃ T : PartitionTree (d+1) n,hierarchyEvent (treeCodes T) q)=1 := by
  have h := measureReal_iUnion_fintype (μ:=(μ:Measure OverlapArray))
    (fun (T U : PartitionTree (d+1) n) hTU => tree_hierarchy_disjoint hTU q) (fun T => hierarchyEvent_measurable (treeCodes T) q)
  rw [hierarchy_partition_mass hG hgg hu q hq h0 h1 ha hn] at h
  apply (ENNReal.toReal_eq_one_iff _).mp
  exact h

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal ContDiff
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation
universe u
variable {ι : Type u} [Fintype ι]

 
@[reducible] def TreeDraw (ι : Type u) : {d r : ℕ} → PartitionTree d r → Type u
  | 0,_,_ => PUnit.{u+1}
  | _+1,_,⟨P,T⟩ => ∀ j : Fin P.length,ι × TreeDraw ι (T j)

instance treeDrawFintype {d r : ℕ} (T : PartitionTree d r) : Fintype (TreeDraw ι T) := by
  induction d generalizing r with
  | zero => exact inferInstanceAs (Fintype PUnit.{u+1})
  | succ d ih =>
    rcases T with ⟨P,T⟩
    letI (j : Fin P.length) : Fintype (TreeDraw ι (T j)) := ih (T j)
    exact inferInstanceAs (Fintype (∀ j : Fin P.length,ι × TreeDraw ι (T j)))

def treeDrawWeight (w : ι → ℝ) : {d r : ℕ} → (T : PartitionTree d r) → TreeDraw ι T → ℝ
  | 0,_,_,_ => 1
  | _+1,_,⟨_,T⟩,s => ∏ j,w (s j).1*treeDrawWeight w (T j) (s j).2

def treeDrawPath : {d r : ℕ} → (T : PartitionTree d r) → TreeDraw ι T → Fin r → (Fin d → ι)
  | 0,_,_,_,_ => fun k => Fin.elim0 k
  | _+1,_,⟨P,T⟩,s,i =>
    let j := P.equivSigma.symm i
    Fin.cons (s j.1).1 (treeDrawPath (T j.1) (s j.1).2 j.2)

omit [Fintype ι] in
lemma treeDrawPath_emb {d r : ℕ} (P : OrderedFinpartition r) (T : ∀ j,PartitionTree d (P.partSize j))
    (s : TreeDraw ι (d:=d+1) (⟨P,T⟩ : PartitionTree (d+1) r)) (j : Fin P.length) (i : Fin (P.partSize j)) :
    treeDrawPath (d:=d+1) (⟨P,T⟩ : PartitionTree (d+1) r) s (P.emb j i)=
      Fin.cons (s j).1 (treeDrawPath (T j) (s j).2 i) := by
  simp only [treeDrawPath]
  rw [show P.equivSigma.symm (P.emb j i)=⟨j,i⟩ from P.equivSigma.symm_apply_apply ⟨j,i⟩]

omit [Fintype ι] in
lemma treeDrawWeight_nonneg (w : ι → ℝ) (hw : ∀ i,0≤w i) {d r : ℕ} (T : PartitionTree d r)
    (s : TreeDraw ι T) : 0≤treeDrawWeight w T s := by
  induction d generalizing r with
  | zero => exact zero_le_one
  | succ d ih =>
    rcases T with ⟨P,T⟩
    exact Finset.prod_nonneg fun j _ => mul_nonneg (hw _) (ih _ _)

lemma treeDrawWeight_sum (w : ι → ℝ) (hw : ∑ i,w i=1) {d r : ℕ} (T : PartitionTree d r) :
    (∑ s : TreeDraw ι T,treeDrawWeight w T s)=1 := by
  induction d generalizing r with
  | zero => change (∑ _ : PUnit.{u+1},(1:ℝ))=1; simp
  | succ d ih =>
    rcases T with ⟨P,T⟩
    change (∑ s : ∀ j,ι × TreeDraw ι (T j),∏ j,w (s j).1*treeDrawWeight w (T j) (s j).2)=1
    rw [← Fintype.prod_sum (fun j (s : ι × TreeDraw ι (T j)) => w s.1*treeDrawWeight w (T j) s.2)]
    simp only [Fintype.sum_prod_type,← Finset.mul_sum,ih,mul_one,hw,Finset.prod_const_one]

lemma treeDraw_product {d r : ℕ} (w : ι → ℝ) (x : (Fin d → ι) → ℝ) (T : PartitionTree d r) :
    (∑ s : TreeDraw ι T,treeDrawWeight w T s*∏ j,x (treeDrawPath T s j))=treeMarkMoment w x T := by
  induction d generalizing r with
  | zero =>
    change (∑ _ : PUnit.{u+1},(1:ℝ)*∏ _ : Fin r,x (fun i => Fin.elim0 i))=x (fun i => Fin.elim0 i)^r
    simp
  | succ d ih =>
    rcases T with ⟨P,T⟩
    change (∑ s : ∀ j,ι × TreeDraw ι (T j),(∏ j,w (s j).1*treeDrawWeight w (T j) (s j).2)*
      ∏ k,x (treeDrawPath (d:=d+1) (⟨P,T⟩ : PartitionTree (d+1) r) s k))=_
    have he (s : TreeDraw ι (d:=d+1) (⟨P,T⟩ : PartitionTree (d+1) r)) :
        (∏ k,x (treeDrawPath (d:=d+1) (⟨P,T⟩ : PartitionTree (d+1) r) s k))=
          ∏ j,∏ i,x (Fin.cons (s j).1 (treeDrawPath (T j) (s j).2 i)) := by
      rw [← P.equivSigma.prod_comp,Fintype.prod_sigma]
      change (∏ j,∏ i,x (treeDrawPath (d:=d+1) (⟨P,T⟩ : PartitionTree (d+1) r) s (P.emb j i)))=_
      simp only [treeDrawPath_emb]
    simp_rw [he,← Finset.prod_mul_distrib,mul_assoc]
    rw [← Fintype.prod_sum (fun j (s : ι × TreeDraw ι (T j)) => w s.1*(treeDrawWeight w (T j) s.2*∏ i,x (Fin.cons s.1 (treeDrawPath (T j) s.2 i))))]
    change (∏ j,∑ si : ι × TreeDraw ι (T j),w si.1*(treeDrawWeight w (T j) si.2*
      ∏ i,x (Fin.cons si.1 (treeDrawPath (T j) si.2 i))))=_
    simp only [Fintype.sum_prod_type,← Finset.mul_sum,treeMarkMoment]
    apply Finset.prod_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact ih (fun s => x (Fin.cons i s)) (T j)

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal ContDiff
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

lemma hierarchy_numerator_mass_nz {d : ℕ} (a : Fin (d+1) → ℝ) (ha : ∀ k,a k≠0)
    {n : ℕ} (hn : 0<n) :
    (∑ T : PartitionTree (d+1) n,hierarchyNumerator (Fin.cons 0 a) (treeCodes T))=((n-1).factorial:ℝ) := by
  let w : Fin 1 → ℝ := fun _ => 1
  have hw : ∑ i,w i=1 := by simp [w]
  have he : hierarchyLog w a (fun _ => 1)=ᶠ[𝓝 (0:ℝ)] (fun z => Real.log (1-z)) := by
    filter_upwards [isOpen_Iio.mem_nhds (show (0:ℝ)<1 by norm_num)] with z hz
    exact hierarchyLog_one w hw a ha hz
  have hd := hierarchyLog_derivative w hw a ha (fun _ => 1) hn
  rw [he.iteratedDeriv_eq n] at hd
  have hf : iteratedDeriv n (fun z : ℝ => Real.log (1-z)) 0= -((n-1).factorial:ℝ) := by
    have hh := log_power_affine_derivative (a:=1) (by norm_num) hn
    simpa only [inv_one,Real.rpow_one,one_mul] using hh
  rw [hf] at hd
  simp only [hierarchyCoefficient,treeMarkMoment_one w hw,mul_one] at hd
  linarith

lemma continuous_hierarchyNumerator {d r : ℕ} (c : Fin (d+1) → Fin r → ℕ) :
    Continuous (fun a : Fin (d+1) → ℝ => hierarchyNumerator a c) := by
  unfold hierarchyNumerator edgeFactor leafFactor branchFactor blockFactor
  fun_prop

lemma hierarchy_numerator_mass {d : ℕ} (a : Fin (d+1) → ℝ) (ha : ∀ k,0≤a k)
    {n : ℕ} (hn : 0<n) :
    (∑ T : PartitionTree (d+1) n,hierarchyNumerator (Fin.cons 0 a) (treeCodes T))=((n-1).factorial:ℝ) := by
  let b : ℕ → Fin (d+1) → ℝ := fun m k => a k+1/(m+1:ℕ)
  have hb : ∀ m k,b m k≠0 := by
    intro m k
    have hh : (0:ℝ)<1/(m+1:ℕ) := by positivity
    exact ne_of_gt (add_pos_of_nonneg_of_pos (ha k) hh)
  have hlim : Tendsto b atTop (𝓝 a) := by
    apply tendsto_pi_nhds.mpr
    intro k
    simpa only [add_zero] using tendsto_const_nhds.add tendsto_succ_reciprocal
  have hc : Continuous (fun a : Fin (d+1) → ℝ => ∑ T : PartitionTree (d+1) n,
      hierarchyNumerator (Fin.cons 0 a) (treeCodes T)) := by
    apply continuous_finsetSum
    intro T _
    apply (continuous_hierarchyNumerator (treeCodes T)).comp
    apply continuous_pi
    intro k
    induction k using Fin.cases with
    | zero => exact continuous_const
    | succ k => exact continuous_apply k
  have h := hc.continuousAt.tendsto.comp hlim
  have he : (fun m => ∑ T : PartitionTree (d+1) n,hierarchyNumerator (Fin.cons 0 (b m)) (treeCodes T))=
      (fun _ : ℕ => ((n-1).factorial:ℝ)) := by
    funext m
    exact hierarchy_numerator_mass_nz (b m) (hb m) hn
  simp only [Function.comp_def] at h
  rw [he] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

lemma hierarchy_partition_mass_all {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {d : ℕ} (q : Fin (d+2) → ℝ) (hq : Monotone q) (h0 : q 0 < -1)
    (h1 : q (Fin.last (d+1))<1) {n : ℕ} (hn : 0<n) :
    (∑ T : PartitionTree (d+1) n,(μ:Measure OverlapArray).real (hierarchyEvent (treeCodes T) q))=1 := by
  have ha : ∀ k : Fin (d+1),0≤overlapDiscount μ (q k.succ) := fun k => ENNReal.toReal_nonneg
  have he : Fin.cons 0 (fun k : Fin (d+1) => overlapDiscount μ (q k.succ))=(fun k => overlapDiscount μ (q k)) := by
    funext k
    induction k using Fin.cases with
    | zero => exact (overlapDiscount_below μ h0).symm
    | succ k => rfl
  have hh := hierarchy_numerator_mass (fun k : Fin (d+1) => overlapDiscount μ (q k.succ)) ha hn
  rw [he] at hh
  have ht (T : PartitionTree (d+1) n) : hierarchyNumerator (fun k => overlapDiscount μ (q k)) (treeCodes T)=
      ((n-1).factorial:ℝ)*(μ:Measure OverlapArray).real (hierarchyEvent (treeCodes T) q) :=
    (GG_hierarchy_EPPF hG hgg hu hn (treeCodes T) (treeCodes_nested T) (fun i j => by simp) q hq h1).symm
  simp_rw [ht] at hh
  rw [← Finset.mul_sum] at hh
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) (by simpa using hh)

lemma hierarchy_partition_cover_all {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {d : ℕ} (q : Fin (d+2) → ℝ) (hq : Monotone q) (h0 : q 0 < -1)
    (h1 : q (Fin.last (d+1))<1) {n : ℕ} (hn : 0<n) :
    (μ:Measure OverlapArray) (⋃ T : PartitionTree (d+1) n,hierarchyEvent (treeCodes T) q)=1 := by
  have h := measureReal_iUnion_fintype (μ:=(μ:Measure OverlapArray))
    (fun (T U : PartitionTree (d+1) n) hTU => tree_hierarchy_disjoint hTU q) (fun T => hierarchyEvent_measurable (treeCodes T) q)
  rw [hierarchy_partition_mass_all hG hgg hu q hq h0 h1 hn] at h
  exact (ENNReal.toReal_eq_one_iff _).mp h

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

def NonnegativeArrays : Set OverlapArray := {R | ∀ i j,0≤(R i j:ℝ)}

lemma isClosed_NonnegativeArrays : IsClosed NonnegativeArrays := by
  unfold NonnegativeArrays
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_le continuous_const (by fun_prop)

lemma negative_pair_event_zero {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (_hu : (μ:Measure OverlapArray) UltrametricArrays=1) (hex : FiniteExchangeable μ)
    (i j : ℕ) {q : ℝ} (hq : q<0) :
    (μ:Measure OverlapArray) {R | (R i j:ℝ)≤q}=0 := by
  by_cases hij : i=j
  · subst j
    have h : ∀ᵐ R ∂(μ:Measure OverlapArray),¬(R i i:ℝ)≤q := by
      filter_upwards [ae_full_probability μ isClosed_GramArrays.measurableSet hG] with R hR
      rw [hR.2.1]
      linarith
    simpa only [not_not] using ae_iff.mp h
  let e : Fin 2 → ℕ := ![i,j]
  have he : Function.Injective e := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [e]
  have hB : MeasurableSet {T : OverlapBlock 2 | (T 0 1:ℝ)≤q} := measurableSet_le (by fun_prop) measurable_const
  have heq := exchangeable_event hex e he hB
  change (μ:Measure OverlapArray) {R | (R i j:ℝ)≤q}=(μ:Measure OverlapArray) {R | (R 0 1:ℝ)≤q} at heq
  rw [heq]
  have hh := GG_negative_threshold_zero hG hgg hq
  unfold Measure.real at hh
  have hz : (entryLaw μ 0 1) {x | (x:ℝ)≤q}=0 := ((ENNReal.toReal_eq_zero_iff _).mp hh).resolve_right (measure_ne_top _ _)
  unfold entryLaw at hz
  rw [Measure.map_apply (by fun_prop) (measurableSet_le (by fun_prop) measurable_const)] at hz
  exact hz

theorem GG_nonnegative_arrays {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1) (hex : FiniteExchangeable μ) :
    (μ:Measure OverlapArray) NonnegativeArrays=1 := by
  have h (i j m : ℕ) : ∀ᵐ R ∂(μ:Measure OverlapArray), (-1:ℝ)/(m+1:ℕ)<(R i j:ℝ) := by
    apply ae_iff.mpr
    simp only [not_lt]
    exact negative_pair_event_zero hG hgg hu hex i j (div_neg_of_neg_of_pos (by norm_num) (by positivity))
  have hh : ∀ᵐ R ∂(μ:Measure OverlapArray),R∈NonnegativeArrays := by
    simp only [NonnegativeArrays,Set.mem_ofPred_eq]
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro j
    filter_upwards [ae_all_iff.mpr (h i j)] with R hR
    have ht : Tendsto (fun m : ℕ => (-1:ℝ)/(m+1:ℕ)) atTop (𝓝 (0:ℝ)) := by
      simpa only [neg_div,neg_zero] using tendsto_succ_reciprocal.neg
    exact le_of_tendsto ht (Filter.Eventually.of_forall fun m => (hR m).le)
  have hz : (μ:Measure OverlapArray) NonnegativeArraysᶜ=0 := ae_iff.mp hh
  rw [measure_compl isClosed_NonnegativeArrays.measurableSet (measure_ne_top _ _)] at hz
  apply le_antisymm (by simpa only [measure_univ] using (measure_mono (Set.subset_univ NonnegativeArrays) : (μ:Measure OverlapArray) NonnegativeArrays≤(μ:Measure OverlapArray) Set.univ))
  exact tsub_eq_zero_iff_le.mp (by simpa only [measure_univ] using hz)

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

abbrev CodeLabel {r : ℕ} (c : Fin r → ℕ) := {l : ℕ // l∈Finset.univ.image c}

def codeGaussianCoeff {d r : ℕ} (c : Fin d → Fin r → ℕ) (v : Fin d → ℝ)
    (i : Fin r) (k : Σ k : Fin d,CodeLabel (c k)) : ℝ :=
  if c k.1 i=k.2.val then Real.sqrt (v k.1) else 0

lemma kernel_codeGaussianCoeff {d r : ℕ} (c : Fin d → Fin r → ℕ) (v : Fin d → ℝ)
    (hv : ∀ k,0≤v k) (i j : Fin r) :
    kernel (codeGaussianCoeff c v) i j=∑ k,if c k i=c k j then v k else 0 := by
  unfold kernel
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k _
  let l : CodeLabel (c k) := ⟨c k i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  rw [Fintype.sum_eq_single l]
  · dsimp [codeGaussianCoeff,l]
    by_cases h : c k i=c k j
    · simp [h,← pow_two,Real.sq_sqrt (hv k)]
    · simp [h,Ne.symm h]
  · intro t ht
    have h : c k i≠t.val := by
      intro he
      apply ht
      exact Subtype.ext he.symm
    simp [codeGaussianCoeff,h]

lemma codeKernel_nonneg {d r : ℕ} (c : Fin d → Fin r → ℕ) (v : Fin d → ℝ)
    (hv : ∀ k,0≤v k) (i j : Fin r) :
    0≤∑ k,if c k i=c k j then v k else 0 :=
  Finset.sum_nonneg fun k _ => by split_ifs <;> simp_all

lemma codeKernel_le_one {d r : ℕ} (c : Fin d → Fin r → ℕ) (v : Fin d → ℝ)
    (hv : ∀ k,0≤v k) (hs : ∑ k,v k=1) (i j : Fin r) :
    (∑ k,if c k i=c k j then v k else 0)≤1 := by
  rw [← hs]
  exact Finset.sum_le_sum fun k _ => by split_ifs <;> simp_all

lemma kernel_quadratic_nonneg {r : ℕ} {κ : Type*} [Fintype κ]
    (A : Fin r → κ → ℝ) (x : Fin r → ℝ) :
    0≤∑ i,∑ j,x i*x j*kernel A i j := by
  have he : (∑ i,∑ j,x i*x j*kernel A i j)=(∑ k,(∑ i,x i*A i k)^2) := by
    simp only [kernel,Finset.mul_sum,pow_two,Finset.sum_mul]
    rw [Finset.sum_comm]
    conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  exact Finset.sum_nonneg fun k _ => sq_nonneg _

def codeGramBlock {d r : ℕ} (c : Fin d → Fin r → ℕ) (v : Fin d → ℝ)
    (hv : ∀ k,0≤v k) (hs : ∑ k,v k=1) : GramBlock r := by
  let R : OverlapBlock r := fun i j => ⟨∑ k,if c k i=c k j then v k else 0,
    ⟨(by linarith [codeKernel_nonneg c v hv i j]),codeKernel_le_one c v hv hs i j⟩⟩
  refine ⟨R,?_,?_,?_⟩
  · intro i j
    apply Subtype.ext
    change (∑ k,if c k i=c k j then v k else 0) = ∑ k,if c k j=c k i then v k else 0
    simp only [eq_comm]
  · intro i
    simpa [R] using hs
  · intro x
    have h := kernel_quadratic_nonneg (codeGaussianCoeff c v) x
    simpa only [kernel_codeGaussianCoeff c v hv,R] using h

lemma codeGramBlock_entry {d r : ℕ} (c : Fin d → Fin r → ℕ) (v : Fin d → ℝ)
    (hv : ∀ k,0≤v k) (hs : ∑ k,v k=1) (i j : Fin r) :
    ((codeGramBlock c v hv hs).val i j:ℝ)=∑ k,if c k i=c k j then v k else 0 := rfl

lemma cavityGramObservable_lipschitz {r : ℕ} (hr : 0<r) (β : ℝ) (T S : GramBlock r) :
    |cavityGramObservable T β-cavityGramObservable S β|≤(β^2*Real.pi)*dist T S := by
  have h1 := coshGramPressure_lipschitz hr T S β
  have h2 := squareGramPressure_lipschitz hr T S β
  have he : cavityGramObservable T β-cavityGramObservable S β=
      (coshGramPressure T β-coshGramPressure S β)-(squareGramPressure T β-squareGramPressure S β) := by
    unfold cavityGramObservable
    ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith)

def stepCovariance {d : ℕ} (q v : Fin d → ℝ) (x : ℝ) : ℝ :=
  ∑ k,if q k<x then v k else 0

lemma codeGramBlock_on_event {d r : ℕ} (T : PartitionTree d r) (q v : Fin (d+1) → ℝ)
    (hv : ∀ k,0≤v k) (hs : ∑ k,v k=1) {R : OverlapArray}
    (hR : R∈hierarchyEvent (treeCodes T) q) (i j : Fin r) :
    ((codeGramBlock (treeCodes T) v hv hs).val i j:ℝ)=stepCovariance q v (R i j) := by
  rw [codeGramBlock_entry]
  unfold stepCovariance
  apply Finset.sum_congr rfl
  intro k _
  simp only [← hR k i j,blockOfArray]

lemma gramBlock_dist_le {r : ℕ} (T S : GramBlock r) {δ : ℝ} (hδ : 0≤δ)
    (h : ∀ i j,|(T.val i j:ℝ)-(S.val i j:ℝ)|≤δ) : dist T S≤δ := by
  apply (dist_pi_le_iff hδ).mpr
  intro i
  apply (dist_pi_le_iff hδ).mpr
  intro j
  exact h i j

lemma codeCavity_error {d r : ℕ} (hr : 0<r) (T : PartitionTree d r) (q v : Fin (d+1) → ℝ)
    (hv : ∀ k,0≤v k) (hs : ∑ k,v k=1) {δ : ℝ} (hδ : 0≤δ)
    (hstep : ∀ x : ℝ,0≤x → x≤1 → |x-stepCovariance q v x|≤δ)
    {R : OverlapArray} (hG : R∈GramArrays) (hpos : ∀ i j,0≤(R i j:ℝ))
    (hR : R∈hierarchyEvent (treeCodes T) q) (β : ℝ) :
    |cavityObservable hr β (blockOfArray r R)-cavityGramObservable (codeGramBlock (treeCodes T) v hv hs) β|≤
      β^2*Real.pi*δ := by
  let B : GramBlock r := ⟨blockOfArray r R,GramArrays_block hG r⟩
  rw [show blockOfArray r R=B.val from rfl,cavityObservable_on_Gram hr β B]
  have hd : dist B (codeGramBlock (treeCodes T) v hv hs)≤δ := by
    apply gramBlock_dist_le _ _ hδ
    intro i j
    rw [codeGramBlock_on_event T q v hv hs hR]
    exact hstep (R i j) (hpos i j) (R i j).property.2
  exact (cavityGramObservable_lipschitz hr β B _).trans
    (mul_le_mul_of_nonneg_left hd (by positivity))

end SKCavity

end

end OAI
