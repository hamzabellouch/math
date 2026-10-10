import Mathlib
import OAI.Probability.IsingPerceptron.TimeIncrement
import OAI.Probability.IsingPerceptron.VariationalDefs

namespace OAI

/-! Field Chain. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def chainPartition (n : ℕ) (ζ : Fin (n+2) → ℝ) (hz : StrictMono ζ)
    (hfirst : ζ 0=0) (hlast : ζ (Fin.last (n+1))=1) : Partition :=
  ⟨n+1,by omega,ζ,hz,hfirst,hlast⟩

def chainFieldStep (n : ℕ) (ζ : Fin (n+2) → ℝ) (hz : StrictMono ζ)
    (hfirst : ζ 0=0) (hlast : ζ (Fin.last (n+1))=1)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) : FieldStep where
  partition := chainPartition n ζ hz hfirst hlast
  value i := h i
  nonneg _ := h0.trans (hh (Nat.zero_le _))
  ordered := fun _ _ hi => hh hi

def chainExponent {n : ℕ} (ζ : Fin (n+2) → ℝ) (i : ℕ) : ℝ :=
  ζ ⟨min (i+1) (n+1),by omega⟩

lemma chainExponent_apply {n : ℕ} (ζ : Fin (n+2) → ℝ) {i : ℕ} (hi : i<n) :
    chainExponent ζ i = ζ ⟨i+1,by omega⟩ := by simp [chainExponent,min_eq_left (by omega : i+1 ≤ n+1)]

lemma chainExponent_admissible {n : ℕ} {ζ : Fin (n+2) → ℝ} (hz : StrictMono ζ)
    (hfirst : ζ 0=0) (hlast : ζ (Fin.last (n+1))=1) : CascadeExponents n (chainExponent ζ) := by
  constructor
  · intro i hi
    rw [chainExponent_apply ζ hi]
    constructor
    · rw [← hfirst]
      exact hz (by change (0 : ℕ) < i+1; omega)
    · rw [← hlast]
      exact hz (by change i+1 < n+1; omega)
  · intro i j hij hj
    rw [chainExponent_apply ζ (by omega),chainExponent_apply ζ hj]
    exact hz (by simpa using (show i+1<j+1 by omega))

lemma stepAt_chain {n : ℕ} (ζ : Fin (n+2) → ℝ) (hz : StrictMono ζ)
    (hfirst : ζ 0=0) (hlast : ζ (Fin.last (n+1))=1)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) {i : ℕ} (hi : i≤n) :
    stepAt (chainFieldStep n ζ hz hfirst hlast h hh h0) i = h i := by
  simp [stepAt,chainFieldStep,chainPartition,show i<n+1 by omega]

lemma fieldRecursion_chain (n : ℕ) (ζ : Fin (n+2) → ℝ) (hz : StrictMono ζ)
    (hfirst : ζ 0=0) (hlast : ζ (Fin.last (n+1))=1)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) :
    fieldRecursion (chainFieldStep n ζ hz hfirst hlast h hh h0) =
      magneticFieldValue n (chainExponent ζ) h := by
  let F := chainFieldStep n ζ hz hfirst hlast h hh h0
  have hat (i : ℕ) (hi : i≤n) : stepAt F i=h i := stepAt_chain ζ hz hfirst hlast h hh h0 hi
  let T := List.ofFn (fun i : Fin n => ((pathAmplitude h (i+1))^2,chainExponent ζ i))
  have ht : (List.ofFn (fun i : Fin n =>
      (stepAt F (i.val+1)-(if i.val+1=0 then 0 else stepAt F (i.val+1-1)),
        ζ i.succ.castSucc))) = T := by
    apply congrArg List.ofFn
    funext i
    simp only [Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel,hat _ (by omega : i.val+1≤n),hat _ (by omega : i.val≤n),
      pathAmplitude_sq hh h0,pathIncrement,chainExponent_apply ζ i.isLt]
    rfl
  have hd : ∀ sd ∈ T, 0 < sd.2 := by
    intro sd hs
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hs
    exact ((chainExponent_admissible hz hfirst hlast).1 i i.isLt).1
  have hg := magneticRecursion_growth n (fun i => pathAmplitude h (i+1)) (chainExponent ζ)
    (fun i hi => ((chainExponent_admissible hz hfirst hlast).1 i hi).1)
  have hf : T.foldr (fun sd U => gaussianTransform sd.1 sd.2 U) (fun x => Real.log (Real.cosh x)) =
      magneticRecursion n (fun i => pathAmplitude h (i+1)) (chainExponent ζ) :=
    (magneticRecursion_eq_fold n (fun i => pathAmplitude h (i+1)) (chainExponent ζ)).symm
  change (List.ofFn (fun i : Fin (n+1) =>
    (stepAt F i-(if i.val=0 then 0 else stepAt F (i.val-1)), ζ i.castSucc))).foldr
      (fun sd U => gaussianTransform sd.1 sd.2 U)
      (fun x => Real.log (Real.cosh x)-stepAt F n/2) 0 = _
  rw [List.ofFn_succ,List.foldr_cons]
  simp only [Fin.val_zero,ite_true,Fin.castSucc_zero,hfirst,hat 0 (Nat.zero_le _),sub_zero,
    Fin.val_succ,hat n le_rfl]
  rw [ht]
  have hc : (fun x => Real.log (Real.cosh x)-h n/2) = (fun x => -h n/2+Real.log (Real.cosh x)) := by
    ext x; ring
  rw [hc,gaussianFold_const_add T hd measurable_logCosh logCosh_linearGrowth, hf,
    gaussianTransform_const_add hg.1 hg.2]
  simp only [gaussianTransform,ite_true,zero_add,magneticFieldValue,pathAmplitude,pathIncrement]
  ring

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma jointPair_measurable : Measurable (fun x : JointArray => (spinArray x 0 1,treeArray x 0 1)) := by
  unfold spinArray treeArray; fun_prop
lemma jointSpin_measurable : Measurable (fun x : JointArray => spinArray x 0 1) := by
  unfold spinArray; fun_prop

lemma jointSpin_unit_support {μ : ProbabilityMeasure JointArray}
    (hp : ∀ᵐ x ∂(μ : Measure JointArray), 0 ≤ spinArray x 0 1) :
    ∀ᵐ r ∂(μ : Measure JointArray).map (fun x => spinArray x 0 1), r ∈ Icc (0:ℝ) 1 := by
  apply (ae_map_iff jointSpin_measurable.aemeasurable measurableSet_Icc).mpr
  filter_upwards [hp] with x hx
  exact ⟨hx,(x (0,1)).1.2.2⟩

 

lemma joint_depthTail_quantile {μ : ProbabilityMeasure JointArray} {n : ℕ}
    (ζ : Fin (n+2) → ℝ) (hz0 : ζ 0=0)
    (hp : ∀ᵐ x ∂(μ : Measure JointArray), 0 ≤ spinArray x 0 1)
    (ho : let ρ := (μ : Measure JointArray).map (fun x => (spinArray x 0 1,treeArray x 0 1))
      ∀ x ∈ ρ.support, ∀ y ∈ ρ.support, x.1 < y.1 → x.2 ≤ y.2)
    (hl : ∀ᵐ x ∂(μ : Measure JointArray), treeArray x 0 1 ∈ treeLevels n)
    (ht : ∀ d : Fin n, (∫ x, treeTail n d (treeArray x 0 1) ∂(μ : Measure JointArray))=1-chainExponent ζ d)
    (j : Fin (n+1)) :
    (∫ x, spinArray x 0 1*depthTail n j (treeArray x 0 1) ∂(μ : Measure JointArray)) =
      ∫ u in Ioi (ζ j.castSucc), quantileFunction ((μ : Measure JointArray).map (fun x => spinArray x 0 1)) u ∂pathMeasure := by
  let ρ : Measure (ℝ × ℝ) := (μ : Measure JointArray).map (fun x => (spinArray x 0 1,treeArray x 0 1))
  let ν : Measure ℝ := (μ : Measure JointArray).map (fun x => spinArray x 0 1)
  let : IsProbabilityMeasure ρ :=
    (Measure.isProbabilityMeasure_map_iff jointPair_measurable.aemeasurable).mpr inferInstance
  let : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff jointSpin_measurable.aemeasurable).mpr inferInstance
  have hν := jointSpin_unit_support hp
  have hf : ρ.map Prod.fst=ν := by
    rw [Measure.map_map measurable_fst jointPair_measurable]
    rfl
  have hs : ∀ᵐ x ∂ρ, x.1∈Icc (0:ℝ) 1 ∧ x.2∈Icc (0:ℝ) 1 := by
    apply (ae_map_iff jointPair_measurable.aemeasurable
      ((measurableSet_Icc.preimage measurable_fst).inter (measurableSet_Icc.preimage measurable_snd))).mpr
    filter_upwards [hp] with x hx
    exact ⟨⟨hx,(x (0,1)).1.2.2⟩,(x (0,1)).2.2⟩
  by_cases hj : j.val=0
  · have je : j=0 := Fin.ext hj
    subst j
    simp only [Fin.val_zero,depthTail,ite_true,mul_one,Fin.castSucc_zero,hz0]
    have he := congrArg (fun η : Measure ℝ => ∫ t, t ∂η) (quantileFunction_law hν)
    rw [integral_map (monotone_quantileFunction hν).measurable.aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun t : ℝ => t) _),
      integral_map jointSpin_measurable.aemeasurable (by fun_prop : AEStronglyMeasurable (fun t : ℝ => t) _)] at he
    change (∫ x, spinArray x 0 1 ∂(μ : Measure JointArray)) = ∫ u in Ioi 0, quantileFunction ν u ∂pathMeasure
    rw [← he]
    congr 1
    change volume.restrict (Ioo (0:ℝ) 1)=(volume.restrict (Ioo (0:ℝ) 1)).restrict (Ioi 0)
    rw [Measure.restrict_restrict measurableSet_Ioi,inter_eq_right.mpr]
    exact Ioo_subset_Ioi_self
  · let d : Fin n := ⟨j.val-1,by omega⟩
    have hd : d.val+1=j.val := by dsimp [d]; omega
    have hζ : chainExponent ζ d=ζ j.castSucc := by
      rw [chainExponent_apply ζ d.isLt]
      congr 1
      exact Fin.ext hd
    have hlev : ∀ᵐ x ∂ρ, x.2∈treeLevels n :=
      (ae_map_iff jointPair_measurable.aemeasurable ((isClosed_treeLevels n).measurableSet.preimage measurable_snd)).mpr hl
    have htail : (∫ x, treeTail n d x.2 ∂ρ)=1-ζ j.castSucc := by
      rw [integral_map jointPair_measurable.aemeasurable
        (show AEStronglyMeasurable (fun x : ℝ × ℝ => treeTail n d x.2) _ from ((continuous_treeTail n d).comp continuous_snd).aestronglyMeasurable)]
      simpa only [hζ] using ht d
    have H := ordered_pair_tree_tail_integral ho hs hlev htail
    rw [hf,integral_map jointPair_measurable.aemeasurable
      (show AEStronglyMeasurable (fun x : ℝ × ℝ => x.1*treeTail n d x.2) _ from (continuous_fst.mul ((continuous_treeTail n d).comp continuous_snd)).aestronglyMeasurable)] at H
    simpa only [depthTail,hj,ite_false,d,pathMeasure,unitUniform] using H

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def finiteStepFunction {k : ℕ} (ζ : Fin (k+1) → ℝ) (v : Fin k → ℝ) (u : ℝ) : ℝ :=
  ∑ i, if ζ i.castSucc < u ∧ u < ζ i.succ then v i else 0

lemma finite_cells_disjoint {k : ℕ} {ζ : Fin (k+1) → ℝ} (hz : StrictMono ζ)
    {i j : Fin k} {u : ℝ} (hi : ζ i.castSucc < u ∧ u < ζ i.succ)
    (hj : ζ j.castSucc < u ∧ u < ζ j.succ) : i=j := by
  apply le_antisymm <;> by_contra h
  · have he : j.succ ≤ i.castSucc := by change j.val+1 ≤ i.val; omega
    have H := hz.monotone he
    linarith
  · have he : i.succ ≤ j.castSucc := by change i.val+1 ≤ j.val; omega
    have H := hz.monotone he
    linarith

lemma measurable_finiteStepFunction {k : ℕ} (ζ : Fin (k+1) → ℝ) (v : Fin k → ℝ) :
    Measurable (finiteStepFunction ζ v) := by
  unfold finiteStepFunction
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite measurableSet_Ioo measurable_const measurable_const

lemma finiteStepFunction_on_cell {k : ℕ} {ζ : Fin (k+1) → ℝ} (hz : StrictMono ζ)
    (v : Fin k → ℝ) {i : Fin k} {u : ℝ} (hi : ζ i.castSucc < u ∧ u < ζ i.succ) :
    finiteStepFunction ζ v u = v i := by
  unfold finiteStepFunction
  rw [Finset.sum_eq_single i]
  · exact ite_eq_left hi
  · intro j _ hji
    exact ite_eq_right (fun hj => hji (finite_cells_disjoint hz hj hi))
  · simp

lemma finiteStepFunction_mul {k : ℕ} {ζ : Fin (k+1) → ℝ} (hz : StrictMono ζ)
    (v w : Fin k → ℝ) :
    (fun u => finiteStepFunction ζ v u*finiteStepFunction ζ w u) = finiteStepFunction ζ (fun i => v i*w i) := by
  ext u
  unfold finiteStepFunction
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : ζ i.castSucc<u ∧ u<ζ i.succ
  · simp only [hi]
    change v i*finiteStepFunction ζ w u=v i*w i
    rw [finiteStepFunction_on_cell hz w hi]
  · simp only [hi,ite_false,zero_mul]

lemma integral_finiteStepFunction {k : ℕ} (ζ : Fin (k+1) → ℝ)
    (hz : StrictMono ζ) (hz0 : ζ 0=0) (hz1 : ζ (Fin.last k)=1) (v : Fin k → ℝ) :
    (∫ u, finiteStepFunction ζ v u ∂pathMeasure) = ∑ i, (ζ i.succ-ζ i.castSucc)*v i := by
  classical
  let : IsFiniteMeasure pathMeasure := by
    change IsFiniteMeasure (volume.restrict (Ioo (0:ℝ) 1))
    infer_instance
  have hs (i : Fin k) : Ioo (ζ i.castSucc) (ζ i.succ) ⊆ Ioo (0:ℝ) 1 := by
    intro u hu
    have h0 : 0≤ζ i.castSucc := by rw [← hz0]; exact hz.monotone (Fin.zero_le _)
    have h1 : ζ i.succ≤1 := by rw [← hz1]; exact hz.monotone (Fin.le_last _)
    exact ⟨h0.trans_lt hu.1,hu.2.trans_le h1⟩
  have hind (i : Fin k) : (fun u => if ζ i.castSucc<u ∧ u<ζ i.succ then v i else 0) =
      (Ioo (ζ i.castSucc) (ζ i.succ)).indicator (fun _ : ℝ => v i) := by
    ext u
    simp only [Set.indicator_apply,Set.mem_Ioo]
  have hi (i : Fin k) : Integrable (fun u => if ζ i.castSucc<u ∧ u<ζ i.succ then v i else 0) pathMeasure := by
    rw [hind]
    exact (integrable_const (v i)).indicator measurableSet_Ioo
  unfold finiteStepFunction
  rw [integral_finsetSum _ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [hind]
  rw [integral_indicator measurableSet_Ioo]
  have he : pathMeasure.restrict (Ioo (ζ i.castSucc) (ζ i.succ)) = volume.restrict (Ioo (ζ i.castSucc) (ζ i.succ)) := by
    rw [pathMeasure,Measure.restrict_restrict measurableSet_Ioo,inter_eq_left.mpr (hs i)]
  rw [he,integral_const]
  simp only [measureReal_def,Measure.restrict_apply_univ,Real.volume_Ioo,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (hz.monotone (Fin.castSucc_le_succ i))),smul_eq_mul]

lemma integral_finiteStepFunction_mul {k : ℕ} (ζ : Fin (k+1) → ℝ)
    (hz : StrictMono ζ) (hz0 : ζ 0=0) (hz1 : ζ (Fin.last k)=1) (v w : Fin k → ℝ) :
    (∫ u, finiteStepFunction ζ v u*finiteStepFunction ζ w u ∂pathMeasure) =
      ∑ i, (ζ i.succ-ζ i.castSucc)*v i*w i := by
  rw [finiteStepFunction_mul hz,integral_finiteStepFunction ζ hz hz0 hz1]
  apply Finset.sum_congr rfl
  intro i _
  ring

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma finiteStep_tail_indicator {k : ℕ} (ζ : Fin (k+1) → ℝ) (hz : StrictMono ζ)
    (v : Fin k → ℝ) (d : Fin (k+1)) :
    (Ioi (ζ d)).indicator (finiteStepFunction ζ v) =
      finiteStepFunction ζ (fun i => if d ≤ i.castSucc then v i else 0) := by
  classical
  ext u
  rw [Set.indicator_apply]
  simp only [Set.mem_Ioi,finiteStepFunction]
  by_cases hd : ζ d < u
  · rw [ite_eq_left hd]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : ζ i.castSucc < u ∧ u < ζ i.succ
    · simp only [ite_eq_left hi]
      have hj : d ≤ i.castSucc := by
        by_contra h
        have hs : i.succ ≤ d := by
          change i.val+1 ≤ d.val
          simp only [Fin.le_def,Fin.val_castSucc] at h
          omega
        have H := hz.monotone hs
        linarith
      rw [ite_eq_left hj]
    · simp only [ite_eq_right hi]
  · rw [ite_eq_right hd]
    symm
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : ζ i.castSucc < u ∧ u < ζ i.succ
    · rw [ite_eq_left hi]
      have hj : ¬d ≤ i.castSucc := fun h => hd ((hz.monotone h).trans_lt hi.1)
      rw [ite_eq_right hj]
    · rw [ite_eq_right hi]

lemma integral_finiteStep_tail {k : ℕ} (ζ : Fin (k+1) → ℝ) (hz : StrictMono ζ)
    (hz0 : ζ 0=0) (hz1 : ζ (Fin.last k)=1) (v : Fin k → ℝ) (d : Fin (k+1)) :
    (∫ u in Ioi (ζ d), finiteStepFunction ζ v u ∂pathMeasure) =
      ∑ i : Fin k, if d ≤ i.castSucc then (ζ i.succ-ζ i.castSucc)*v i else 0 := by
  rw [← integral_indicator measurableSet_Ioi,finiteStep_tail_indicator ζ hz,
    integral_finiteStepFunction ζ hz hz0 hz1]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma abs_linearGrowth : HasLinearGrowth (fun x : ℝ => |x|) := by
  refine ⟨0,1,le_rfl,zero_le_one,fun x => ?_⟩
  simp only [abs_abs,zero_add,one_mul,Real.norm_eq_abs,le_refl]

lemma gaussian_abs_exp_bound (a x : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    (∫ z, Real.exp (d*|x+a*z|) ∂gaussianReal 0 1) ≤
      2*Real.exp (d*|x|+(d*a)^2/2) := by
  have hi : Integrable (fun z : ℝ => Real.exp (d*|x+a*z|)) (gaussianReal 0 1) :=
    integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments _ _)
      (by fun_prop) ((abs_linearGrowth.add_left x).scale_argument a) d
  have hj : Integrable (fun z : ℝ => Real.exp (d*|x|)*
      (Real.exp ((d*a)*z)+Real.exp ((-d*a)*z))) (gaussianReal 0 1) :=
    ((integrable_exp_mul_gaussianReal (d*a)).add (integrable_exp_mul_gaussianReal (-d*a))).const_mul _
  have hp (z : ℝ) : Real.exp (d*|x+a*z|) ≤ Real.exp (d*|x|)*
      (Real.exp ((d*a)*z)+Real.exp ((-d*a)*z)) := by
    calc
      _ ≤ Real.exp (d*(|x|+|a*z|)) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_add_le _ _) hd)
      _ = Real.exp (d*|x|)*Real.exp (d*|a*z|) := by rw [mul_add,Real.exp_add]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        by_cases h : 0 ≤ a*z
        · rw [abs_of_nonneg h]
          have he : d*(a*z) = (d*a)*z := by ring
          rw [he]
          exact le_add_of_nonneg_right (Real.exp_pos _).le
        · rw [abs_of_neg (lt_of_not_ge h)]
          have he : d*-(a*z) = (-d*a)*z := by ring
          rw [he]
          exact le_add_of_nonneg_left (Real.exp_pos _).le
  calc
    _ ≤ ∫ z, Real.exp (d*|x|)*(Real.exp ((d*a)*z)+Real.exp ((-d*a)*z)) ∂gaussianReal 0 1 :=
      integral_mono hi hj hp
    _ = _ := by
      rw [integral_const_mul,integral_add (integrable_exp_mul_gaussianReal _) (integrable_exp_mul_gaussianReal _)]
      have hmgf (t : ℝ) : (∫ z : ℝ, Real.exp (t*z) ∂gaussianReal 0 1) = Real.exp (t^2/2) := by
        simpa [mgf] using mgf_gaussianReal (p := gaussianReal 0 1) (μ := 0) (v := 1) (X := fun z : ℝ => z) (by simp) t
      rw [hmgf,hmgf]
      have hs : (-d*a)^2 = (d*a)^2 := by ring
      rw [hs,Real.exp_add]
      ring

lemma gaussianTransform_abs_bound {s d : ℝ} (hs : 0 ≤ s) (hd : 0 < d) (x : ℝ) :
    gaussianTransform s d (fun y => |y|) x ≤ |x|+d*s/2+Real.log 2/d := by
  have hi : Integrable (fun z : ℝ => Real.exp (d*|x+Real.sqrt s*z|)) (gaussianReal 0 1) :=
    integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments _ _)
      (by fun_prop) ((abs_linearGrowth.add_left x).scale_argument (Real.sqrt s)) d
  change (if d=0 then _ else _/d) ≤ _
  rw [ite_eq_right hd.ne']
  apply (div_le_iff₀ hd).2
  have H := Real.log_le_log (integral_exp_pos (gaussianReal 0 1) _ hi)
    (gaussian_abs_exp_bound (Real.sqrt s) x hd.le)
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp] at H
  have hsq := Real.sq_sqrt hs
  apply H.trans_eq
  rw [mul_pow,hsq]
  field_simp
  ring

lemma gaussianTransform_upper_abs {U : ℝ → ℝ} (hm : Measurable U) (hG : HasLinearGrowth U)
    {C s d : ℝ} (hU : ∀ x, U x ≤ |x|+C) (hs : 0 ≤ s) (hd : 0 < d) (x : ℝ) :
    gaussianTransform s d U x ≤ |x|+C+d*s/2+Real.log 2/d := by
  have hg : HasLinearGrowth (fun x : ℝ => C+|x|) := by
    refine ⟨|C|,1,abs_nonneg _,zero_le_one,fun x => ?_⟩
    simpa only [one_mul,Real.norm_eq_abs,abs_abs] using abs_add_le C |x|
  have he : gaussianTransform s d U x ≤ gaussianTransform s d (fun x => C+|x|) x := by
    simp only [gaussianTransform,hd.ne',ite_false]
    apply logMean_mono (gaussianReal 0 1) hd
    · exact integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments _ _)
        (hm.comp (measurable_const.add (measurable_id.const_mul _)))
        ((hG.add_left x).scale_argument (Real.sqrt s)) d
    · exact integrable_exp_of_linearGrowth _ (gaussianReal_exponentialNormMoments _ _)
        (by fun_prop) ((hg.add_left x).scale_argument (Real.sqrt s)) d
    · intro z; simpa only [add_comm C] using hU (x+Real.sqrt s*z)
  rw [gaussianTransform_const_add (by fun_prop) abs_linearGrowth] at he
  have H := gaussianTransform_abs_bound hs hd x
  linarith

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma magneticRecursion_upper (n : ℕ) (a b : ℕ → ℝ) (hb : ∀ i<n, 0<b i) (x : ℝ) :
    magneticRecursion n a b x ≤ |x|+∑ i : Fin n, (b i*(a i)^2/2+Real.log 2/b i) := by
  induction n generalizing a b x with
  | zero =>
    simpa [magneticRecursion] using (le_abs_self (Real.log (Real.cosh x))).trans (abs_log_cosh_le x)
  | succ n ih =>
    have hb' : ∀ i<n, 0 < b (i+1) := fun i hi => hb (i+1) (by omega)
    have hG := magneticRecursion_growth n (fun i => a (i+1)) (fun i => b (i+1)) hb'
    have H := gaussianTransform_upper_abs hG.1 hG.2
      (ih (fun i => a (i+1)) (fun i => b (i+1)) hb') (sq_nonneg (a 0)) (hb 0 (by omega)) x
    rw [Fin.sum_univ_succ]
    simpa only [magneticRecursion,Fin.val_zero,Fin.val_succ,add_assoc,add_left_comm,add_comm] using H

lemma magneticFieldValue_growth (n : ℕ) (b : ℕ → ℝ) (hb : ∀ i<n, 0<b i)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0 ≤ h 0) :
    magneticFieldValue n b h ≤
      (∫ z : ℝ, |z| ∂gaussianReal 0 1)*Real.sqrt (h 0) +
      (∑ i : Fin n, Real.log 2/b i) +
      (∑ i : Fin n, b i*(h (i+1)-h i))/2-h n/2 := by
  have hG := magneticRecursion_growth n (fun i => pathAmplitude h (i+1)) b hb
  have hi : Integrable (fun z : ℝ => magneticRecursion n (fun i => pathAmplitude h (i+1)) b (pathAmplitude h 0*z))
      (gaussianReal 0 1) := gaussian_linearGrowth_integrable (hG.1.comp (measurable_id.const_mul _))
    (hG.2.scale_argument _) _ _
  have hj : Integrable (fun z : ℝ => |pathAmplitude h 0*z|+
      ∑ i : Fin n, (b i*(pathAmplitude h (i+1))^2/2+Real.log 2/b i)) (gaussianReal 0 1) :=
    (((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl).const_mul _).abs.add (integrable_const _)
  have H := integral_mono hi hj (fun z => magneticRecursion_upper n (fun i => pathAmplitude h (i+1)) b hb (pathAmplitude h 0*z))
  have ha : Integrable (fun z : ℝ => |pathAmplitude h 0*z|) (gaussianReal 0 1) :=
    (((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable le_rfl).const_mul (pathAmplitude h 0)).abs
  rw [integral_add ha (integrable_const _)] at H
  simp only [abs_mul,integral_const_mul,
    integral_const,probReal_univ,one_smul,Finset.sum_add_distrib,
    pathAmplitude_sq hh h0,pathIncrement] at H
  unfold magneticFieldValue
  dsimp only [pathAmplitude,pathIncrement] at H ⊢
  rw [abs_of_nonneg (Real.sqrt_nonneg _), ← Finset.sum_div] at H
  linarith

end IsingPerceptron

 

 

open scoped BigOperators
namespace IsingPerceptron

lemma finite_field_telescoping (z h : ℕ → ℝ) (n : ℕ) :
    (∑ i : Fin (n+1), (z (i+1)-z i)*h i) +
      (∑ i : Fin n, z (i+1)*(h (i+1)-h i)) = z (n+1)*h n-z 0*h 0 := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Fin.sum_univ_castSucc (fun i : Fin (n+2) => (z (i+1)-z i)*h i),
      Fin.sum_univ_castSucc (fun i : Fin (n+1) => z (i+1)*(h (i+1)-h i))]
    simp only [Fin.val_castSucc,Fin.val_last] at *
    linarith

lemma field_sum_last_lower (n : ℕ) (w h q : Fin (n+1) → ℝ)
    (hw : ∀ i, 0≤w i) (hh : ∀ i, 0≤h i) (hq : ∀ i, q i≤1) :
    w (Fin.last n)*(1-q (Fin.last n))*h (Fin.last n) ≤
      ∑ i, w i*(1-q i)*h i :=
  Finset.single_le_sum (fun i _ => mul_nonneg (mul_nonneg (hw i) (sub_nonneg.mpr (hq i))) (hh i))
    (Finset.mem_univ _)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def chainWeight {n : ℕ} (ζ : Fin (n+2) → ℝ) (i : Fin (n+1)) : ℝ := ζ i.succ-ζ i.castSucc

lemma chainWeight_pos {n : ℕ} {ζ : Fin (n+2) → ℝ} (hz : StrictMono ζ) (i : Fin (n+1)) :
    0<chainWeight ζ i := sub_pos.mpr (hz (Fin.castSucc_lt_succ))

lemma chain_field_telescoping {n : ℕ} (ζ : Fin (n+2) → ℝ)
    (hz0 : ζ 0=0) (hz1 : ζ (Fin.last (n+1))=1) (h : ℕ → ℝ) :
    (∑ i : Fin (n+1), chainWeight ζ i*h i) +
      (∑ i : Fin n, chainExponent ζ i*(h (i+1)-h i)) = h n := by
  let z : ℕ → ℝ := fun i => ζ ⟨min i (n+1),by omega⟩
  have he (i : ℕ) (hi : i≤n+1) : z i=ζ ⟨i,by omega⟩ := by simp [z,min_eq_left hi]
  have H := finite_field_telescoping z h n
  have hS : (∑ i : Fin (n+1), (z (i+1)-z i)*h i) =
      ∑ i : Fin (n+1), chainWeight ζ i*h i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [he _ (by omega),he _ (by omega)]
    rfl
  rw [hS] at H
  change (∑ i : Fin (n+1), chainWeight ζ i*h i) +
    (∑ i : Fin n, chainExponent ζ i*(h (i+1)-h i)) = z (n+1)*h n-z 0*h 0 at H
  have hzN : z (n+1)=1 := by simpa [z,Fin.last] using hz1
  have hzZ : z 0=0 := by simpa [z] using hz0
  simpa only [hzN,hzZ,one_mul,zero_mul,sub_zero] using H

lemma magneticFieldValue_chain_growth {n : ℕ} (ζ : Fin (n+2) → ℝ) (hz : StrictMono ζ)
    (hz0 : ζ 0=0) (hz1 : ζ (Fin.last (n+1))=1)
    (h : ℕ → ℝ) (hh : Monotone h) (h0 : 0≤h 0) :
    magneticFieldValue n (chainExponent ζ) h ≤
      (∫ z : ℝ, |z| ∂gaussianReal 0 1)*Real.sqrt (h 0) +
      (∑ i : Fin n, Real.log 2/chainExponent ζ i)-
      (∑ i : Fin (n+1), chainWeight ζ i*h i)/2 := by
  have G := magneticFieldValue_growth n (chainExponent ζ)
    (fun i hi => ((chainExponent_admissible hz hz0 hz1).1 i hi).1) h hh h0
  have T := chain_field_telescoping ζ hz0 hz1 h
  linarith

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma contact_cone_depthTail {N n : ℕ} (hN : 0 < N)
    (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (ν : Measure (Spin N)) [IsProbabilityMeasure ν] {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] {φ : A → Spin N → ℝ} (hm : Measurable φ)
    {K : ℝ} (hK : 0 ≤ K) (hφ : ∀ y x, |φ y x| ≤ K)
    (c : Fin (n+1) → ℝ) (S v : ℝ) {rmax : ℝ≥0} {H : ℝ} {p : ContactParameter n N}
    (hp : p∈contactRegion n N rmax H)
    (hmin : IsMinOn (enrichedContactObjective P n b ν φ c S v) (contactRegion n N rmax H) p)
    (hcap : (∑ i, p.2.1 i) < H) (j : Fin (n+1)) :
    (∑ i, if j ≤ i then c i else 0) ≤
      ∫ x, spinArray x 0 1*depthTail n j (treeArray x 0 1)
        ∂(enrichedArrayLaw P p.1 n b (finiteFieldPath p.2.1) p.2.2 ν hm : Measure JointArray) := by
  classical
  have hp' := contactRegion_nonneg hp
  have hu : ∀ j, |p.2.2 j| ≤ 2 := fun j => abs_le.mpr ⟨by linarith [(hp'.2.2.2.2 j).1],(hp'.2.2.2.2 j).2⟩
  rw [enrichedArrayLaw_depthTail hN n b (monotone_finiteFieldPath hp'.2.2.1)
    (finiteFieldPath_nonneg hp'.2.2.1 0) p.2.2 hu ν P hm hK hφ]
  have Hc := enriched_contact_cone hN n b hb ν P hm hK hφ c S v hp hmin hcap
    (Pi.single j 1) (fun i => by by_cases hij : i=j <;> simp [hij])
  simpa only [finiteFieldPath_single,Fin.le_def,mul_ite,mul_one,mul_zero] using Hc

theorem enriched_contact_nodal_tails
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (hNlim : Tendsto N atTop atTop)
    (n : ℕ) (ζ : Fin (n+2) → ℝ) (hz : StrictMono ζ) (hz0 : ζ 0=0) (hz1 : ζ (Fin.last (n+1))=1)
    (q : Fin (n+1) → ℝ) (S v H : ℝ) (α : ℝ≥0)
    (p : (k : ℕ) → ContactParameter n (N k))
    (hp : ∀ k, p k∈contactRegion n (N k) (α*(N k:ℝ≥0)) H)
    (hcap : ∀ k, (∑ i, (p k).2.1 i) < H)
    (ν : (k : ℕ) → Measure (Spin (N k))) [∀ k, IsProbabilityMeasure (ν k)]
    (A : ℕ → Type*) [∀ k, MeasurableSpace (A k)]
    (P : (k : ℕ) → Measure (A k)) [∀ k, IsProbabilityMeasure (P k)]
    (φ : (k : ℕ) → A k → Spin (N k) → ℝ) (hm : ∀ k, Measurable (φ k))
    (K : ℝ) (hK : 0 ≤ K) (hφ : ∀ k y x, |φ k y x| ≤ K)
    (hmin : ∀ k, IsMinOn (enrichedContactObjective (P k) n (chainExponent ζ) (ν k) (φ k)
      (fun i => chainWeight ζ i*q i) S v) (contactRegion n (N k) (α*(N k:ℝ≥0)) H) (p k))
    (μ : ProbabilityMeasure JointArray)
    (hL : Tendsto (fun k => enrichedArrayLaw (P k) (p k).1 n (chainExponent ζ)
      (finiteFieldPath (p k).2.1) (p k).2.2 (ν k) (hm k)) atTop (𝓝 μ)) :
    ∀ j : Fin (n+1), (∑ i, if j ≤ i then chainWeight ζ i*q i else 0) ≤
      ∫ u in Ioi (ζ j.castSucc), quantileFunction ((μ : Measure JointArray).map (fun x => spinArray x 0 1)) u ∂pathMeasure := by
  let h := fun k => finiteFieldPath (p k).2.1
  have hp' k := contactRegion_nonneg (hp k)
  have hh k := monotone_finiteFieldPath (hp' k).2.2.1
  have h0 k := finiteFieldPath_nonneg (hp' k).2.2.1 0
  have hu k := (hp' k).2.2.2.2
  have hub k j : |(p k).2.2 j| ≤ 2 := abs_le.mpr ⟨by linarith [(hu k j).1],(hu k j).2⟩
  have hH k : h k n ≤ H := by dsimp only [h]; rw [finiteFieldPath_last]; exact (hp' k).2.2.2.1
  have hr k : ((p k).1:ℝ) ≤ (α:ℝ)*N k := by exact_mod_cast (hp' k).2.1
  have hb := chainExponent_admissible hz hz0 hz1
  have hpert k := enriched_contact_perturbation_minimum (P k) (chainExponent ζ) (ν k) (φ k)
    (fun i => chainWeight ζ i*q i) S v (hp k) (hmin k)
  have hord := enriched_minimizers_ordered N hN hNlim n (chainExponent ζ) hb h hh h0 H hH
    (fun k => (p k).2.2) hu ν A P φ hm K hK hφ (fun k => (p k).1) α hr hpert μ hL
  have ht := enrichedArrayLaw_limit_tree N hN n (chainExponent ζ) hb h hh h0
    (fun k => (p k).2.2) hub ν A P φ hm K hK hφ (fun k => (p k).1) μ hL
  intro j
  rw [← joint_depthTail_quantile ζ hz0 hord.1 hord.2 ht.1 ht.2 j]
  have hc : Continuous (fun x : JointArray => spinArray x 0 1*depthTail n j (treeArray x 0 1)) :=
    (by unfold spinArray; fun_prop : Continuous (fun x : JointArray => spinArray x 0 1)).mul
      ((continuous_depthTail n j).comp (by unfold treeArray; fun_prop))
  apply ge_of_tendsto (jointArray_tendsto_integral hL hc)
  exact Eventually.of_forall (fun k => contact_cone_depthTail (hN k) (chainExponent ζ) hb (ν k)
    (P k) (hm k) hK (hφ k) (fun i => chainWeight ζ i*q i) S v (hp k) (hmin k) (hcap k) j)

end IsingPerceptron

end

end OAI
