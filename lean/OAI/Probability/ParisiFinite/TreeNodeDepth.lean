import Mathlib
import OAI.Probability.ParisiFinite.SumFinLtNat

namespace OAI

/-! Tree Node Depth. -/

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
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation

def treeNodeDepth : {d r : ℕ} → (T : PartitionTree d r) → TreeNode T → Fin d
  | 0,_,_ => Empty.elim
  | _+1,_,⟨_,T⟩ => fun ⟨j,x⟩ => Sum.casesOn x (fun _ => 0) (fun n => (treeNodeDepth (T j) n).succ)

lemma treeNodeDepth_path {d r : ℕ} (T : PartitionTree d r) (i : Fin r) (k : Fin d) :
    treeNodeDepth T (treeNodePath T i k)=k := by
  induction d generalizing r with
  | zero => exact Fin.elim0 k
  | succ d ih =>
    rcases T with ⟨P,T⟩
    obtain ⟨⟨j,i⟩,rfl⟩ := P.equivSigma.surjective i
    change treeNodeDepth _ (treeNodePath _ (P.emb j i) k)=k
    rw [treeNodePath_emb]
    induction k using Fin.cases with
    | zero => rfl
    | succ k => exact congrArg Fin.succ (ih (T j) i k)

lemma treeNodePath_injective {d r : ℕ} (T : PartitionTree d r) (i : Fin r) :
    Function.Injective (treeNodePath T i) := by
  intro k l h
  simpa only [treeNodeDepth_path] using congrArg (treeNodeDepth T) h

lemma treeNodePath_eq_levels {d r : ℕ} (T : PartitionTree d r) (i j : Fin r) (k l : Fin d)
    (h : treeNodePath T i k=treeNodePath T j l) : k=l := by
  simpa only [treeNodeDepth_path] using congrArg (treeNodeDepth T) h

def treeGaussianCoeff {d r : ℕ} (T : PartitionTree d r) (v : Fin d → ℝ)
    (i : Fin r) (n : TreeNode T) : ℝ :=
  ∑ k,if treeNodePath T i k=n then Real.sqrt (v k) else 0

lemma field_treeGaussianCoeff {d r : ℕ} (T : PartitionTree d r) (v : Fin d → ℝ)
    (z : TreeNode T → ℝ) (i : Fin r) :
    field (treeGaussianCoeff T v) z i=∑ k,Real.sqrt (v k)*z (treeNodePath T i k) := by
  simp only [field,treeGaussianCoeff,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_eq_single (treeNodePath T i k)]
  · simp
  · intro n hn hne
    simp [Ne.symm hne]
  · simp

lemma treeGaussianCoeff_at_path {d r : ℕ} (T : PartitionTree d r) (v : Fin d → ℝ)
    (i j : Fin r) (k : Fin d) :
    treeGaussianCoeff T v j (treeNodePath T i k)=
      if treeNodePath T j k=treeNodePath T i k then Real.sqrt (v k) else 0 := by
  unfold treeGaussianCoeff
  rw [Finset.sum_eq_single k]
  · intro l hl hne
    have he : treeNodePath T j l≠treeNodePath T i k := fun h => hne (treeNodePath_eq_levels T j i l k h)
    simp [he]
  · simp

lemma kernel_treeGaussianCoeff {d r : ℕ} (T : PartitionTree d r) (v : Fin d → ℝ)
    (hv : ∀ k,0≤v k) (i j : Fin r) :
    kernel (treeGaussianCoeff T v) i j=
      ∑ k,if treeCodes T k.succ i=treeCodes T k.succ j then v k else 0 := by
  change field (treeGaussianCoeff T v) (treeGaussianCoeff T v j) i=_
  rw [field_treeGaussianCoeff]
  simp only [treeGaussianCoeff_at_path,treeNodePath_eq_iff]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : treeCodes T k.succ i=treeCodes T k.succ j
  · simp [h,← pow_two,Real.sq_sqrt (hv k)]
  · simp [h,Ne.symm h]

lemma tree_code_gaussian_law {d r : ℕ} (T : PartitionTree d r) (v : Fin d → ℝ)
    (hv : ∀ k,0≤v k) :
    (gaussianLaw (TreeNode T)).map (field (treeGaussianCoeff T v))=
      (gaussianLaw (Σ k : Fin (d+1),CodeLabel (treeCodes T k))).map
        (field (codeGaussianCoeff (treeCodes T) (Fin.cons 0 v))) := by
  apply field_law_eq_of_kernel
  funext i j
  rw [kernel_treeGaussianCoeff T v hv]
  have hv' : ∀ k : Fin (d+1),0≤(Fin.cons (0:ℝ) v : Fin (d+1) → ℝ) k := by intro k; cases k using Fin.cases <;> simp [hv]
  rw [kernel_codeGaussianCoeff _ _ hv',Fin.sum_univ_succ]
  simp

def treeGaussianMoment {d r : ℕ} (T : PartitionTree d r) (x : (Fin d → ℝ) → ℝ) : ℝ :=
  ∫ z,∏ i,x (fun k => z (treeNodePath T i k)) ∂gaussianLaw (TreeNode T)

lemma treeGaussianMoment_mem_unit {d r : ℕ} (T : PartitionTree d r)
    {x : (Fin d → ℝ) → ℝ} (hx : Continuous x) (hb : ∀ s,0≤x s ∧ x s≤1) :
    0≤treeGaussianMoment T x ∧ treeGaussianMoment T x≤1 := by
  have hm : Continuous (fun z : TreeNode T → ℝ => ∏ i,x (fun k => z (treeNodePath T i k))) := by
    apply continuous_finsetProd
    intro i _
    exact hx.comp (continuous_pi fun k => continuous_apply _)
  have hb' (z : TreeNode T → ℝ) : 0≤(∏ i,x (fun k => z (treeNodePath T i k))) ∧
      (∏ i,x (fun k => z (treeNodePath T i k)))≤1 :=
    ⟨Finset.prod_nonneg (fun i _ => (hb _).1),Finset.prod_le_one₀ (fun i _ => (hb _).1) (fun i _ => (hb _).2)⟩
  have hi : Integrable (fun z : TreeNode T → ℝ => ∏ i,x (fun k => z (treeNodePath T i k)))
      (gaussianLaw (TreeNode T)) :=
    (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable (ae_of_all _ fun z => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (hb' z).1] using (hb' z).2)
  refine ⟨integral_nonneg (fun z => (hb' z).1),?_⟩
  simpa [treeGaussianMoment] using
    integral_mono hi (integrable_const (1:ℝ)) (fun z => (hb' z).2)

 

lemma treeMarkMoment_tendsto_gaussian {d r : ℕ} (T : PartitionTree d r)
    {x : (Fin d → ℝ) → ℝ} (hx : Continuous x) (hb : ∀ s,0≤x s ∧ x s≤1) :
    Tendsto (fun m => treeMarkMoment (gaussianQuantizerWeight m)
      (fun s : Fin d → GaussianQuantizerLabel m => x (fun k => (s k).val)) T) atTop
      (𝓝 (treeGaussianMoment T x)) := by
  simp_rw [treeMarkMoment_node_sum]
  apply gaussianQuantizer_bounded_continuous
  · apply continuous_finsetProd
    intro i _
    exact hx.comp (continuous_pi fun k => continuous_apply _)
  · intro z
    rw [abs_of_nonneg (Finset.prod_nonneg (fun i _ => (hb _).1))]
    exact Finset.prod_le_one₀ (fun i _ => (hb _).1) (fun i _ => (hb _).2)

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace ParisiFinite

lemma integrable_of_uniform_abs {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} {C : ℝ}
    (hf : Measurable f) (hb : ∀ x,|f x|≤C) : Integrable f μ := by
  exact (integrable_const C).mono' hf.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb x)

lemma integrable_exp_of_uniform_abs {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} {C : ℝ} (a : ℝ)
    (hf : Measurable f) (hb : ∀ x,|f x|≤C) :
    Integrable (fun x => Real.exp (a*f x)) μ := by
  apply integrable_of_uniform_abs (C:=Real.exp (|a| * C)) (by fun_prop)
  intro x
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact le_trans (le_abs_self _) (by simpa only [abs_mul] using mul_le_mul_of_nonneg_left (hb x) (abs_nonneg a))

lemma logMean_uniform_abs {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω → ℝ} {C a : ℝ}
    (ha : 0≤a) (hf : Measurable f) (hb : ∀ x,|f x|≤C) : |logMean μ a f|≤C := by
  have hi := integrable_of_uniform_abs (μ:=μ) hf hb
  have he := integrable_exp_of_uniform_abs (μ:=μ) a hf hb
  rw [abs_le]
  constructor
  · have h := logMean_mono ha (integrable_const (-C)) hi
      (integrable_const (Real.exp (a*(-C)))) he (fun x => (abs_le.mp (hb x)).1)
    simpa only [logMean_const] using h
  · have h := logMean_mono ha hi (integrable_const C) he
      (integrable_const (Real.exp (a*C))) (fun x => (abs_le.mp (hb x)).2)
    simpa only [logMean_const] using h

 

lemma tendsto_logMean_of_uniform_abs {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (a : ℝ) {f : ℕ → Ω → ℝ} {g : Ω → ℝ} {C : ℝ}
    (hf : ∀ m,Measurable (f m)) (hg : Measurable g)
    (hb : ∀ m x,|f m x|≤C) (hbg : ∀ x,|g x|≤C)
    (ht : ∀ x,Tendsto (fun m => f m x) atTop (𝓝 (g x))) :
    Tendsto (fun m => logMean μ a (f m)) atTop (𝓝 (logMean μ a g)) := by
  by_cases ha : a=0
  · simp only [ha,logMean_zero]
    exact tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun m => (hf m).aestronglyMeasurable) (integrable_const C)
      (fun m => ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb m x) (ae_of_all _ ht)
  · simp only [logMean,ha,↓reduceIte]
    have hi : Tendsto (fun m => ∫ x,Real.exp (a*f m x) ∂μ) atTop
        (𝓝 (∫ x,Real.exp (a*g x) ∂μ)) := by
      apply tendsto_integral_of_dominated_convergence (fun _ => Real.exp (|a| * C))
      · intro m; exact (by fun_prop : Measurable (fun x => Real.exp (a*f m x))).aestronglyMeasurable
      · exact integrable_const _
      · intro m
        filter_upwards with x
        rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        exact (le_abs_self _).trans (by simpa only [abs_mul] using mul_le_mul_of_nonneg_left (hb m x) (abs_nonneg a))
      · filter_upwards with x
        exact Real.continuous_exp.continuousAt.tendsto.comp ((ht x).const_mul a)
    exact (hi.log (ne_of_gt (integral_exp_pos (integrable_exp_of_uniform_abs a hg hbg)))).div_const a

end ParisiFinite
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite

lemma gaussianQuantizer_logMean (m : ℕ) (a : ℝ) (f : GaussianQuantizerLabel m → ℝ) :
    logMean (gaussianQuantizerLaw m) a f=
      logMean (gaussianReal 0 1) a (fun z => f (gaussianQuantizerIndex m z)) := by
  unfold logMean gaussianQuantizerLaw
  rw [integral_map (gaussianQuantizerIndex_measurable m).aemeasurable
    (Integrable.of_finite (μ:=(gaussianReal 0 1).map (gaussianQuantizerIndex m))).aestronglyMeasurable]
  rw [integral_map (gaussianQuantizerIndex_measurable m).aemeasurable
    (Integrable.of_finite (μ:=(gaussianReal 0 1).map (gaussianQuantizerIndex m))).aestronglyMeasurable]

lemma gaussianQuantizer_logMean_tendsto (a : ℝ) {f : ℝ → ℝ} {C : ℝ}
    (hf : Continuous f) (hb : ∀ x,|f x|≤C) :
    Tendsto (fun m => logMean (gaussianQuantizerLaw m) a (fun z => f z.val)) atTop
      (𝓝 (logMean (gaussianReal 0 1) a f)) := by
  simp_rw [gaussianQuantizer_logMean]
  apply tendsto_logMean_of_uniform_abs a
  · intro m; exact hf.measurable.comp (gaussianQuantizer m).measurable
  · exact hf.measurable
  · intro m x; exact hb _
  · exact hb
  · intro x
    exact hf.continuousAt.tendsto.comp (gaussianQuantizer_tendsto x)

end SKCavity

 

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite
variable {ι : Type*} [Fintype ι]

def finiteRisk (w : ι → ℝ) (a : ℝ) (f : ι → ℝ) : ℝ :=
  if a=0 then ∑ i,w i*f i else Real.log (∑ i,w i*Real.exp (a*f i))/a

def finiteHierarchyRisk (w : ι → ℝ) : {d : ℕ} → (Fin d → ℝ) → ((Fin d → ι) → ℝ) → ℝ
  | 0,_,f => f (fun k => Fin.elim0 k)
  | _+1,a,f => finiteRisk w (a 0) (fun i => finiteHierarchyRisk w (fun k => a k.succ) (fun s => f (Fin.cons i s)))

lemma finiteRisk_const (w : ι → ℝ) (hw : ∑ i,w i=1) (a c : ℝ) : finiteRisk w a (fun _ => c)=c := by
  unfold finiteRisk
  simp only [← Finset.sum_mul,hw,one_mul,Real.log_exp]
  split_ifs with h
  · rfl
  · exact mul_div_cancel_left₀ c h

lemma finiteRisk_exp {w : ι → ℝ} (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1)
    {a : ℝ} (ha : a≠0) (f : ι → ℝ) :
    Real.exp (a*finiteRisk w a f)=∑ i,w i*Real.exp (a*f i) := by
  have hp := weighted_sum_pos hw hs (fun i => Real.exp_pos (a*f i))
  simp only [finiteRisk,ha,↓reduceIte]
  rw [mul_div_cancel₀ _ ha,Real.exp_log hp]

lemma hierarchyMark_eq_finiteRisk {d : ℕ} {w : ι → ℝ}
    (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1) (a : Fin (d+1) → ℝ)
    (ha : ∀ k : Fin d,a k.succ≠0) {x : (Fin d → ι) → ℝ}
    {z : ℝ} (hp : ∀ s,0<1-z*x s) :
    hierarchyMark w d a x z=Real.exp (a 0*finiteHierarchyRisk w (fun k => a k.succ)
      (fun s => Real.log (1-z*x s))) := by
  induction d with
  | zero =>
    simp only [hierarchyMark,finiteHierarchyRisk,Real.rpow_def_of_pos (hp _)]
    congr 1
    ring
  | succ d ih =>
    change (∑ i,w i*hierarchyMark w d (fun k => a k.succ) (fun s => x (Fin.cons i s)) z)^(a 0/a 1)=_
    simp_rw [ih (fun k => a k.succ) (fun k => ha k.succ) (fun s => hp _)]
    let F : ι → ℝ := fun i => finiteHierarchyRisk w (fun k : Fin d => a k.succ.succ)
      (fun s => Real.log (1-z*x (Fin.cons i s)))
    change (∑ i,w i*Real.exp (a 1*F i))^(a 0/a 1)=Real.exp (a 0*finiteRisk w (a 1) F)
    have h1 : a 1≠0 := ha 0
    have hp' := weighted_sum_pos hw hs (fun i => Real.exp_pos (a 1*F i))
    rw [Real.rpow_def_of_pos hp']
    simp only [finiteRisk,h1,↓reduceIte]
    congr 1
    ring

 

lemma hierarchyLog_eq_finiteHierarchyRisk {d : ℕ} {w : ι → ℝ}
    (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1) (a : Fin (d+1) → ℝ)
    (ha : ∀ k,a k≠0) {x : (Fin (d+1) → ι) → ℝ}
    {z : ℝ} (hp : ∀ s,0<1-z*x s) :
    hierarchyLog w a x z=finiteHierarchyRisk w a (fun s => Real.log (1-z*x s)) := by
  unfold hierarchyLog
  simp_rw [hierarchyMark_eq_finiteRisk hw hs a (fun k => ha k.succ) (fun s => hp _)]
  change (a 0)⁻¹*Real.log (∑ i,w i*Real.exp (a 0*finiteHierarchyRisk w (fun k => a k.succ)
    (fun s => Real.log (1-z*x (Fin.cons i s)))))=_
  simp only [finiteHierarchyRisk,finiteRisk,ha 0,↓reduceIte,div_eq_mul_inv,mul_comm]

lemma finiteRisk_eq_logMean (m : ℕ) (a : ℝ) (f : GaussianQuantizerLabel m → ℝ) :
    finiteRisk (gaussianQuantizerWeight m) a f=logMean (gaussianQuantizerLaw m) a f := by
  unfold finiteRisk logMean
  rw [integral_fintype Integrable.of_finite,integral_fintype Integrable.of_finite]
  rfl

lemma finiteRisk_uniform_abs {w : ι → ℝ} (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1)
    {a C : ℝ} (ha : 0≤a) {f : ι → ℝ} (hb : ∀ i,|f i|≤C) : |finiteRisk w a f|≤C := by
  have havg (g : ι → ℝ) {D : ℝ} (hg : ∀ i,g i≤D) : (∑ i,w i*g i)≤D := by
    calc
      _ ≤ ∑ i,w i*D := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hg i) (hw i)
      _ = D := by rw [← Finset.sum_mul,hs,one_mul]
  have hlow (g : ι → ℝ) {D : ℝ} (hg : ∀ i,D≤g i) : D≤(∑ i,w i*g i) := by
    calc
      _ = ∑ i,w i*D := by rw [← Finset.sum_mul,hs,one_mul]
      _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hg i) (hw i)
  unfold finiteRisk
  split_ifs with h0
  · rw [abs_le]
    exact ⟨hlow f (fun i => (abs_le.mp (hb i)).1),havg f (fun i => (abs_le.mp (hb i)).2)⟩
  · have hap : 0<a := lt_of_le_of_ne ha (Ne.symm h0)
    have hp := weighted_sum_pos hw hs (fun i => Real.exp_pos (a*f i))
    have hlu : Real.exp (a*(-C))≤∑ i,w i*Real.exp (a*f i) :=
      hlow _ (fun i => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_le.mp (hb i)).1 ha))
    have huu : (∑ i,w i*Real.exp (a*f i))≤Real.exp (a*C) :=
      havg _ (fun i => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (abs_le.mp (hb i)).2 ha))
    have hl := Real.log_le_log (Real.exp_pos (a*(-C))) hlu
    have hu := Real.log_le_log hp huu
    rw [Real.log_exp] at hl hu
    rw [abs_le,le_div_iff₀ hap,div_le_iff₀ hap]
    constructor <;> nlinarith

lemma finiteHierarchyRisk_uniform_abs {d : ℕ} {w : ι → ℝ}
    (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1) {a : Fin d → ℝ} (ha : ∀ k,0≤a k)
    {f : (Fin d → ι) → ℝ} {C : ℝ} (hb : ∀ s,|f s|≤C) : |finiteHierarchyRisk w a f|≤C := by
  induction d with
  | zero => exact hb _
  | succ d ih =>
    exact finiteRisk_uniform_abs hw hs (ha 0)
      (fun i => ih (fun k => ha k.succ) (fun s => hb _))

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite

def gaussianHierarchyRisk : {d : ℕ} → (Fin d → ℝ) → ((Fin d → ℝ) → ℝ) → ℝ
  | 0,_,f => f (fun k => Fin.elim0 k)
  | _+1,a,f => logMean (gaussianReal 0 1) (a 0)
      (fun z => gaussianHierarchyRisk (fun k => a k.succ) (fun s => f (Fin.cons z s)))

lemma continuous_gaussianLogMean {E : Type*} [TopologicalSpace E] [FirstCountableTopology E]
    {f : E → ℝ → ℝ} {C : ℝ} (a : ℝ)
    (hf : Continuous (Function.uncurry f)) (hb : ∀ e z,|f e z|≤C) :
    Continuous (fun e => logMean (gaussianReal 0 1) a (f e)) := by
  have hc (e : E) : Continuous (f e) := hf.comp (continuous_const.prodMk continuous_id)
  by_cases ha : a=0
  · simp only [ha,logMean_zero]
    apply continuous_of_dominated (bound:=fun _ => C)
    · intro e; exact (hc e).aestronglyMeasurable
    · intro e; exact ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hb e z
    · exact integrable_const C
    · filter_upwards with z
      exact hf.comp (continuous_id.prodMk continuous_const)
  · simp only [logMean,ha,↓reduceIte]
    have hi : Continuous (fun e => ∫ z,Real.exp (a*f e z) ∂gaussianReal 0 1) := by
      apply continuous_of_dominated (bound:=fun _ => Real.exp (|a| * C))
      · intro e; exact (Real.continuous_exp.comp ((hc e).const_mul a)).aestronglyMeasurable
      · intro e
        filter_upwards with z
        rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        exact (le_abs_self _).trans (by simpa only [abs_mul] using mul_le_mul_of_nonneg_left (hb e z) (abs_nonneg a))
      · exact integrable_const _
      · filter_upwards with z
        exact Real.continuous_exp.comp ((hf.comp (continuous_id.prodMk continuous_const)).const_mul a)
    exact (hi.log (fun e => ne_of_gt (ParisiFinite.integral_exp_pos
      (integrable_exp_of_uniform_abs a (hc e).measurable (hb e))))).div_const a

lemma continuous_finCons {E : Type*} [TopologicalSpace E] {d : ℕ}
    {x : E → ℝ} {y : E → Fin d → ℝ} (hx : Continuous x) (hy : Continuous y) :
    Continuous (fun e => (Fin.cons (x e) (y e) : Fin (d+1) → ℝ)) := by
  apply continuous_pi
  intro k
  cases k using Fin.cases with
  | zero => exact hx
  | succ k => exact (continuous_apply k).comp hy

lemma gaussianHierarchyRisk_continuous_bound {d : ℕ} {E : Type*}
    [TopologicalSpace E] [FirstCountableTopology E] {a : Fin d → ℝ} (ha : ∀ k,0≤a k)
    {f : E → (Fin d → ℝ) → ℝ} {C : ℝ} (hf : Continuous (Function.uncurry f))
    (hb : ∀ e s,|f e s|≤C) :
    Continuous (fun e => gaussianHierarchyRisk a (f e)) ∧
      ∀ e,|gaussianHierarchyRisk a (f e)|≤C := by
  induction d generalizing E with
  | zero =>
    exact ⟨hf.comp (continuous_id.prodMk continuous_const),fun e => hb e _⟩
  | succ d ih =>
    let g : (E×ℝ) → (Fin d → ℝ) → ℝ := fun e s => f e.1 (Fin.cons e.2 s)
    have hg : Continuous (Function.uncurry g) := by
      exact hf.comp ((continuous_fst.fst).prodMk (continuous_finCons continuous_fst.snd continuous_snd))
    have hh := ih (fun k => ha k.succ) hg (fun e s => hb e.1 _)
    have hlog := continuous_gaussianLogMean (a 0) hh.1 (fun e z => hh.2 (e,z))
    refine ⟨hlog,?_⟩
    intro e
    apply logMean_uniform_abs (ha 0)
    · exact (hh.1.comp (continuous_const.prodMk continuous_id)).measurable
    · intro z; exact hh.2 (e,z)

lemma gaussianHierarchyRisk_uniform_abs {d : ℕ} {a : Fin d → ℝ} (ha : ∀ k,0≤a k)
    {f : (Fin d → ℝ) → ℝ} {C : ℝ} (hf : Continuous f) (hb : ∀ s,|f s|≤C) :
    |gaussianHierarchyRisk a f|≤C :=
  (gaussianHierarchyRisk_continuous_bound (E:=Unit) (f:=fun _ s => f s) ha (hf.comp continuous_snd) (fun _ s => hb s)).2 ()

 

theorem quantizedHierarchyRisk_tendsto {d : ℕ} {E : Type*}
    [TopologicalSpace E] [FirstCountableTopology E] {a : Fin d → ℝ} (ha : ∀ k,0≤a k)
    {f : E → (Fin d → ℝ) → ℝ} {C : ℝ} (hf : Continuous (Function.uncurry f))
    (hb : ∀ e s,|f e s|≤C) {u : ℕ → E} {e : E} (hu : Tendsto u atTop (𝓝 e)) :
    Tendsto (fun m => finiteHierarchyRisk (gaussianQuantizerWeight m) a
      (fun s : Fin d → GaussianQuantizerLabel m => f (u m) (fun k => (s k).val))) atTop
      (𝓝 (gaussianHierarchyRisk a (f e))) := by
  induction d generalizing E with
  | zero =>
    simp only [finiteHierarchyRisk,gaussianHierarchyRisk]
    have he (m : ℕ) : (fun k : Fin 0 => ((Fin.elim0 k : GaussianQuantizerLabel m)).val)=
        (fun k : Fin 0 => (Fin.elim0 k : ℝ)) := Subsingleton.elim _ _
    simp_rw [he]
    exact hf.continuousAt.tendsto.comp (hu.prodMk_nhds tendsto_const_nhds)
  | succ d ih =>
    let g : (E×ℝ) → (Fin d → ℝ) → ℝ := fun e s => f e.1 (Fin.cons e.2 s)
    have hg : Continuous (Function.uncurry g) := by
      exact hf.comp ((continuous_fst.fst).prodMk (continuous_finCons continuous_fst.snd continuous_snd))
    let H (m : ℕ) (i : GaussianQuantizerLabel m) :=
      finiteHierarchyRisk (gaussianQuantizerWeight m) (fun k => a k.succ)
        (fun s : Fin d → GaussianQuantizerLabel m => f (u m) (Fin.cons i.val (fun k => (s k).val)))
    let G (z : ℝ) := gaussianHierarchyRisk (fun k => a k.succ) (fun s => f e (Fin.cons z s))
    have heq (m : ℕ) : finiteHierarchyRisk (gaussianQuantizerWeight m) a
        (fun s : Fin (d+1) → GaussianQuantizerLabel m => f (u m) (fun k => (s k).val))=
        logMean (gaussianReal 0 1) (a 0) (fun z => H m (gaussianQuantizerIndex m z)) := by
      change finiteRisk _ _ _=_
      rw [finiteRisk_eq_logMean,gaussianQuantizer_logMean]
      congr 1
      funext z
      congr 1
      funext s
      change f (u m) (fun k => ((Fin.cons (gaussianQuantizerIndex m z) s : Fin (d+1) → GaussianQuantizerLabel m) k).val)=
        f (u m) (Fin.cons (gaussianQuantizerIndex m z).val (fun k => (s k).val))
      congr 1
      funext k
      cases k using Fin.cases <;> rfl
    simp_rw [heq]
    change Tendsto _ _ (𝓝 (logMean (gaussianReal 0 1) (a 0) G))
    apply tendsto_logMean_of_uniform_abs (a 0) (C:=C)
    · intro m
      exact (measurable_of_finite (H m)).comp (gaussianQuantizerIndex_measurable m)
    · have hh := gaussianHierarchyRisk_continuous_bound (fun k => ha k.succ) hg (fun e s => hb e.1 _)
      exact (hh.1.comp (continuous_const.prodMk continuous_id)).measurable
    · intro m z
      exact finiteHierarchyRisk_uniform_abs (gaussianQuantizerWeight_nonneg m) (gaussianQuantizerWeight_sum m)
        (fun k => ha k.succ) (fun s => hb (u m) _)
    · intro z
      exact gaussianHierarchyRisk_uniform_abs (fun k => ha k.succ)
        (hf.comp (continuous_const.prodMk (continuous_finCons continuous_const continuous_id))) (fun s => hb e _)
    · intro z
      exact ih (fun k => ha k.succ) hg (fun e s => hb e.1 _)
        (hu.prodMk_nhds (gaussianQuantizer_tendsto z))

end SKCavity

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped BigOperators Topology NNReal ENNReal
namespace SKCavity
open SKQAOA SKGaussian ParisiInterpolation ParisiFinite

def gaussianHierarchyMoment {d : ℕ} (μ : ProbabilityMeasure OverlapArray)
    (q : Fin (d+1) → ℝ) (x : (Fin d → ℝ) → ℝ) (n : ℕ) : ℝ :=
  ∑ T : PartitionTree d n,(μ:Measure OverlapArray).real (hierarchyEvent (treeCodes T) q)*treeGaussianMoment T x

lemma hierarchyMarkedMoment_tendsto_gaussian {d : ℕ} (μ : ProbabilityMeasure OverlapArray)
    (q : Fin (d+1) → ℝ) {x : (Fin d → ℝ) → ℝ} (hx : Continuous x)
    (hb : ∀ s,0≤x s ∧ x s≤1) (n : ℕ) :
    Tendsto (fun m => hierarchyMarkedMoment μ q (gaussianQuantizerWeight m)
      (fun s : Fin d → GaussianQuantizerLabel m => x (fun k => (s k).val)) n) atTop
      (𝓝 (gaussianHierarchyMoment μ q x n)) := by
  unfold hierarchyMarkedMoment gaussianHierarchyMoment
  apply tendsto_finsetSum
  intro T _
  exact (treeMarkMoment_tendsto_gaussian T hx hb).const_mul _

lemma gaussianHierarchyMoment_mem_unit {d : ℕ} (μ : ProbabilityMeasure OverlapArray)
    (q : Fin (d+1) → ℝ) {x : (Fin d → ℝ) → ℝ} (hx : Continuous x)
    (hb : ∀ s,0≤x s ∧ x s≤1) (n : ℕ) :
    0≤gaussianHierarchyMoment μ q x n ∧ gaussianHierarchyMoment μ q x n≤1 := by
  have ht := hierarchyMarkedMoment_tendsto_gaussian μ q hx hb n
  have h (m : ℕ) := hierarchyMarkedMoment_mem_unit μ q (gaussianQuantizerWeight_nonneg m)
    (gaussianQuantizerWeight_sum m) (fun s : Fin d → GaussianQuantizerLabel m => hb (fun k => (s k).val)) n
  exact ⟨ge_of_tendsto ht (Eventually.of_forall (fun m => (h m).1)),
    le_of_tendsto ht (Eventually.of_forall (fun m => (h m).2))⟩

lemma normalized_moment_bound {M : ℝ} (hM : 0≤M ∧ M≤1) (z : ℝ) (n : ℕ) :
    ‖-M/(n:ℝ)*z^n‖≤|z|^n := by
  by_cases hn : n=0
  · simp [hn]
  have hn1 : (1:ℝ)≤n := by exact_mod_cast Nat.pos_of_ne_zero hn
  simp only [Real.norm_eq_abs,abs_mul,abs_div,abs_neg,abs_of_nonneg hM.1,
    abs_of_nonneg (Nat.cast_nonneg n : (0:ℝ)≤n),abs_pow]
  exact mul_le_of_le_one_left (pow_nonneg (abs_nonneg z) n)
    ((div_le_one (by positivity)).mpr (hM.2.trans hn1))

lemma affine_log_bounded {d : ℕ} {x : (Fin d → ℝ) → ℝ}
    (hb : ∀ s,0≤x s ∧ x s≤1) {z : ℝ} (hz : |z|<1) (s : Fin d → ℝ) :
    |Real.log (1-z*x s)|≤|Real.log (1-|z|)|+|Real.log (1+|z|)| := by
  have hp : 0<1-|z| := by linarith
  have hb' : |z*x s|≤|z| := by
    rw [abs_mul,abs_of_nonneg (hb s).1]
    exact mul_le_of_le_one_right (abs_nonneg z) (hb s).2
  have hl : 1-|z|≤1-z*x s := by linarith [(abs_le.mp hb').2]
  have hu : 1-z*x s≤1+|z| := by linarith [(abs_le.mp hb').1]
  have hlogl := Real.log_le_log hp hl
  have hlogu := Real.log_le_log (hp.trans_le hl) hu
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log (1-|z|)),abs_nonneg (Real.log (1+|z|))]
  · linarith [le_abs_self (Real.log (1+|z|)),abs_nonneg (Real.log (1-|z|))]

 

theorem GG_gaussian_hierarchy_log_identity {μ : ProbabilityMeasure OverlapArray}
    (hG : (μ:Measure OverlapArray) GramArrays=1) (hgg : GGIdentities μ)
    (hu : (μ:Measure OverlapArray) UltrametricArrays=1)
    {d : ℕ} (q : Fin (d+2) → ℝ) (hq : Monotone q) (h0 : q 0 < -1)
    (h1 : q (Fin.last (d+1))<1) (ha : ∀ k : Fin (d+1),overlapDiscount μ (q k.succ)≠0)
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
    rw [← hierarchyLog_eq_finiteHierarchyRisk (gaussianQuantizerWeight_nonneg m)
      (gaussianQuantizerWeight_sum m) a ha (fun s => affine_mark_pos (hb _) hz)]
    rw [GG_hierarchy_log_identity hG hgg hu q hq h0 h1 ha
      (gaussianQuantizerWeight_nonneg m) (gaussianQuantizerWeight_sum m) (fun s => hb _) hz]
    simp only [FormalMultilinearSeries.sum,hierarchyLogSeries,FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul]
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
open SKQAOA SKGaussian ParisiInterpolation

lemma card_injective_replica_maps (r k : ℕ) :
    (Finset.univ.filter (fun e : Fin k → Fin r => Function.Injective e)).card=r.descFactorial k := by
  classical
  let I := Finset.univ.filter (fun e : Fin k → Fin r => Function.Injective e)
  let e : ↥I ≃ (Fin k ↪ Fin r) :=
      { toFun := fun e => ⟨e.val,(Finset.mem_filter.mp e.property).2⟩
        invFun := fun e => ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,e.injective⟩⟩
        left_inv := fun e => rfl
        right_inv := fun e => rfl }
  change I.card=_
  rw [← Fintype.card_coe]
  exact (Fintype.card_congr e).trans (by simp)

lemma descFactorial_ratio_tendsto (k : ℕ) :
    Tendsto (fun r : ℕ => ((r+1).descFactorial k:ℝ)/(r+1:ℕ)^k) atTop (𝓝 1) := by
  have he : ∀ᶠ r : ℕ in atTop,
      ((r+1).descFactorial k:ℝ)/(r+1:ℕ)^k=
        ∏ i : Fin k,(1-(i:ℕ)/(r+1:ℝ)) := by
    filter_upwards [eventually_ge_atTop k] with r hr
    rw [Nat.descFactorial_eq_prod_range]
    push_cast
    rw [← Fin.prod_univ_eq_prod_range]
    have hd : (r+1:ℝ)^k=∏ i:Fin k,(r+1:ℝ) := by simp
    rw [hd,← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [Nat.cast_sub (by omega)]
    have h : (r+1:ℝ)≠0 := by positivity
    push_cast
    field_simp
  apply Tendsto.congr' (he.mono (fun r h => h.symm))
  have hi (i : Fin k) : Tendsto (fun r : ℕ => 1-(i:ℕ)/(r+1:ℝ)) atTop (𝓝 (1:ℝ)) := by
    have h := tendsto_succ_reciprocal.const_mul (i:ℝ)
    simpa only [mul_zero,sub_zero,mul_one_div,Nat.cast_add,Nat.cast_one] using tendsto_const_nhds.sub h
  simpa using tendsto_finsetProd Finset.univ (fun i _ => hi i)

 

theorem replica_average_moment_tendsto (k : ℕ)
    (H : (r : ℕ) → (Fin k → Fin (r+1)) → ℝ) {M : ℝ} (_hM : 0≤M ∧ M≤1)
    (hH : ∀ r e,0≤H r e ∧ H r e≤1)
    (he : ∀ r e,Function.Injective e → H r e=M) :
    Tendsto (fun r => (∑ e,H r e)/(r+1:ℕ)^k) atTop (𝓝 M) := by
  classical
  let C (r : ℕ) : ℝ := ((r+1).descFactorial k:ℝ)/(r+1:ℕ)^k
  have hb (r : ℕ) : C r*M≤(∑ e,H r e)/(r+1:ℕ)^k ∧
      (∑ e,H r e)/(r+1:ℕ)^k≤C r*M+(1-C r) := by
    let I : Finset (Fin k → Fin (r+1)) := Finset.univ.filter Function.Injective
    have hsum : (∑ e∈I,H r e)=I.card*M := by
      rw [Finset.sum_congr rfl (fun e he' => he r e ((Finset.mem_filter.mp he').2))]
      simp only [Finset.sum_const,nsmul_eq_mul]
      rfl
    have hall : (∑ e,H r e)=(∑ e∈I,H r e)+∑ e∈Finset.univ\I,H r e := by
      exact (Finset.sum_add_sum_compl I (fun e => H r e)).symm
    have hlow : 0≤∑ e∈Finset.univ\I,H r e := Finset.sum_nonneg (fun e _ => (hH r e).1)
    have hup : (∑ e∈Finset.univ\I,H r e)≤(Finset.univ\I).card := by
      simpa using Finset.sum_le_sum (s:=Finset.univ\I) (fun e _ => (hH r e).2)
    have hcard : I.card=(r+1).descFactorial k := card_injective_replica_maps _ _
    have hcc : (I.card:ℝ)+((Finset.univ\I).card:ℝ)=(r+1:ℕ)^k := by
      have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ I)
      have hh' : (Finset.univ\I).card+I.card=(r+1)^k := by simpa using hh
      have hh'' : ((Finset.univ\I).card:ℝ)+(I.card:ℝ)=(r+1:ℕ)^k := by exact_mod_cast hh'
      linarith
    have hD : (0:ℝ)<(r+1:ℕ)^k := by positivity
    rw [hall,hsum]
    dsimp only [C]
    rw [← hcard]
    constructor
    · rw [div_mul_eq_mul_div]
      exact (div_le_div_iff_of_pos_right hD).mpr (by linarith)
    · rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hD).mpr
      field_simp
      nlinarith
  have hC : Tendsto C atTop (𝓝 1) := descFactorial_ratio_tendsto k
  have hl := hC.mul_const M
  have hu : Tendsto (fun r => C r*M+(1-C r)) atTop (𝓝 M) := by
    simpa using (hC.mul_const M).add ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).sub hC)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hl) (by simpa using hu)
    (fun r => (hb r).1) (fun r => (hb r).2)

end SKCavity

end

end OAI
