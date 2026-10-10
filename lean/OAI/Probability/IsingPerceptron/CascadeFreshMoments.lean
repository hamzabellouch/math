import Mathlib
import OAI.Probability.IsingPerceptron.GaussianMomentTest

namespace OAI

/-! Cascade Fresh Moments. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

lemma freshPatternFactor_replica_moment {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Ω → Measure X)
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (A : X → ℕ →₀ ℝ) {f : ℝ → ℝ} (hf : Measurable f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) (m : ℕ) :
    (∫ z : Ω × (ℕ → ℝ), (freshPatternFactor (ν z.1) A f z.2)^m ∂P.prod gaussianCoordinates) =
      ∫ σ, gaussianMoment m f (fun i j : Fin m => cylinderCross (A (σ i)) (A (σ j)))
        ∂replicaLaw P ν hν := by
  rw [replicaLaw_integral_prefix P ν hν
    (fun σ : Fin m → X => gaussianMoment m f (fun i j : Fin m => cylinderCross (A (σ i)) (A (σ j))))
    (fun σ => gaussianMoment_bound m hK _)]
  have hi : Integrable (fun z : Ω × (ℕ → ℝ) => (freshPatternFactor (ν z.1) A f z.2)^m)
      (P.prod gaussianCoordinates) := by
    apply Integrable.of_bound ((measurable_random_freshPatternFactor hν A hf).pow_const m).aestronglyMeasurable
      ((Real.exp K)^m)
    exact ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_pow,abs_of_nonneg ((Real.exp_pos _).le.trans (freshPatternFactor_bound (ν z.1) A f hK z.2).1)]
      exact pow_le_pow_left₀ ((Real.exp_pos _).le.trans (freshPatternFactor_bound (ν z.1) A f hK z.2).1)
        (freshPatternFactor_bound (ν z.1) A f hK z.2).2 _)
  rw [integral_prod _ hi]
  exact integral_congr_ae (ae_of_all _ (fun ω => freshPatternFactor_moment (ν ω) A hf hK m))

 

def cascadeFreshFactor (n : ℕ) (a : ℕ → ℝ) (f : ℝ → ℝ)
    (p : LabeledTree n × (ℕ → ℝ)) : ℝ :=
  freshPatternFactor (labeledLeafLaw n p.1)
    (fun v => treeFieldCoefficients n v (fun i => pathAmplitude a i) (fun _ : Unit => 1))
    (gaussianTransform (1-a n) 1 f) p.2

lemma measurable_cascadeFreshFactor (n : ℕ) (a : ℕ → ℝ) {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (cascadeFreshFactor n a f) := by
  apply measurable_random_freshPatternFactor (measurable_labeledLeafLaw n)
  rw [gaussianTransform_one]
  exact (measurable_rowFactor _ hf).log

lemma cascadeFreshFactor_bound (n : ℕ) (a : ℕ → ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    {K : ℝ} (hb : ∀ x, |f x| ≤ K) (p : LabeledTree n × (ℕ → ℝ)) :
    cascadeFreshFactor n a f p ∈ Icc (Real.exp (-K)) (Real.exp K) :=
  freshPatternFactor_bound _ _ _ (gaussianTransform_one_bound _ hf hb) _

 

theorem cascadeFreshFactor_moment (n : ℕ) (b a : ℕ → ℝ) (ha : Monotone a) (ha0 : 0 ≤ a 0)
    (ha1 : a n ≤ 1) {f : ℝ → ℝ} (hf : Measurable f) {K : ℝ} (hb : ∀ x, |f x| ≤ K) (m : ℕ) :
    (∫ p, (cascadeFreshFactor n a f p)^m
      ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates) =
      ∫ σ, gaussianMoment m f (fun i j : Fin m => diagonalPatch 1 (cascadeScalarArray n a σ) i j)
        ∂cascadeReplicaLaw n b := by
  rw [cascadeReplicaLaw_eq_replicaLaw]
  change (∫ p, (freshPatternFactor _ _ _ _ : ℝ)^m ∂_) = _
  rw [freshPatternFactor_replica_moment _ _ (measurable_labeledLeafLaw n) _
    (by rw [gaussianTransform_one]; exact (measurable_rowFactor _ hf).log)
    (gaussianTransform_one_bound _ hf hb)]
  apply integral_congr_ae
  filter_upwards [] with σ
  rw [gaussianMoment_residual _ (sub_nonneg.mpr ha1) hf hb]
  congr 1
  funext i j
  rw [treeField_path_cross n (σ i) (σ j) ha ha0]
  simp only [Fintype.sum_unique,mul_one,diagonalPatch,cascadeScalarArray]
  by_cases hij : i=j
  · subst j
    simp only [ite_true,labeledCommonDepth_self]
    ring
  · simp [hij,show (i:ℕ) ≠ (j:ℕ) from fun h => hij (Fin.ext h)]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma measurable_scalar_root_factor (n : ℕ) (s : ℕ → ℝ) {F : ℝ → ℝ}
    (hF : Measurable F) (c : ℝ) :
    Measurable (fun p : (LabeledTree n × ℝ) × (ForestVertex n → ℝ) =>
      Real.log (labeledScalarFactor n s F (c*p.1.2) (p.1.1,p.2))) := by
  let j : (LabeledTree n × ℝ) × (ForestVertex n → ℝ) → ℝ × (LabeledTree n × (ForestVertex n → ℝ)) :=
    fun p => (c*p.1.2,(p.1.1,p.2))
  have hj : Measurable j :=
    (measurable_fst.snd.const_mul c).prodMk (measurable_fst.fst.prodMk measurable_snd)
  exact ((measurable_labeledScalarFactor n s hF).comp hj).log

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma scalarFreshFactor_nodes (n : ℕ) (a : ℕ → ℝ) (F : ℝ → ℝ) (T : LabeledTree n) (g : ℕ → ℝ) :
    freshPatternFactor (labeledLeafLaw n T)
      (fun v => treeFieldCoefficients n v (fun i => pathAmplitude a i) (fun _ : Unit => 1)) F g =
    labeledScalarFactor n (fun i => pathAmplitude a (i+1)) F (pathAmplitude a 0*scalarGaussianNodes n g none)
      (T,fun v => scalarGaussianNodes n g (some v)) := by
  unfold freshPatternFactor labeledScalarFactor
  apply integral_congr_ae
  filter_upwards [] with v
  rw [cylinderField_scalar_nodes]

lemma scalarFresh_log_bound (n : ℕ) (a : ℕ → ℝ) (F : ℝ → ℝ) {K : ℝ}
    (hF : ∀ y, |F y| ≤ K) (T : LabeledTree n) (g : ℕ → ℝ) :
    |Real.log (freshPatternFactor (labeledLeafLaw n T)
      (fun v => treeFieldCoefficients n v (fun i => pathAmplitude a i) (fun _ : Unit => 1)) F g)| ≤ K := by
  rw [scalarFreshFactor_nodes]
  exact labeledScalar_log_bound _ _ _ hF _ _

 

theorem scalarFresh_log_recursion (n : ℕ) (b a : ℕ → ℝ) (hb : CascadeExponents n b)
    {F : ℝ → ℝ} (hF : Measurable F) {K : ℝ} (hbound : ∀ y, |F y| ≤ K) :
    (∫ p, Real.log (freshPatternFactor (labeledLeafLaw n p.1)
      (fun v => treeFieldCoefficients n v (fun i => pathAmplitude a i) (fun _ : Unit => 1)) F p.2)
      ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates) =
    ∫ z, cascadeRecursion n b (fun _ => ⟨gaussianReal 0 1,inferInstance⟩)
      (fun i p => p.1+pathAmplitude a (i+1)*p.2) F (pathAmplitude a 0*z) ∂gaussianReal 0 1 := by
  let P := (labeledCascadeLaw n b : Measure (LabeledTree n))
  let Q := Measure.infinitePi (fun _ : ForestVertex n => gaussianReal 0 1)
  let s := fun i => pathAmplitude a (i+1)
  let J : (LabeledTree n × ℝ) × (ForestVertex n → ℝ) → ℝ :=
    fun p => Real.log (labeledScalarFactor n s F (pathAmplitude a 0*p.1.2) (p.1.1,p.2))
  have hJ : Measurable J := measurable_scalar_root_factor n s hF (pathAmplitude a 0)
  have hJB (p) : |J p| ≤ K := labeledScalar_log_bound n s F hbound _ _
  have hi : Integrable (fun p : LabeledTree n × (ℕ → ℝ) => Real.log (freshPatternFactor (labeledLeafLaw n p.1)
      (fun v => treeFieldCoefficients n v (fun i => pathAmplitude a i) (fun _ : Unit => 1)) F p.2))
      (P.prod gaussianCoordinates) := by
    apply Integrable.of_bound ((measurable_random_freshPatternFactor (measurable_labeledLeafLaw n) _ hF).log).aestronglyMeasurable K
    exact ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs] using scalarFresh_log_bound n a F hbound p.1 p.2)
  rw [integral_prod _ hi]
  have heT (T : LabeledTree n) :
      (∫ g, Real.log (freshPatternFactor (labeledLeafLaw n T)
        (fun v => treeFieldCoefficients n v (fun i => pathAmplitude a i) (fun _ : Unit => 1)) F g) ∂gaussianCoordinates) =
      ∫ z, ∫ w, J ((T,z),w) ∂Q ∂gaussianReal 0 1 := by
    have hm : Measurable (fun p : ℝ × (ForestVertex n → ℝ) => J ((T,p.1),p.2)) := hJ.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    have hI : Integrable (fun p : ℝ × (ForestVertex n → ℝ) => J ((T,p.1),p.2)) ((gaussianReal 0 1).prod Q) := by
      apply Integrable.of_bound hm.aestronglyMeasurable K
      exact ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs,Function.comp_apply] using hJB ((T,p.1),p.2))
    have he := (HasLaw.mk (scalarGaussianRootForest_law n).measurable.aemeasurable
      (scalarGaussianRootForest_law n).map_eq).integral_comp hm.aestronglyMeasurable
    rw [integral_prod _ hI] at he
    simpa only [Function.comp_apply,scalarFreshFactor_nodes,J,s] using he
  simp_rw [heT]
  have hI : Integrable (fun p : LabeledTree n × ℝ => ∫ w, J (p,w) ∂Q) (P.prod (gaussianReal 0 1)) := by
    apply Integrable.of_bound hJ.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable K
    filter_upwards [] with p
    have hh : ‖∫ w, J (p,w) ∂Q‖ ≤ K*Q.real univ :=
      norm_integral_le_of_norm_le_const (ae_of_all _ (fun w => by simpa only [Real.norm_eq_abs,Function.comp_apply] using hJB (p,w)))
    simpa using hh
  rw [integral_integral_swap hI]
  apply integral_congr_ae
  filter_upwards [] with z
  have hz : Integrable (fun p : LabeledTree n × (ForestVertex n → ℝ) => J ((p.1,z),p.2)) (P.prod Q) := by
    apply Integrable.of_bound (hJ.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)).aestronglyMeasurable K
    exact ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs,Function.comp_apply] using hJB ((p.1,z),p.2))
  rw [← integral_prod _ hz]
  exact labeledScalar_log_recursion n b s hb hF hbound (pathAmplitude a 0*z)

 
theorem cascadeFresh_log_value (n : ℕ) (b a : ℕ → ℝ) (hb : CascadeExponents n b)
    {f : ℝ → ℝ} (hf : Measurable f) {K : ℝ} (hbound : ∀ y, |f y| ≤ K) :
    (∫ p, Real.log (cascadeFreshFactor n a f p)
      ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates) =
    gaussianTransform (a 0) 0
      ((List.ofFn (fun i : Fin n => (pathIncrement a (i+1),b i))).foldr
        (fun sd U => gaussianTransform sd.1 sd.2 U) (gaussianTransform (1-a n) 1 f)) 0 := by
  rw [show cascadeFreshFactor n a f = fun p => freshPatternFactor (labeledLeafLaw n p.1)
      (fun v => treeFieldCoefficients n v (fun i => pathAmplitude a i) (fun _ : Unit => 1))
      (gaussianTransform (1-a n) 1 f) p.2 from rfl]
  rw [scalarFresh_log_recursion n b a hb
    (by rw [gaussianTransform_one]; exact (measurable_rowFactor _ hf).log)
    (gaussianTransform_one_bound _ hf hbound)]
  change (∫ z, cascadeRecursion n b _ (fun i p => p.1+Real.sqrt (pathIncrement a (i+1))*p.2)
    (gaussianTransform (1-a n) 1 f) (pathAmplitude a 0*z) ∂gaussianReal 0 1) = _
  rw [cascadeRecursion_gaussian n b (fun i => pathIncrement a (i+1)) _ (fun i hi => (hb.1 i hi).1.ne')]
  simp only [gaussianTransform,ite_true,pathAmplitude,pathIncrement,zero_add]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma cell_subset_unit (n i : ℕ) (hi : i ≤ n) :
    Ioo ((i:ℝ)/(n+1:ℕ)) (((i:ℝ)+1)/(n+1:ℕ)) ⊆ Ioo (0:ℝ) 1 := by
  intro u hu
  constructor
  · exact lt_of_le_of_lt (by positivity) hu.1
  · apply hu.2.trans_le
    apply (div_le_one (by positivity : (0:ℝ) < (n+1:ℕ))).mpr
    exact_mod_cast Nat.succ_le_succ hi

lemma uniformCellAverage_eq_cellAverage (q : OverlapPath) (p : ℝ → ℝ)
    (hp : p =ᵐ[pathMeasure] q.val) (n i : ℕ) (hi : i ≤ n) :
    uniformCellAverage p n i = cellAverage q (n+1) i := by
  unfold uniformCellAverage cellAverage
  congr 1
  have hm : pathMeasure.restrict (Ioo ((i:ℝ)/(n+1:ℕ)) (((i:ℝ)+1)/(n+1:ℕ))) =
      volume.restrict (Ioo ((i:ℝ)/(n+1:ℕ)) (((i:ℝ)+1)/(n+1:ℕ))) := by
    rw [pathMeasure,Measure.restrict_restrict measurableSet_Ioo,inter_eq_left.mpr (cell_subset_unit n i hi)]
  rw [← hm]
  exact integral_congr_ae hp.restrict

lemma uniformPattern_root_tail (f : ℝ → ℝ) (q : OverlapPath) (n : ℕ) :
    uniformPattern f q n =
    gaussianTransform (cellAverage q (n+1) 0) 0
      ((List.ofFn (fun i : Fin n => (cellAverage q (n+1) (i+1)-cellAverage q (n+1) i,
        uniformExponent n i))).foldr
        (fun sd U => gaussianTransform sd.1 sd.2 U)
        (gaussianTransform (1-cellAverage q (n+1) n) 1 f)) 0 := by
  dsimp only [uniformPattern]
  rw [List.ofFn_succ]
  simp only [Fin.val_zero,Nat.cast_zero,Nat.zero_lt_succ,ite_true,sub_zero,zero_div,List.foldr_cons]
  apply congrArg (fun U : ℝ → ℝ => gaussianTransform (cellAverage q (n+1) 0) 0 U 0)
  rw [List.ofFn_succ']
  rw [List.concat_eq_append]
  simp only [List.foldr_append,List.foldr_cons,List.foldr_nil]
  congr 1
  · simp only [Fin.val_last,Fin.val_succ,Nat.lt_irrefl,ite_false,Nat.succ_ne_zero,
      Nat.add_sub_cancel,Nat.lt_succ_self,ite_true,Nat.cast_add,Nat.cast_one]
    rw [div_self (by positivity : (n:ℝ)+1 ≠ 0)]
  · apply congrArg List.ofFn
    funext i
    simp only [Fin.val_castSucc,Fin.val_succ,Nat.add_sub_cancel,Nat.succ_ne_zero,ite_false,
      show i.val+1 < n+1 by omega,show i.val < n+1 by omega,ite_true,uniformExponent,Nat.cast_add,Nat.cast_one]

lemma cascadeFresh_uniformPattern (q : OverlapPath) (p : ℝ → ℝ)
    (hp : p =ᵐ[pathMeasure] q.val) (n : ℕ)
    {f : ℝ → ℝ} (hf : Measurable f) {K : ℝ} (hbound : ∀ y, |f y| ≤ K) :
    (∫ x, Real.log (cascadeFreshFactor n (uniformCellAverage p n) f x)
      ∂(labeledCascadeLaw n (uniformExponent n) : Measure (LabeledTree n)).prod gaussianCoordinates) =
    uniformPattern f q n := by
  rw [cascadeFresh_log_value n _ _ (uniformExponent_cascade n) hf hbound,uniformPattern_root_tail]
  congr 2
  · exact uniformCellAverage_eq_cellAverage q p hp n 0 (Nat.zero_le _)
  congr 2
  · exact uniformCellAverage_eq_cellAverage q p hp n n le_rfl
  · apply congrArg List.ofFn
    funext i
    simp only [pathIncrement]
    rw [uniformCellAverage_eq_cellAverage q p hp n (i+1) (by omega),
      uniformCellAverage_eq_cellAverage q p hp n i (by omega)]

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
namespace IsingPerceptron

def unitClip (x : ℝ) : ℝ := max 0 (min 1 x)
lemma unitClip_mem (x : ℝ) : unitClip x ∈ Icc (0:ℝ) 1 :=
  ⟨le_max_left _ _,max_le zero_le_one (min_le_left _ _)⟩
lemma unitClip_eq {x : ℝ} (h : x ∈ Icc (0:ℝ) 1) : unitClip x = x := by
  simp only [unitClip,min_eq_right h.2,max_eq_right h.1]
lemma continuous_unitClip : Continuous unitClip := by unfold unitClip; fun_prop

def scalarJointEntry (x : ℝ) : JointEntry :=
  (⟨unitClip x,⟨(by norm_num : (-1:ℝ) ≤ 0).trans (unitClip_mem x).1,(unitClip_mem x).2⟩⟩,⟨0,by norm_num⟩)
lemma continuous_scalarJointEntry : Continuous scalarJointEntry := by
  unfold scalarJointEntry
  exact continuous_unitClip.subtype_mk _ |>.prodMk continuous_const

def compactScalarArray (B : RealArray) : JointArray := fun ij => scalarJointEntry (B ij.1 ij.2)
lemma continuous_compactScalarArray : Continuous compactScalarArray := by
  apply continuous_pi; intro ij
  exact continuous_scalarJointEntry.comp (by fun_prop)

lemma spinArray_compactScalarArray {B : RealArray} (hB : ∀ i j, B i j ∈ Icc (0:ℝ) 1) :
    spinArray (compactScalarArray B) = B := by
  funext i j
  exact unitClip_eq (hB i j)

def cascadeCompactLaw (n : ℕ) (b a : ℕ → ℝ) : ProbabilityMeasure JointArray :=
  ⟨(cascadeReplicaLaw n b).map (fun σ => compactScalarArray (diagonalPatch 1 (cascadeScalarArray n a σ))),
    by infer_instance⟩

lemma cascade_patch_mem (n : ℕ) {a : ℕ → ℝ} (ha : Monotone a) (h0 : 0 ≤ a 0) (h1 : a n ≤ 1)
    (σ : ℕ → LabeledLeaf n) (i j : ℕ) :
    diagonalPatch 1 (cascadeScalarArray n a σ) i j ∈ Icc (0:ℝ) 1 := by
  unfold diagonalPatch cascadeScalarArray
  split_ifs
  · exact ⟨zero_le_one,le_rfl⟩
  · exact ⟨h0.trans (ha (Nat.zero_le _)),(ha (labeledCommonDepth_le n _ _)).trans h1⟩

lemma cascadeCompact_spin (n : ℕ) {a : ℕ → ℝ} (ha : Monotone a) (h0 : 0 ≤ a 0) (h1 : a n ≤ 1)
    (σ : ℕ → LabeledLeaf n) :
    spinArray (compactScalarArray (diagonalPatch 1 (cascadeScalarArray n a σ))) =
      diagonalPatch 1 (cascadeScalarArray n a σ) :=
  spinArray_compactScalarArray (cascade_patch_mem n ha h0 h1 σ)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
namespace IsingPerceptron

 

lemma cascade_integral_GG (n r : ℕ) (b : ℕ → ℝ) (hb : CascadeExponents n b)
    (a : ℕ → ℝ) (i : Fin (r+1)) (D : (Fin (r+1) → Fin (r+1) → ℝ) → ℝ)
    (c : ℝ → ℝ) :
    ((r+1:ℕ):ℝ)*(∫ σ, D (arrayBlock (cascadeScalarArray n a) (r+1) σ)*c (cascadeScalarArray n a σ i (r+1)) ∂cascadeReplicaLaw n b) -
      (∫ σ, D (arrayBlock (cascadeScalarArray n a) (r+1) σ) ∂cascadeReplicaLaw n b)*
      (∫ σ, c (cascadeScalarArray n a σ 0 1) ∂cascadeReplicaLaw n b) -
      ∑ j ∈ Finset.univ.erase i,
        ∫ σ, D (arrayBlock (cascadeScalarArray n a) (r+1) σ)*c (cascadeScalarArray n a σ i j) ∂cascadeReplicaLaw n b = 0 := by
  let E : PrefixPattern n (r+1) → ℝ := fun Q => D (fun i j => prefixVectorValue n a (Q i j))
  let e : ℕ → ℝ := fun k => c (a k)
  have h := prefixGGResidual_value n r b hb i E e
  change ((r+1:ℕ):ℝ)*prefixPatternMean n (r+1+1) b
      (fun Q => E (patternReindex Q Fin.castSucc)*prefixVectorValue n e (Q i.castSucc (Fin.last (r+1)))) -
    prefixPatternMean n (r+1) b E*prefixPatternMean n 2 b (fun Q => prefixVectorValue n e (Q 0 1)) -
    (∑ j ∈ Finset.univ.erase i, prefixPatternMean n (r+1) b (fun Q => E Q*prefixVectorValue n e (Q i j))) = 0 at h
  unfold arrayBlock
  simpa only [prefixPatternMean,E,e,patternReindex_label,prefixVectorValue_pattern,
    Function.comp_apply,Fin.val_castSucc,Fin.val_last,Fin.val_zero,Fin.val_one,cascadeScalarArray] using h

lemma cascade_patch_integral_GG (n m : ℕ) (hm : 0 < m) (b : ℕ → ℝ)
    (hb : CascadeExponents n b) (a : ℕ → ℝ) (i : Fin m) (v : ℝ)
    (D : (Fin m → Fin m → ℝ) → ℝ) (c : ℝ → ℝ) :
    (m:ℝ)*(∫ σ, D (arrayBlock (fun σ => diagonalPatch v (cascadeScalarArray n a σ)) m σ)*
        c (diagonalPatch v (cascadeScalarArray n a σ) i m) ∂cascadeReplicaLaw n b) -
      (∫ σ, D (arrayBlock (fun σ => diagonalPatch v (cascadeScalarArray n a σ)) m σ) ∂cascadeReplicaLaw n b)*
      (∫ σ, c (diagonalPatch v (cascadeScalarArray n a σ) 0 1) ∂cascadeReplicaLaw n b) -
      ∑ j ∈ Finset.univ.erase i,
        ∫ σ, D (arrayBlock (fun σ => diagonalPatch v (cascadeScalarArray n a σ)) m σ)*
          c (diagonalPatch v (cascadeScalarArray n a σ) i j) ∂cascadeReplicaLaw n b = 0 := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have h := cascade_integral_GG n r b hb a i (fun B => D (diagonalPatch v B)) c
  simp_rw [diagonalPatch_arrayBlock]
  have hin : (i:ℕ) ≠ r+1 := Nat.ne_of_lt i.isLt
  simp only [diagonalPatch,hin,show (0:ℕ) ≠ 1 by omega,ite_false]
  have hs : (∑ j ∈ Finset.univ.erase i, ∫ σ, D (diagonalPatch v (arrayBlock (cascadeScalarArray n a) (r+1) σ))*
        c (if (i:ℕ) = (j:ℕ) then v else cascadeScalarArray n a σ i j) ∂cascadeReplicaLaw n b) =
      ∑ j ∈ Finset.univ.erase i, ∫ σ, D (diagonalPatch v (arrayBlock (cascadeScalarArray n a) (r+1) σ))*
        c (cascadeScalarArray n a σ i j) ∂cascadeReplicaLaw n b := by
    apply Finset.sum_congr rfl
    intro j hj
    have hij : (i:ℕ) ≠ (j:ℕ) := fun h => (Finset.mem_erase.mp hj).1 (Fin.ext h).symm
    simp only [hij,ite_false]
  rw [hs]
  exact h

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Classical
namespace IsingPerceptron

lemma cascadeCompact_integral (n : ℕ) (b a : ℕ → ℝ) {F : JointArray → ℝ}
    (hF : Measurable F) :
    (∫ x, F x ∂(cascadeCompactLaw n b a : Measure JointArray)) =
      ∫ σ, F (compactScalarArray (diagonalPatch 1 (cascadeScalarArray n a σ))) ∂cascadeReplicaLaw n b := by
  exact integral_map
    (continuous_compactScalarArray.measurable.comp ((measurable_diagonalPatch 1).comp (measurable_cascadeScalarArray n a))).aemeasurable
    hF.aestronglyMeasurable

lemma cascadeCompact_residual (n : ℕ) (b a : ℕ → ℝ) (hb : CascadeExponents n b)
    (m : ℕ) (hm : 0 < m) (i : Fin m) (D : JointBlock m → ℝ) (hD : Continuous D) (p d : ℕ) :
    jointMonomialResidual (cascadeCompactLaw n b a) m i D p d = 0 := by
  have hDm : Measurable (fun x : JointArray => D (jointBlockView m x)) := hD.measurable.comp (continuous_jointBlockView m).measurable
  have htest (j : ℕ) : Measurable (fun x : JointArray => D (jointBlockView m x)*(x (i,j)).1.1^p*(x (i,j)).2.1^d) :=
    (hDm.mul (by fun_prop)).mul (by fun_prop)
  unfold jointMonomialResidual
  rw [cascadeCompact_integral n b a (htest m),cascadeCompact_integral n b a hDm,
    cascadeCompact_integral n b a (by fun_prop)]
  simp_rw [cascadeCompact_integral n b a (htest _)]
  have h := cascade_patch_integral_GG n m hm b hb a i 1
    (fun B => D (fun i j => scalarJointEntry (B i j))) (fun x => unitClip x^p*(0:ℝ)^d)
  unfold jointBlockView compactScalarArray
  simpa only [scalarJointEntry,arrayBlock,mul_assoc] using h

lemma cascadeCompact_limit_GG {n : ℕ → ℕ} {b a : ℕ → ℕ → ℝ}
    (hb : ∀ k, CascadeExponents (n k) (b k)) {μ : ProbabilityMeasure JointArray}
    (hL : Tendsto (fun k => cascadeCompactLaw (n k) (b k) (a k)) atTop (𝓝 μ)) :
    HasEntryGhirlandaGuerra (fun x i j => x (i,j)) (μ : Measure JointArray) := by
  apply jointGG_of_weak_monomial_residuals hL
  intro r hr i D hD p d
  simpa only [cascadeCompact_residual _ _ _ (hb _) r (by omega) i D hD p d] using
    (tendsto_const_nhds (x := (0:ℝ)) : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix Classical
namespace IsingPerceptron

lemma cascade_patch_gram (n : ℕ) {a : ℕ → ℝ} (ha : Monotone a) (h0 : 0 ≤ a 0) (h1 : a n ≤ 1)
    (σ : ℕ → LabeledLeaf n) : GramDiagonal 1 (diagonalPatch 1 (cascadeScalarArray n a σ)) := by
  constructor
  · intro m
    let A : Fin m → ℕ →₀ ℝ := fun i => treeFieldCoefficients n (σ i) (fun j => pathAmplitude a j) (fun _ : Unit => 1)
    have hA (i j : Fin m) : cylinderCross (A i) (A j) = cascadeScalarArray n a σ i j := by
      rw [treeField_path_cross n (σ i) (σ j) ha h0]
      simp only [Fintype.sum_unique,mul_one,cascadeScalarArray]
    have hM : (fun i j : Fin m => diagonalPatch 1 (cascadeScalarArray n a σ) i j) =
        (show Matrix (Fin m) (Fin m) ℝ from fun i j => cylinderCross (A i) (A j))+Matrix.diagonal (fun _ => 1-a n) := by
      funext i j
      change (if (i:ℕ)=(j:ℕ) then 1 else cascadeScalarArray n a σ i j) =
        cylinderCross (A i) (A j)+(if i=j then 1-a n else 0)
      simp only [hA,Fin.val_inj]
      by_cases hij : i=j
      · subst j
        simp only [ite_true,cascadeScalarArray,labeledCommonDepth_self]
        ring
      · simp only [hij,ite_false,add_zero]
    rw [hM]
    exact (cylinderCross_matrix_posSemidef A).add (Matrix.PosSemidef.diagonal (fun _ => sub_nonneg.mpr h1))
  · intro i
    simp only [diagonalPatch,ite_true]

lemma cascade_patch_ultra (n : ℕ) {a : ℕ → ℝ} (ha : Monotone a) (h1 : a n ≤ 1)
    (σ : ℕ → LabeledLeaf n) : IsUltrametricArray (diagonalPatch 1 (cascadeScalarArray n a σ)) := by
  apply diagonalPatch_ultrametric
  · exact fun i j => congrArg a (labeledCommonDepth_symm n (σ i) (σ j))
  · exact fun i j k => monotone_labeledCommonDepth_ultrametric n ha (σ i) (σ j) (σ k)
  · exact fun i j => (ha (labeledCommonDepth_le n (σ i) (σ j))).trans h1

lemma cascadeCompact_geometry (n : ℕ) (b : ℕ → ℝ) {a : ℕ → ℝ}
    (ha : Monotone a) (h0 : 0 ≤ a 0) (h1 : a n ≤ 1) :
    (∀ᵐ x ∂(cascadeCompactLaw n b a : Measure JointArray), GramDiagonal 1 (spinArray x)) ∧
      ∀ᵐ x ∂(cascadeCompactLaw n b a : Measure JointArray), IsUltrametricArray (spinArray x) := by
  have hm := (continuous_compactScalarArray.measurable.comp ((measurable_diagonalPatch 1).comp (measurable_cascadeScalarArray n a))).aemeasurable (μ := cascadeReplicaLaw n b)
  constructor
  · apply (ae_map_iff hm ((isClosed_gramDiagonal 1).preimage continuous_spinArray).measurableSet).mpr
    filter_upwards [] with σ
    simp only [Function.comp_apply]
    rw [cascadeCompact_spin n ha h0 h1]
    exact cascade_patch_gram n ha h0 h1 σ
  · apply (ae_map_iff hm (isClosed_ultrametricArray.preimage continuous_spinArray).measurableSet).mpr
    filter_upwards [] with σ
    simp only [Function.comp_apply]
    rw [cascadeCompact_spin n ha h0 h1]
    exact cascade_patch_ultra n ha h1 σ

lemma cascadeCompact_limit_geometry {n : ℕ → ℕ} {b a : ℕ → ℕ → ℝ}
    (ha : ∀ k, Monotone (a k)) (h0 : ∀ k, 0 ≤ a k 0) (h1 : ∀ k, a k (n k) ≤ 1)
    {μ : ProbabilityMeasure JointArray}
    (hL : Tendsto (fun k => cascadeCompactLaw (n k) (b k) (a k)) atTop (𝓝 μ)) :
    (∀ᵐ x ∂(μ : Measure JointArray), GramDiagonal 1 (spinArray x)) ∧
      ∀ᵐ x ∂(μ : Measure JointArray), IsUltrametricArray (spinArray x) := by
  constructor
  · exact ae_closed_of_weak_limit hL ((isClosed_gramDiagonal 1).preimage continuous_spinArray)
      (fun k => (cascadeCompact_geometry _ _ (ha k) (h0 k) (h1 k)).1)
  · exact ae_closed_of_weak_limit hL (isClosed_ultrametricArray.preimage continuous_spinArray)
      (fun k => (cascadeCompact_geometry _ _ (ha k) (h0 k) (h1 k)).2)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

lemma cellAverage_integral_tendsto {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) (F : ℝ →ᵇ ℝ) :
    Tendsto (fun n => ∫ u, F (uniformCellAverage q n (uniformCellIndex n u)) ∂unitUniform)
      atTop (𝓝 (∫ u, F (q u) ∂unitUniform)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖F‖)
  · intro n
    exact (F.continuous.measurable.comp ((measurable_of_countable (uniformCellAverage q n)).comp
      (measurable_uniformCellIndex n))).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ (fun u => F.norm_coe_le_norm _)
  · filter_upwards [uniformCellAverage_ae_tendsto hq hb] with u hu
    exact F.continuous.continuousAt.tendsto.comp hu

lemma cascadeCompact_pair_integral (n : ℕ) {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) (F : ℝ →ᵇ ℝ) :
    (∫ x, F (spinArray x 0 1) ∂(cascadeCompactLaw n (uniformExponent n) (uniformCellAverage q n) : Measure JointArray)) =
      ∫ u, F (uniformCellAverage q n (uniformCellIndex n u)) ∂unitUniform := by
  rw [cascadeCompact_integral n (uniformExponent n) (uniformCellAverage q n)
    (F := fun x => F (spinArray x 0 1)) ((F.continuous.comp (by unfold spinArray; fun_prop)).measurable)]
  simp_rw [cascadeCompact_spin n (uniformCellAverage_monotone hq hb n) (uniformCellAverage_mem hq hb n 0).1
    (uniformCellAverage_mem hq hb n n).2]
  simp only [diagonalPatch,show (0:ℕ) ≠ 1 by omega,ite_false]
  have he := congrArg (fun μ : Measure ℝ => ∫ x, F x ∂μ) (cascade_pair_uniformIndex n (uniformCellAverage q n))
  have hmap : Measurable (fun u => uniformCellAverage q n (uniformCellIndex n u)) :=
    (measurable_of_countable (uniformCellAverage q n)).comp (measurable_uniformCellIndex n)
  have hmap2 : Measurable (fun σ => cascadeScalarArray n (uniformCellAverage q n) σ 0 1) :=
    (measurable_pi_apply 1).comp ((measurable_pi_apply 0).comp (measurable_cascadeScalarArray n (uniformCellAverage q n)))
  rw [integral_map hmap.aemeasurable
      F.continuous.aestronglyMeasurable,
    integral_map hmap2.aemeasurable
      F.continuous.aestronglyMeasurable] at he
  exact he.symm

lemma cascadeCompact_limit_pairLaw {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) {ns : ℕ → ℕ} (hns : Tendsto ns atTop atTop)
    {μ : ProbabilityMeasure JointArray}
    (hL : Tendsto (fun k => cascadeCompactLaw (ns k) (uniformExponent (ns k)) (uniformCellAverage q (ns k))) atTop (𝓝 μ)) :
    (μ : Measure JointArray).map (fun x => spinArray x 0 1) = unitUniform.map q := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  rw [integral_map (by unfold spinArray; fun_prop : Measurable (fun x : JointArray => spinArray x 0 1)).aemeasurable
      F.continuous.aestronglyMeasurable,
    integral_map hq.measurable.aemeasurable F.continuous.aestronglyMeasurable]
  apply tendsto_nhds_unique (jointArray_tendsto_integral hL (F.continuous.comp (by unfold spinArray; fun_prop)))
  simpa only [Function.comp_def,cascadeCompact_pair_integral _ hq hb F] using (cellAverage_integral_tendsto hq hb F).comp hns

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix BoundedContinuousFunction
namespace IsingPerceptron

lemma gaussianMoment_blockLaw {Ω : Type*} [MeasurableSpace Ω]
    {B : Ω → RealArray} {P : Measure Ω} (hB : Measurable B)
    (hG : ∀ᵐ x ∂P, GramDiagonal 1 (B x))
    (m : ℕ) {f : ℝ → ℝ} (_hf : Continuous f) {K : ℝ} (_hK : ∀ x, |f x| ≤ K)
    (F : Matrix (Fin m) (Fin m) ℝ →ᵇ ℝ) (hF : ∀ S, S.PosSemidef → F S = gaussianMoment m f S) :
    (∫ x, gaussianMoment m f (fun i j => B x i j) ∂P) = ∫ S, F S ∂blockLaw B P m := by
  let : MeasurableSpace (Matrix (Fin m) (Fin m) ℝ) := inferInstanceAs (MeasurableSpace (Fin m → Fin m → ℝ))
  let : BorelSpace (Matrix (Fin m) (Fin m) ℝ) := inferInstanceAs (BorelSpace (Fin m → Fin m → ℝ))
  rw [blockLaw,integral_map (measurable_arrayBlock hB m).aemeasurable F.continuous.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hG] with x hx
  exact (hF _ (hx.1 m)).symm

lemma gaussianMoment_blockLaw_congr {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {B : Ω → RealArray} {C : Ω' → RealArray} {P : Measure Ω} {Q : Measure Ω'}
    (hB : Measurable B) (hC : Measurable C)
    (hG : ∀ᵐ x ∂P, GramDiagonal 1 (B x)) (hH : ∀ᵐ x ∂Q, GramDiagonal 1 (C x))
    (m : ℕ) (hL : blockLaw B P m = blockLaw C Q m)
    {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) :
    (∫ x, gaussianMoment m f (fun i j => B x i j) ∂P) =
      ∫ x, gaussianMoment m f (fun i j => C x i j) ∂Q := by
  obtain ⟨F,hF⟩ := gaussianMoment_extension m hf hK
  rw [gaussianMoment_blockLaw hB hG m hf hK F hF,gaussianMoment_blockLaw hC hH m hf hK F hF,hL]

lemma cascadeFreshFactor_compact_moment (n : ℕ) (b a : ℕ → ℝ) (ha : Monotone a) (ha0 : 0 ≤ a 0)
    (ha1 : a n ≤ 1) {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ} (hb : ∀ x, |f x| ≤ K) (m : ℕ) :
    (∫ p, (cascadeFreshFactor n a f p)^m
      ∂(labeledCascadeLaw n b : Measure (LabeledTree n)).prod gaussianCoordinates) =
      ∫ x, gaussianMoment m f (fun i j : Fin m => spinArray x i j)
        ∂(cascadeCompactLaw n b a : Measure JointArray) := by
  rw [cascadeFreshFactor_moment n b a ha ha0 ha1 hf.measurable hb m]
  obtain ⟨F,hF⟩ := gaussianMoment_extension m hf hb
  have he : (∫ x, gaussianMoment m f (fun i j : Fin m => spinArray x i j)
      ∂(cascadeCompactLaw n b a : Measure JointArray)) =
      ∫ x, F (fun i j : Fin m => spinArray x i j) ∂(cascadeCompactLaw n b a : Measure JointArray) := by
    apply integral_congr_ae
    filter_upwards [(cascadeCompact_geometry n b ha ha0 ha1).1] with x hx
    exact (hF _ (hx.1 m)).symm
  rw [he,cascadeCompact_integral n b a (F := fun x => F (fun i j : Fin m => spinArray x i j))
    (F.continuous.comp (by unfold spinArray; fun_prop)).measurable]
  apply integral_congr_ae
  filter_upwards [] with σ
  rw [cascadeCompact_spin n ha ha0 ha1]
  exact (hF _ ((cascade_patch_gram n ha ha0 ha1 σ).1 m)).symm

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

 

theorem cascadeFresh_moments_tendsto {q : ℝ → ℝ} (hq : Monotone q)
    (hb : ∀ u, q u ∈ Icc (0:ℝ) 1) (μ : ProbabilityMeasure JointArray)
    (hGG : HasGhirlandaGuerra spinArray (μ : Measure JointArray))
    (hG : ∀ᵐ x ∂(μ : Measure JointArray), GramDiagonal 1 (spinArray x))
    (hU : ∀ᵐ x ∂(μ : Measure JointArray), IsUltrametricArray (spinArray x))
    (hp : (μ : Measure JointArray).map (fun x => spinArray x 0 1) = unitUniform.map q)
    {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) (m : ℕ) :
    Tendsto (fun n => ∫ x, (cascadeFreshFactor n (uniformCellAverage q n) f x)^m
      ∂(labeledCascadeLaw n (uniformExponent n) : Measure (LabeledTree n)).prod gaussianCoordinates)
      atTop (𝓝 (∫ x, gaussianMoment m f (fun i j => spinArray x i j) ∂(μ : Measure JointArray))) := by
  simp_rw [cascadeFreshFactor_compact_moment _ _ _ (uniformCellAverage_monotone hq hb _)
    (uniformCellAverage_mem hq hb _ 0).1 (uniformCellAverage_mem hq hb _ _).2 hf hK m]
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ν,ms,hms,hν⟩ := jointArrayLaw_subsequence
    (fun k => cascadeCompactLaw (ns k) (uniformExponent (ns k)) (uniformCellAverage q (ns k)))
  have hν' : Tendsto (fun k => cascadeCompactLaw (ns (ms k)) (uniformExponent (ns (ms k)))
      (uniformCellAverage q (ns (ms k)))) atTop (𝓝 ν) := hν
  have hgeom := cascadeCompact_limit_geometry
    (fun k => uniformCellAverage_monotone hq hb (ns (ms k)))
    (fun k => (uniformCellAverage_mem hq hb (ns (ms k)) 0).1)
    (fun k => (uniformCellAverage_mem hq hb (ns (ms k)) (ns (ms k))).2) hν'
  have hGGν : HasGhirlandaGuerra spinArray (ν : Measure JointArray) :=
    (cascadeCompact_limit_GG (fun k => uniformExponent_cascade (ns (ms k))) hν').real_map
      (f := fun x => x.1.1) (by fun_prop)
  have hpair := cascadeCompact_limit_pairLaw hq hb (hns.comp hms.tendsto_atTop) hν'
  have hblock := gg_blockLaw_unique continuous_spinArray.measurable continuous_spinArray.measurable
    hGGν hGG (hgeom.1.mono (fun _ h => h.symm)) (hG.mono (fun _ h => h.symm))
    hgeom.2 hU (hgeom.1.mono (fun _ h => h.2)) (hG.mono (fun _ h => h.2)) (hpair.trans hp.symm)
  have he := gaussianMoment_blockLaw_congr continuous_spinArray.measurable continuous_spinArray.measurable
    hgeom.1 hG m (hblock m) hf hK
  refine ⟨ms,?_⟩
  rw [← he]
  exact jointArray_tendsto_gaussianMoment hν'
    (fun k => (cascadeCompact_geometry _ _ (uniformCellAverage_monotone hq hb _)
      (uniformCellAverage_mem hq hb _ 0).1 (uniformCellAverage_mem hq hb _ _).2).1)
    hgeom.1 m hf hK

end IsingPerceptron

end

end OAI
