import OAI.Analysis.RotationWeights.MeasurableWeight

namespace OAI

noncomputable section

namespace CircleSampling

universe uX uY uι

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical

section
open CircleModel Set Filter MeasureTheory
open scoped Topology BigOperators

def modelAngle : CircleModel.CircleX := (parameterAngle : CircleModel.CircleX)
def modelGood : Set CircleModel.CircleX := CircleModel.good modelFrequency modelAngle
def modelF (k : ℤ) : CircleModel.CircleX → ℝ := CircleModel.cocycle modelFrequency modelAngle coordinateDrop k
def modelWeight : CircleModel.CircleX → ℝ := modelF 1

lemma model_beta (i : ℕ) : CircleModel.beta modelFrequency modelAngle i=coordinatePhase i := by
  unfold CircleModel.beta CircleModel.Xi modelAngle coordinatePhase
  rw [←AddCircle.coe_nsmul, nsmul_eq_mul,CircleModel.repr_mk]
lemma model_beta_sum : Summable (CircleModel.beta modelFrequency modelAngle) := by
  have he : CircleModel.beta modelFrequency modelAngle = coordinatePhase := funext model_beta
  rw [he]
  exact summable_coordinatePhase
lemma model_good_ae : ∀ᵐ x : CircleModel.CircleX, x∈modelGood :=
  CircleModel.ae_good (fun i => (frequency_pos (i+1)).ne') modelAngle model_beta_sum
lemma modelGood_measurable : MeasurableSet modelGood := CircleModel.measurableSet_good _ _
lemma modelF_measurable (k : ℤ) : Measurable (modelF k) := CircleModel.measurable_cocycle _ _ _ _
lemma modelF_pos (k : ℤ) (x : CircleModel.CircleX) : 0 < modelF k x := CircleModel.cocycle_pos _ _ _ _ _
lemma modelF_zero (x : CircleModel.CircleX) : modelF 0 x=1 := CircleModel.cocycle_zero _ _ _ _
lemma modelF_antitone (x : CircleModel.CircleX) : Antitone (fun k => modelF k x) :=
  CircleModel.cocycle_antitone _ _ _ (fun i => dropSize_nonneg (coordinateBlock i)) x
lemma modelWeight_bounds (x : CircleModel.CircleX) : 0 < modelWeight x ∧ modelWeight x≤1 := by
  exact ⟨modelF_pos 1 x,by simpa only [modelWeight, modelF_zero] using modelF_antitone x (show (0:ℤ)≤1 by norm_num)⟩
lemma modelF_add (k n : ℤ) (x : CircleModel.CircleX) :
    modelF (k+n) x=modelF n (CircleModel.shift modelAngle k x)*modelF k x :=
  CircleModel.cocycle_add _ _ _ _ _ _
lemma modelGood_shift (k : ℤ) (x : CircleModel.CircleX) : CircleModel.shift modelAngle k x∈modelGood ↔ x∈modelGood :=
  CircleModel.good_shift _ _ _ _
lemma modelF_ratio_ordered {x y : CircleModel.CircleX} (hx : x∈modelGood) (hy : y∈modelGood)
    (hxy : ∀ i,CircleModel.Xi modelFrequency i x≤CircleModel.Xi modelFrequency i y) (k : ℤ) :
    modelF k y/modelF k x≤1 :=
  CircleModel.cocycle_ratio_ordered coordinateDrop (fun i => dropSize_nonneg (coordinateBlock i)) k hx hy hxy
lemma modelF_ratio_tail {x y : CircleModel.CircleX} (D : ℕ) (hx : x∈modelGood) (hy : y∈modelGood)
    (hxy : ∀ i,D ≤ i → CircleModel.Xi modelFrequency i x≤CircleModel.Xi modelFrequency i y) (k : ℤ) :
    modelF k y/modelF k x≤Real.exp (∑ i∈Finset.range D,coordinateDrop i) :=
  CircleModel.cocycle_ratio_tail_bound coordinateDrop (fun i => dropSize_nonneg (coordinateBlock i)) D k hx hy hxy

lemma phase_orbit (i : ℕ) (n : ℤ) :
    modelFrequency i • (n•modelAngle)=((n*coordinatePhase i:ℝ):CircleModel.CircleX) := by
  rw [smul_comm,←model_beta]
  unfold CircleModel.beta CircleModel.Xi
  rw [←zsmul_eq_mul,AddCircle.coe_zsmul,CircleModel.repr_coe]

lemma model_coordinate_shift (i : ℕ) (n : ℤ) (x : CircleModel.CircleX) :
    CircleModel.Xi modelFrequency i (CircleModel.shift modelAngle n x)=
      Int.fract (CircleModel.Xi modelFrequency i x+n*coordinatePhase i) := by
  rw [CircleModel.Xi_shift,model_beta]
end

open MeasureTheory Set Filter
open scoped ENNReal Topology
section

def weightedMeasure {X : Type uX} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (f x))
lemma weightedMeasure_finite {X : Type uX} [MeasurableSpace X] (μ : Measure X) {f : X → ℝ}
    (hf : Integrable f μ) (hn : ∀ x,0≤f x) : IsFiniteMeasure (weightedMeasure μ f) := by
  apply isFiniteMeasure_withDensity
  rw [←ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ hn)]
  exact ENNReal.ofReal_ne_top
lemma weightedMeasure_real_apply {X : Type uX} [MeasurableSpace X] (μ : Measure X) {f : X → ℝ}
    (hf : Integrable f μ) (hn : ∀ x,0≤f x) {A : Set X} (hA : MeasurableSet A) :
    (weightedMeasure μ f).real A=∫ x in A,f x ∂μ := by
  rw [Measure.real,weightedMeasure,withDensity_apply _ hA,
    ←ofReal_integral_eq_lintegral_ofReal hf.restrict (ae_of_all _ hn),ENNReal.toReal_ofReal]
  exact integral_nonneg hn
lemma weightedMeasure_integral {X : Type uX} [MeasurableSpace X] (μ : Measure X) {f : X → ℝ}
    (hf : Measurable f) (hn : ∀ x,0≤f x) (g : X → ℝ) :
    (∫ x,g x ∂weightedMeasure μ f)=∫ x,f x*g x ∂μ := by
  rw [weightedMeasure,integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hn _),smul_eq_mul]

lemma weightedMeasure_map_equiv {X : Type uX} [MeasurableSpace X] (μ : Measure X)
    (T : X ≃ᵐ X) (hT : MeasurePreserving T μ μ) (f : X → ℝ) (hf : Measurable f) :
    Measure.map T (weightedMeasure μ f)=weightedMeasure μ (fun y => f (T.symm y)) := by
  ext A hA
  rw [Measure.map_apply T.measurable hA,weightedMeasure,weightedMeasure,
    withDensity_apply _ (T.measurable hA),withDensity_apply _ hA]
  have hgm : Measurable (A.indicator (fun y => ENNReal.ofReal (f (T.symm y)))) :=
    (hf.ennreal_ofReal.comp T.symm.measurable).indicator hA
  rw [←lintegral_indicator (T.measurable hA),←lintegral_indicator hA]
  calc
    _ = ∫⁻ x, A.indicator (fun y => ENNReal.ofReal (f (T.symm y))) (T x) ∂μ := by
      apply lintegral_congr
      intro x
      by_cases hx : T x∈A <;> simp [hx]
    _ = ∫⁻ y, A.indicator (fun y => ENNReal.ofReal (f (T.symm y))) y ∂Measure.map T μ :=
      (lintegral_map' hgm.aemeasurable T.measurable.aemeasurable).symm
    _ = _ := by rw [hT.map_eq]

def weightedGraph {X : Type uX} {Y : Type uY} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (f : X → ℝ) (T : X → Y) : Measure (X×Y) :=
  Measure.map (fun x => (x,T x)) (weightedMeasure μ f)
lemma weightedGraph_fst {X : Type uX} {Y : Type uY} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (f : X → ℝ) (T : X → Y) (hT : Measurable T) :
    Measure.map Prod.fst (weightedGraph μ f T)=weightedMeasure μ f := by
  rw [weightedGraph,Measure.map_map measurable_fst (show Measurable (fun x => (x,T x)) from measurable_id.prodMk hT)]
  exact Measure.map_id
lemma weightedGraph_snd {X : Type uX} [MeasurableSpace X] (μ : Measure X)
    (T : X ≃ᵐ X) (hT : MeasurePreserving T μ μ) (f : X → ℝ) (hf : Measurable f) :
    Measure.map Prod.snd (weightedGraph μ f T)=weightedMeasure μ (fun y => f (T.symm y)) := by
  rw [weightedGraph,Measure.map_map measurable_snd (show Measurable (fun x => (x,T x)) from measurable_id.prodMk T.measurable)]
  exact weightedMeasure_map_equiv μ T hT f hf

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

lemma weightedMeasure_add {X : Type uX} [MeasurableSpace X] (μ : Measure X) {f g : X → ℝ}
    (hf : Measurable f) (hfn : ∀ x,0≤f x) (hgn : ∀ x,0≤g x) :
    weightedMeasure μ (fun x => f x+g x)=weightedMeasure μ f+weightedMeasure μ g := by
  unfold weightedMeasure
  simp only [ENNReal.ofReal_add (hfn _) (hgn _)]
  exact withDensity_add_left hf.ennreal_ofReal _
lemma weightedMeasure_mul {X : Type uX} [MeasurableSpace X] (μ : Measure X) (f : X → ℝ)
    (hf : Measurable f) {c : ℝ} (hc : 0≤c) :
    weightedMeasure μ (fun x => c*f x)=ENNReal.ofReal c • weightedMeasure μ f := by
  unfold weightedMeasure
  simp only [ENNReal.ofReal_mul hc]
  exact withDensity_smul _ hf.ennreal_ofReal
lemma weightedMeasure_sum {X : Type uX} {ι : Type uι} [MeasurableSpace X] (μ : Measure X)
    (s : Finset ι) (f : ι → X → ℝ) (hf : ∀ i∈s,Measurable (f i))
    (hn : ∀ i∈s,∀ x,0≤f i x) :
    weightedMeasure μ (fun x => ∑ i∈s,f i x)=∑ i∈s,weightedMeasure μ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [weightedMeasure]
  | @insert i s hi ih =>
    simp only [Finset.mem_insert] at hf hn
    simp only [Finset.sum_insert hi]
    rw [weightedMeasure_add μ (hf i (Or.inl rfl)) (hn i (Or.inl rfl))
      (fun x => Finset.sum_nonneg (fun k hk => hn k (Or.inr hk) x))]
    rw [ih (fun k hk => hf k (Or.inr hk)) (fun k hk => hn k (Or.inr hk))]

lemma map_finsetSum {X : Type uX} {Y : Type uY} {ι : Type uι} [MeasurableSpace X] [MeasurableSpace Y]
    (s : Finset ι) (μ : ι → Measure X) {T : X → Y} (hT : Measurable T) :
    Measure.map T (∑ i∈s,μ i)=∑ i∈s,Measure.map T (μ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi,Measure.map_add _ _ hT,ih]

def finiteGraphAverage {X : Type uX} {ι : Type uι} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (w : ι → X → ℝ) (T : ι → X → X) : Measure (X×X) :=
  ENNReal.ofReal ((Fintype.card ι:ℝ)⁻¹) • ∑ i,weightedGraph μ (w i) (T i)
def finiteAverage {X : Type uX} {ι : Type uι} [Fintype ι] (w : ι → X → ℝ) (x : X) : ℝ :=
  (Fintype.card ι:ℝ)⁻¹ * ∑ i,w i x

lemma finiteGraphAverage_fst {X : Type uX} {ι : Type uι} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (w : ι → X → ℝ) (T : ι → X → X)
    (hw : ∀ i,Measurable (w i)) (hn : ∀ i x,0≤w i x) (hT : ∀ i,Measurable (T i)) :
    Measure.map Prod.fst (finiteGraphAverage μ w T)=weightedMeasure μ (finiteAverage w) := by
  rw [finiteGraphAverage,Measure.map_smul _ measurable_fst.aemeasurable,
    map_finsetSum _ _ measurable_fst]
  simp_rw [weightedGraph_fst μ _ _ (hT _)]
  change _ = weightedMeasure μ (fun x => (Fintype.card ι:ℝ)⁻¹ * ∑ i, w i x)
  rw [weightedMeasure_mul _ _ (by fun_prop) (by positivity),
    weightedMeasure_sum _ _ _ (fun i _ => hw i) (fun i _ => hn i)]
lemma finiteGraphAverage_snd {X : Type uX} {ι : Type uι} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (T : ι → X ≃ᵐ X) (hT : ∀ i,MeasurePreserving (T i) μ μ)
    (w : ι → X → ℝ) (hw : ∀ i,Measurable (w i)) (hn : ∀ i x,0≤w i x) :
    Measure.map Prod.snd (finiteGraphAverage μ w (fun i => T i))=
      weightedMeasure μ (finiteAverage (fun i y => w i ((T i).symm y))) := by
  rw [finiteGraphAverage,Measure.map_smul _ measurable_snd.aemeasurable,
    map_finsetSum _ _ measurable_snd]
  simp_rw [weightedGraph_snd μ _ (hT _) _ (hw _)]
  change _ = weightedMeasure μ (fun y => (Fintype.card ι:ℝ)⁻¹ * ∑ i, w i ((T i).symm y))
  rw [weightedMeasure_mul _ _ (by fun_prop) (by positivity),
    weightedMeasure_sum μ Finset.univ (fun i y => w i ((T i).symm y)) (fun i _ => (hw i).comp (T i).symm.measurable) (fun i _ x => hn i _)]

lemma finiteGraphAverage_finite {X : Type uX} {ι : Type uι} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (w : ι → X → ℝ) (T : ι → X → X)
    (hw : ∀ i,Integrable (w i) μ) (hn : ∀ i x,0≤w i x) :
    IsFiniteMeasure (finiteGraphAverage μ w T) := by
  have (i : ι) : IsFiniteMeasure (weightedMeasure μ (w i)) := weightedMeasure_finite μ (hw i) (hn i)
  have (i : ι) : IsFiniteMeasure (weightedGraph μ (w i) (T i)) := by unfold weightedGraph; infer_instance
  unfold finiteGraphAverage
  exact Measure.smul_finite _ ENNReal.ofReal_ne_top

lemma finiteGraphAverage_ae {X : Type uX} {ι : Type uι} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (w : ι → X → ℝ) (T : ι → X → X)
    (hw : ∀ i,Measurable (w i)) (hT : ∀ i,Measurable (T i))
    (P : X×X → Prop) (hP : MeasurableSet {z | P z})
    (hp : ∀ i,∀ᵐ x ∂μ,w i x≠0 → P (x,T i x)) :
    ∀ᵐ z ∂finiteGraphAverage μ w T,P z := by
  unfold finiteGraphAverage
  apply Measure.ae_smul_measure
  apply ae_finsetSum_measure_iff.mpr
  intro i _
  rw [weightedGraph]
  apply (ae_map_iff (show Measurable (fun x => (x,T i x)) from measurable_id.prodMk (hT i)).aemeasurable hP).mpr
  rw [weightedMeasure,ae_withDensity_iff (hw i).ennreal_ofReal]
  filter_upwards [hp i] with x hx hne
  apply hx
  intro hz
  exact hne (by simp [hz])
end

section
open ContinuousCircleWeight.Sampling MeasureTheory Set CircleModel
open scoped BigOperators

lemma stageEll_pos (j : ℕ) : 0 < scaleEll (blockLength j) :=
  Real.rpow_pos_of_pos (Nat.cast_pos.mpr (scaleStep j).mpos) _
lemma stageEll_lt (j : ℕ) : scaleEll (blockLength j) < 1 := by
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast (by have := blockLength_ge j; omega : 1 < blockLength j)
  · norm_num
lemma stageAlpha_pos (j : ℕ) : 0 < scaleAlpha (blockLength j) :=
  Real.rpow_pos_of_pos (Nat.cast_pos.mpr (scaleStep j).mpos) _

def stageFactor (positive : Bool) (j : ℕ) (n : ℤ) (i : Fin (blockLength j)) (x : CircleModel.CircleX) : ℝ :=
  orientedWeight positive (scaleEll (blockLength j)) (scaleAlpha (blockLength j))
    (((scaleStep j).q (i+1):ℤ) • x)
    (((n:ℝ)*Int.fract (((scaleStep j).q (i+1):ℝ)*parameterAngle):ℝ):CircleModel.CircleX)
def stageWeight (positive : Bool) (j : ℕ) (n : ℤ) (x : CircleModel.CircleX) : ℝ :=
  ∏ i : Fin (blockLength j), stageFactor positive j n i x

lemma stageFactor_measurable (positive : Bool) (j : ℕ) (n : ℤ) (i : Fin (blockLength j)) :
    Measurable (stageFactor positive j n i) :=
  (measurable_orientedWeight _ _ _).comp ((continuous_id.zsmul _).measurable.prodMk measurable_const)
lemma stageFactor_bounds (positive : Bool) (j : ℕ) (n : ℤ) (i : Fin (blockLength j)) (x : CircleModel.CircleX) :
    0 ≤ stageFactor positive j n i x ∧
      stageFactor positive j n i x ≤ 1/(scaleEll (blockLength j)*scaleAlpha (blockLength j)) :=
  orientedWeight_bounds positive (stageEll_pos j) (stageAlpha_pos j) _ _
lemma stageWeight_measurable (positive : Bool) (j : ℕ) (n : ℤ) : Measurable (stageWeight positive j n) := by
  unfold stageWeight
  exact Finset.measurable_prod _ (fun i _ => stageFactor_measurable _ _ _ i)
lemma stageWeight_bounds (positive : Bool) (j : ℕ) (n : ℤ) (x : CircleModel.CircleX) :
    0 ≤ stageWeight positive j n x ∧ stageWeight positive j n x ≤
      (1/(scaleEll (blockLength j)*scaleAlpha (blockLength j)))^(blockLength j) := by
  constructor
  · exact Finset.prod_nonneg (fun i _ => (stageFactor_bounds positive j n i x).1)
  · have h := Finset.prod_le_prod₀ (s:=Finset.univ) (fun i _ => (stageFactor_bounds positive j n i x).1)
      (fun i _ => (stageFactor_bounds positive j n i x).2)
    simpa [stageWeight] using h
lemma stageWeight_memLp (positive : Bool) (j : ℕ) (n : ℤ) : MemLp (stageWeight positive j n) 2 := by
  apply MemLp.of_bound (stageWeight_measurable positive j n).aestronglyMeasurable
    ((1/(scaleEll (blockLength j)*scaleAlpha (blockLength j)))^(blockLength j))
  exact ae_of_all _ (fun x => by rw [Real.norm_of_nonneg (stageWeight_bounds positive j n x).1]; exact (stageWeight_bounds positive j n x).2)

lemma stage_frequency (j : ℕ) (i : Fin (blockLength j)) :
    modelFrequency (blocks.equiv ⟨j,i⟩)=(scaleStep j).q (i+1) := by
  change frequency (blockEnd j+i.val+1)=_
  rw [show blockEnd j+i.val+1=blockEnd j+(i.val+1) by omega,frequency_block j (by omega)]
lemma stage_phase (j : ℕ) (i : Fin (blockLength j)) :
    coordinatePhase (blocks.equiv ⟨j,i⟩) = Int.fract (((scaleStep j).q (i+1):ℝ)*parameterAngle) := by
  unfold coordinatePhase
  rw [stage_frequency]
lemma stageFactor_model (positive : Bool) (j : ℕ) (n : ℤ) (i : Fin (blockLength j)) (x : CircleModel.CircleX) :
    stageFactor positive j n i x = orientedWeight positive (scaleEll (blockLength j)) (scaleAlpha (blockLength j))
      (modelFrequency (blocks.equiv ⟨j,i⟩) • x) (modelFrequency (blocks.equiv ⟨j,i⟩) • (n • modelAngle)) := by
  rw [phase_orbit,stage_phase,stage_frequency]
  rfl
lemma stageWeight_negative (j : ℕ) (n : ℤ) (x : CircleModel.CircleX) :
    stageWeight false j n x = stageWeight true j n (CircleModel.shift modelAngle (-n) x) := by
  apply Finset.prod_congr rfl
  intro i _
  simp only [stageFactor_model,orientedWeight,Bool.false_eq_true,↓reduceIte,uNeg,CircleModel.shift,neg_smul]
  rw [smul_add,smul_neg,sub_eq_add_neg]

instance stageSample_nonempty (j : ℕ) (t : Fin ((scaleState j).1.q (scaleState j).1.d)) :
    Nonempty ((scaleStep j).samples t) := (scaleStep j).samples_nonempty t |>.coe_sort

def stageDensity (positive : Bool) (j : ℕ) (t : Fin ((scaleState j).1.q (scaleState j).1.d)) : CircleModel.CircleX → ℝ :=
  finiteAverage (fun n : (scaleStep j).samples t => stageWeight positive j n.val)
lemma stageDensity_measurable (positive : Bool) (j : ℕ) (t : Fin ((scaleState j).1.q (scaleState j).1.d)) :
    Measurable (stageDensity positive j t) := by
  unfold stageDensity finiteAverage
  exact (Finset.measurable_sum _ (fun n _ => stageWeight_measurable positive j n.val)).const_mul _
lemma stageDensity_nonneg (positive : Bool) (j : ℕ) (t : Fin ((scaleState j).1.q (scaleState j).1.d)) (x : CircleModel.CircleX) :
    0 ≤ stageDensity positive j t x := by
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg (fun n _ => (stageWeight_bounds positive j n.val x).1)
lemma stageDensity_memLp (positive : Bool) (j : ℕ) (t : Fin ((scaleState j).1.q (scaleState j).1.d)) :
    MemLp (stageDensity positive j t) 2 := by
  have h : MemLp (fun x => ∑ n : (scaleStep j).samples t, stageWeight positive j n.val x) 2 :=
    memLp_finsetSum Finset.univ (fun n _ => stageWeight_memLp positive j n.val)
  exact h.const_mul _
lemma stageDensity_energy (positive : Bool) (j : ℕ) (t : Fin ((scaleState j).1.q (scaleState j).1.d)) :
    (∫ x, (stageDensity positive j t x-1)^2) < 1/((j:ℝ)+1)^2 := by
  exact (scaleStep j).energies parameterAngle (parameterAngle_spec.2.2.2 j) t positive
end

open CircleModel Set MeasureTheory
open scoped BigOperators

def sampleBound (j : ℕ) : ℝ := (blockLength j:ℝ)^((7:ℝ)/10*blockLength j)
def oldGraphBad (j : ℕ) : Set CircleX :=
  ⋃ i : Fin (blockEnd j), {x | 1-(modelFrequency i:ℝ)*gridTolerance j (scaleState j).1  ≤  CircleModel.Xi modelFrequency i x}
def tailGraphBad (j : ℕ) : Set CircleX :=
  ⋃ i : {i : ℕ // blockEnd (j+1)  ≤  i}, {x | 1-sampleBound j*coordinatePhase i  ≤  CircleModel.Xi modelFrequency i x}
def graphBad (j : ℕ) : Set CircleX := oldGraphBad j ∪ tailGraphBad j
lemma graphBad_measurable (j : ℕ) : MeasurableSet (graphBad j) :=
  (MeasurableSet.iUnion (fun _ => measurableSet_le measurable_const (CircleModel.measurable_Xi _ _))).union
    (MeasurableSet.iUnion (fun _ => measurableSet_le measurable_const (CircleModel.measurable_Xi _ _)))
lemma sampleBound_pos (j : ℕ) : 0  <  sampleBound j :=
  Real.rpow_pos_of_pos (Nat.cast_pos.mpr (scaleStep j).mpos) _
lemma sample_bound (j : ℕ) {t : Fin ((scaleState j).1.q (scaleState j).1.d)} {n : ℤ}
    (hn : n∈(scaleStep j).samples t) : 0  <  n ∧ (n:ℝ) ≤ sampleBound j := by
  have h := (scaleStep j).samples_bounds t n hn
  refine ⟨?_,h.2⟩
  have hh : (0:ℝ) < n := lt_of_lt_of_le (half_pos (sampleBound_pos j)) h.1
  exact_mod_cast hh
lemma coordinate_add_nowrap (q : ℕ) (x y : CircleX) (t : ℝ)
    (he : q•y=(t:CircleX)) (ht : 0 ≤ t)
    (hu : CircleModel.repr (q•x)+t < 1) :
    CircleModel.repr (q • (x+y))=CircleModel.repr (q•x)+t := by
  have he' : q • (x+y)=((CircleModel.repr (q • x)+t:ℝ):CircleX) := by
    rw [nsmul_add,he,AddCircle.coe_add,CircleModel.repr_coe]
  rw [he',CircleModel.repr_mk]
  exact Int.fract_eq_self.mpr ⟨add_nonneg (CircleModel.repr_mem _).1 ht,hu⟩
lemma positive_weight_order {ℓ α : ℝ} (hℓ : ℓ < 1) (hα : 0 < α) (s t : CircleX)
    (hw : uPos ℓ α s t ≠ 0) : CircleModel.repr s  ≤  CircleModel.repr (s+t) := by
  have hh : α ≤ delta (repr s) ∧ 0 < repr t ∧ repr t < ℓ*delta (repr s) := by
    by_cases hh : α ≤ delta (repr s) ∧ 0 < repr t ∧ repr t < ℓ*delta (repr s)
    · exact hh
    · exact False.elim (hw (by simp only [uPos,weight,ite_eq_right hh]))
  have hd : 0 < delta (repr s) := lt_of_lt_of_le hα hh.1
  have hst : repr s+repr t < 1 := by
    have : ℓ*delta (repr s) < delta (repr s) := (mul_lt_iff_lt_one_left hd).mpr hℓ
    have := min_le_right (repr s) (1-repr s)
    unfold delta at *
    linarith [hh.2.2]
  have he : CircleModel.repr (s+t)=CircleModel.repr s+CircleModel.repr t := by
    simpa only [one_nsmul] using coordinate_add_nowrap 1 s t (CircleModel.repr t)
      (by simpa using (CircleModel.repr_coe t).symm) hh.2.1.le (by simpa only [one_nsmul,repr,CircleModel.repr] using hst)
  rw [he]
  exact le_add_of_nonneg_right hh.2.1.le
lemma stageWeight_order (j : ℕ) (n : ℤ) (x : CircleX)
    (hw : stageWeight true j n x ≠ 0) (i : Fin (blockLength j)) :
    CircleModel.Xi modelFrequency (blocks.equiv ⟨j,i⟩) x  ≤
      CircleModel.Xi modelFrequency (blocks.equiv ⟨j,i⟩) (CircleModel.shift modelAngle n x) := by
  have hfactor : stageFactor true j n i x ≠ 0 := (Finset.prod_ne_zero_iff.mp hw) i (Finset.mem_univ _)
  rw [stageFactor_model] at hfactor
  change uPos _ _ _ _ ≠ 0 at hfactor
  have h := positive_weight_order (stageEll_lt j) (stageAlpha_pos j) _ _ hfactor
  simpa only [CircleModel.Xi,CircleModel.shift,nsmul_add] using h

lemma restricted_orbit_order (j D : ℕ) (h : CircleX)
    (hperiod : ∀ i, D ≤ i  →  modelFrequency i•h=0)
    (t : Fin ((scaleState j).1.q (scaleState j).1.d))
    (ht : gridPoint (scaleState j).1 t=h)
    (n : ℤ) (hn : n∈(scaleStep j).samples t) (x : CircleX)
    (hx : x∉graphBad j) (hw : stageWeight true j n x ≠ 0) :
    ∀ i, D ≤ i  →  CircleModel.Xi modelFrequency i x ≤
      CircleModel.Xi modelFrequency i (CircleModel.shift modelAngle n x) := by
  have ho := (scaleStep j).orbits parameterAngle (parameterAngle_spec.2.2.2 j) t n hn
  rw [ht] at ho
  obtain ⟨δ,hδ,hδeq⟩ := ho
  have hδn : n•modelAngle=h+(δ:CircleX) := by
    change (δ:CircleX)=n•modelAngle-h at hδeq
    exact (sub_eq_iff_eq_add.mp hδeq.symm).trans (add_comm _ _)
  intro i hi
  by_cases hold : i < blockEnd j
  · have hbad : CircleModel.Xi modelFrequency i x < 1-(modelFrequency i:ℝ)*gridTolerance j (scaleState j).1 := by
      by_contra! hh
      exact hx (Or.inl (mem_iUnion.mpr ⟨⟨i,hold⟩,hh⟩))
    have he : modelFrequency i•(n•modelAngle)=(((modelFrequency i:ℝ)*δ:ℝ):CircleX) := by
      rw [hδn,nsmul_add,hperiod i hi,zero_add,←AddCircle.coe_nsmul,nsmul_eq_mul]
    have hval := coordinate_add_nowrap (modelFrequency i) x (n•modelAngle)
      ((modelFrequency i:ℝ)*δ) he (mul_nonneg (Nat.cast_nonneg _) hδ.1.le)
      (by change CircleModel.Xi modelFrequency i x+_ < 1
          have hdiff : (modelFrequency i:ℝ)*δ < (modelFrequency i:ℝ)*gridTolerance j (scaleState j).1 :=
            mul_lt_mul_of_pos_left hδ.2 (Nat.cast_pos.mpr (frequency_pos (i+1)))
          linarith)
    change CircleModel.Xi modelFrequency i x  ≤  CircleModel.repr (modelFrequency i•(x+n•modelAngle))
    rw [hval]
    exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hδ.1.le)
  · by_cases htail : blockEnd (j+1) ≤ i
    · have hbad : CircleModel.Xi modelFrequency i x < 1-sampleBound j*coordinatePhase i := by
        by_contra! hh
        exact hx (Or.inr (mem_iUnion.mpr ⟨⟨i,htail⟩,hh⟩))
      have hn0 : 0 ≤ (n:ℝ) := by exact_mod_cast (sample_bound j hn).1.le
      have hval := coordinate_add_nowrap (modelFrequency i) x (n•modelAngle)
        ((n:ℝ)*coordinatePhase i) (phase_orbit i n)
        (mul_nonneg hn0 (coordinatePhase_pos i).le)
        (by change CircleModel.Xi modelFrequency i x+_ < 1
            nlinarith [mul_le_mul_of_nonneg_right (sample_bound j hn).2 (coordinatePhase_pos i).le])
      change CircleModel.Xi modelFrequency i x  ≤  CircleModel.repr (modelFrequency i•(x+n•modelAngle))
      rw [hval]
      exact le_add_of_nonneg_right (mul_nonneg hn0 (coordinatePhase_pos i).le)
    · have hem : blockEnd (j+1)=blockEnd j+blockLength j := rfl
      let k : Fin (blockLength j) := ⟨i-blockEnd j,by omega⟩
      have he : blocks.equiv ⟨j,k⟩=i := by change blockEnd j+(i-blockEnd j)=i; omega
      simpa only [he] using stageWeight_order j n x hw k


end CircleSampling

end

end OAI
