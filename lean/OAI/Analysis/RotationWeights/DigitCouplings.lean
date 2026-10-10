import OAI.Analysis.RotationWeights.ProjectionIdentity

namespace OAI

noncomputable section

namespace CircleCoupling

universe uκ uD

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
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace

open MeasureTheory Set
open scoped ENNReal BigOperators Classical
section

instance labelMeasurableSpace {κ : Type uκ} : MeasurableSpace (Option κ) := ⊤
instance labelMeasurableSingleton {κ : Type uκ} : MeasurableSingletonClass (Option κ) := ⟨by intro a; trivial⟩

def uniformOn {D : Type uD} [MeasurableSpace D] (S : Finset D) (hs : S.Nonempty) : Measure D :=
  (PMF.uniformOfFinset S hs).toMeasure
instance {D : Type uD} [MeasurableSpace D] (S : Finset D) (hs : S.Nonempty) :
    IsProbabilityMeasure (uniformOn S hs) := by unfold uniformOn; infer_instance

lemma uniformOn_singleton {D : Type uD} [MeasurableSpace D] [MeasurableSingletonClass D]
    (S : Finset D) (hs : S.Nonempty) (d : D) :
    uniformOn S hs {d} = if d ∈ S then (S.card : ℝ≥0∞)⁻¹ else 0 := by
  classical
  simp [uniformOn, PMF.toMeasure_apply_singleton, PMF.uniformOfFinset_apply]

def labelled {κ : Type uκ} {D : Type uD} [MeasurableSpace κ] [MeasurableSpace D]
    (a : Option κ) (μ : Measure (D × D)) : Measure (Option κ × (D × D)) :=
  Measure.map (fun z => (a,z)) μ

def mixture {κ : Type uκ} {D : Type uD} [Fintype κ] [MeasurableSpace κ] [MeasurableSpace D]
    (p : κ → ℝ≥0∞) (p₀ : ℝ≥0∞) (μ₀ : Measure (D × D))
    (μ : κ → Measure (D × D)) : Measure (Option κ × (D × D)) :=
  p₀ • labelled none μ₀ + ∑ a, p a • labelled (some a) (μ a)

lemma labelled_univ {κ : Type uκ} {D : Type uD} [MeasurableSpace κ] [MeasurableSpace D]
    (a : Option κ) (μ : Measure (D × D)) : labelled a μ univ = μ univ := by
  rw [labelled, Measure.map_apply (show Measurable (fun z : D × D => (a,z)) from measurable_const.prodMk measurable_id) MeasurableSet.univ]
  simp

lemma mixture_probability {κ : Type uκ} {D : Type uD} [Fintype κ] [MeasurableSpace κ] [MeasurableSpace D]
    (p : κ → ℝ≥0∞) (p₀ : ℝ≥0∞) (μ₀ : Measure (D × D))
    (μ : κ → Measure (D × D)) [IsProbabilityMeasure μ₀] [∀ a, IsProbabilityMeasure (μ a)]
    (hp : p₀ + ∑ a, p a = 1) : IsProbabilityMeasure (mixture p p₀ μ₀ μ) := by
  constructor
  simpa [mixture, Measure.add_apply, Measure.sum_apply, Measure.smul_apply, labelled_univ,
    measure_univ] using hp

lemma labelled_fiber {κ : Type uκ} {D : Type uD} [MeasurableSpace κ] [MeasurableSpace D]
    [MeasurableSingletonClass D] (a : Option κ) (μ : Measure (D × D))
    (f : D × D → D) (hf : Measurable f) (d : D) :
    labelled a μ {ω | f ω.2 = d} = μ (f ⁻¹' {d}) := by
  change labelled a μ ((fun ω => f ω.2) ⁻¹' {d}) = _
  unfold labelled
  exact Measure.map_apply (show Measurable (fun z : D × D => (a,z)) from
    measurable_const.prodMk measurable_id) ((hf.comp measurable_snd) (measurableSet_singleton d))

lemma labelled_fiber_label {κ : Type uκ} {D : Type uD} [MeasurableSpace κ] [MeasurableSpace D]
    [MeasurableSingletonClass κ] [MeasurableSingletonClass D]
    (a b : Option κ) (μ : Measure (D × D))
    (f : D × D → D) (hf : Measurable f) (d : D) :
    labelled a μ {ω | f ω.2 = d ∧ ω.1 = b} = if a = b then μ (f ⁻¹' {d}) else 0 := by
  classical
  have hm : MeasurableSet {ω : Option κ × (D × D) | f ω.2 = d ∧ ω.1 = b} :=
    ((hf.comp measurable_snd) (measurableSet_singleton d)).inter
      (measurable_fst (measurableSet_singleton b))
  rw [labelled, Measure.map_apply (show Measurable (fun z : D × D => (a,z)) from measurable_const.prodMk measurable_id) hm]
  by_cases hab : a = b
  · simp only [hab, ↓reduceIte]
    congr 1
    ext z
    simp
  · simp only [hab, ↓reduceIte]
    have : (fun z => (a,z)) ⁻¹' {ω : Option κ × (D × D) | f ω.2 = d ∧ ω.1 = b} = ∅ := by
      ext z; simp [hab]
    rw [this,measure_empty]

lemma mixture_fiber {κ : Type uκ} {D : Type uD} [Fintype κ] [MeasurableSpace κ] [MeasurableSpace D]
    [MeasurableSingletonClass D]
    (p : κ → ℝ≥0∞) (p₀ : ℝ≥0∞) (μ₀ : Measure (D × D))
    (μ : κ → Measure (D × D)) (f : D × D → D) (hf : Measurable f) (d : D) :
    mixture p p₀ μ₀ μ {ω | f ω.2 = d} =
      p₀ * μ₀ (f ⁻¹' {d}) + ∑ a, p a * μ a (f ⁻¹' {d}) := by
  simp [mixture,Measure.add_apply,Measure.smul_apply,
    labelled_fiber _ _ f hf d]

lemma mixture_fiber_label {κ : Type uκ} {D : Type uD} [Fintype κ] [MeasurableSpace κ] [MeasurableSpace D]
    [MeasurableSingletonClass κ] [MeasurableSingletonClass D]
    (p : κ → ℝ≥0∞) (p₀ : ℝ≥0∞) (μ₀ : Measure (D × D))
    (μ : κ → Measure (D × D)) (f : D × D → D) (hf : Measurable f) (d : D) (a : κ) :
    mixture p p₀ μ₀ μ {ω | f ω.2 = d ∧ ω.1 = some a} = p a * μ a (f ⁻¹' {d}) := by
  classical
  simp [mixture,Measure.add_apply,Measure.smul_apply,
    labelled_fiber_label _ _ _ f hf d]

lemma prod_fiber_fst {D : Type uD} [MeasurableSpace D] [MeasurableSingletonClass D]
    (μ ν : Measure D) [IsProbabilityMeasure ν] (d : D) :
    (μ.prod ν) (Prod.fst ⁻¹' {d}) = μ {d} := by
  rw [show Prod.fst ⁻¹' {d} = ({d} : Set D) ×ˢ univ by ext z; simp,
    Measure.prod_prod,measure_univ,mul_one]

lemma prod_fiber_snd {D : Type uD} [MeasurableSpace D] [MeasurableSingletonClass D]
    (μ ν : Measure D) [IsProbabilityMeasure μ] [SFinite ν] (d : D) :
    (μ.prod ν) (Prod.snd ⁻¹' {d}) = ν {d} := by
  rw [show Prod.snd ⁻¹' {d} = (univ : Set D) ×ˢ {d} by ext z; simp,
    Measure.prod_prod,measure_univ,one_mul]


def lowerDigits (l a : ℕ) (ha : a < l) : Finset (Fin l) := Finset.Iio ⟨a,ha⟩
def upperDigits (l b : ℕ) (hb : b < l) : Finset (Fin l) := Finset.Ici ⟨b,hb⟩

lemma lowerDigits_nonempty (l a : ℕ) (ha : a < l) (hpos : 0 < a) :
    (lowerDigits l a ha).Nonempty := by
  exact ⟨⟨0,lt_trans hpos ha⟩,by simpa [lowerDigits,Fin.lt_def] using hpos⟩
lemma upperDigits_nonempty (l b : ℕ) (hb : b < l) :
    (upperDigits l b hb).Nonempty := by
  exact ⟨⟨b,hb⟩,by simp [upperDigits]⟩

@[simp] lemma card_lowerDigits (l a : ℕ) (ha : a < l) : (lowerDigits l a ha).card = a := by
  simp [lowerDigits]
@[simp] lemma card_upperDigits (l b : ℕ) (hb : b < l) : (upperDigits l b hb).card = l-b := by
  simp [upperDigits]
@[simp] lemma mem_lowerDigits (l a : ℕ) (ha : a < l) (d : Fin l) :
    d ∈ lowerDigits l a ha ↔ d.val < a := by simp [lowerDigits,Fin.lt_def]
@[simp] lemma mem_upperDigits (l b : ℕ) (hb : b < l) (d : Fin l) :
    d ∈ upperDigits l b hb ↔ b ≤ d.val := by simp [upperDigits,Fin.le_def]

def rectangle (l a b : ℕ) (ha : a < l) (hp : 0 < a) (hb : b < l) :
    Measure (Fin l × Fin l) :=
  (uniformOn (lowerDigits l a ha) (lowerDigits_nonempty l a ha hp)).prod
    (uniformOn (upperDigits l b hb) (upperDigits_nonempty l b hb))
instance rectangle_probability (l a b : ℕ) (ha : a < l) (hp : 0 < a) (hb : b < l) :
    IsProbabilityMeasure (rectangle l a b ha hp hb) := by unfold rectangle; infer_instance

lemma rectangle_fst_singleton (l a b : ℕ) (ha : a < l) (hp : 0 < a) (hb : b < l) (d : Fin l) :
    rectangle l a b ha hp hb (Prod.fst ⁻¹' {d}) = if d.val < a then (a : ℝ≥0∞)⁻¹ else 0 := by
  simp [rectangle,prod_fiber_fst,uniformOn_singleton]
lemma rectangle_snd_singleton (l a b : ℕ) (ha : a < l) (hp : 0 < a) (hb : b < l) (d : Fin l) :
    rectangle l a b ha hp hb (Prod.snd ⁻¹' {d}) = if b ≤ d.val then ((l-b : ℕ) : ℝ≥0∞)⁻¹ else 0 := by
  simp [rectangle,prod_fiber_snd,uniformOn_singleton]

lemma uniformOn_ae_mem {D : Type uD} [MeasurableSpace D] [MeasurableSingletonClass D]
    (S : Finset D) (hs : S.Nonempty) : ∀ᵐ d ∂uniformOn S hs, d ∈ S := by
  apply ae_iff.mpr
  change (uniformOn S hs) (↑S)ᶜ = 0
  rw [uniformOn,(PMF.uniformOfFinset S hs).toMeasure_apply_eq_zero_iff (S.measurableSet.compl),
    PMF.support_uniformOfFinset]
  exact disjoint_compl_right

lemma rectangle_ae (l a b : ℕ) (ha : a < l) (hp : 0 < a) (hb : b < l) :
    ∀ᵐ z ∂rectangle l a b ha hp hb, z.1.val < a ∧ b ≤ z.2.val := by
  have hx := uniformOn_ae_mem (lowerDigits l a ha) (lowerDigits_nonempty l a ha hp)
  have hy := uniformOn_ae_mem (upperDigits l b hb) (upperDigits_nonempty l b hb)
  unfold rectangle
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [hx] with x hxx
  filter_upwards [hy] with y hyy
  exact ⟨(mem_lowerDigits _ _ _ _).mp hxx,(mem_upperDigits _ _ _ _).mp hyy⟩

def diagonal (l : ℕ) [NeZero l] : Measure (Fin l × Fin l) :=
  Measure.map (fun d => (d,d)) (PMF.uniformOfFintype (Fin l)).toMeasure
instance diagonal_probability (l : ℕ) [NeZero l] : IsProbabilityMeasure (diagonal l) := by
  unfold diagonal
  infer_instance

lemma diagonal_fiber_fst (l : ℕ) [NeZero l] (d : Fin l) :
    diagonal l (Prod.fst ⁻¹' {d}) = (l : ℝ≥0∞)⁻¹ := by
  rw [diagonal,Measure.map_apply (by fun_prop) (measurable_fst (measurableSet_singleton d))]
  change (PMF.uniformOfFintype (Fin l)).toMeasure {d} = _
  simp [PMF.uniformOfFintype_apply]
lemma diagonal_fiber_snd (l : ℕ) [NeZero l] (d : Fin l) :
    diagonal l (Prod.snd ⁻¹' {d}) = (l : ℝ≥0∞)⁻¹ := by
  rw [diagonal,Measure.map_apply (by fun_prop) (measurable_snd (measurableSet_singleton d))]
  change (PMF.uniformOfFintype (Fin l)).toMeasure {d} = _
  simp [PMF.uniformOfFintype_apply]

def components (l t u r : ℕ) (ht : 0<t ∧ t<l) (hu : 0<u ∧ u<l) (hr : 0<r ∧ r<l) :
    Fin 5 → Measure (Fin l × Fin l) :=
  ![rectangle l (l-t) (l-t) (by omega) (by omega) (by omega),
    rectangle l t t ht.2 ht.1 ht.2,
    rectangle l (l-u) (l-u) (by omega) (by omega) (by omega),
    rectangle l u u hu.2 hu.1 hu.2,
    rectangle l r (l-r) hr.2 hr.1 (by omega)]
instance components_probability (l t u r : ℕ) (ht : 0<t ∧ t<l) (hu : 0<u ∧ u<l)
    (hr : 0<r ∧ r<l) (i : Fin 5) : IsProbabilityMeasure (components l t u r ht hu hr i) := by
  fin_cases i <;> dsimp [components] <;> infer_instance

def sixWeights (p q τ : ℝ≥0∞) : Fin 5 → ℝ≥0∞ := ![p,p,q,q,τ]
lemma sum_sixWeights (p q τ : ℝ≥0∞) : ∑ a, sixWeights p q τ a = 2*p+2*q+τ := by
  simp [sixWeights,Fin.sum_univ_succ]
  ring

def sixLaw (l t u r : ℕ) [NeZero l] (ht : 0<t ∧ t<l) (hu : 0<u ∧ u<l)
    (hr : 0<r ∧ r<l) (p q τ : ℝ≥0∞) : Measure (Option (Fin 5) × (Fin l × Fin l)) :=
  mixture (sixWeights p q τ) (1-(2*p+2*q+τ)) (diagonal l) (components l t u r ht hu hr)

lemma sixLaw_probability (l t u r : ℕ) [NeZero l] (ht : 0<t ∧ t<l) (hu : 0<u ∧ u<l)
    (hr : 0<r ∧ r<l) (p q τ : ℝ≥0∞) (hp : 2*p+2*q+τ ≤ 1) :
    IsProbabilityMeasure (sixLaw l t u r ht hu hr p q τ) := by
  apply mixture_probability
  rw [sum_sixWeights,tsub_add_cancel_of_le hp]

lemma sixLaw_top_t (l t u r : ℕ) [NeZero l] (ht : 0<t ∧ t<l) (hu : 0<u ∧ u<l)
    (hr : 0<r ∧ r<l) (p q τ : ℝ≥0∞) (d : Fin l) (hd : d.val < l-t) :
    sixLaw l t u r ht hu hr p q τ {ω | ω.2.1 = d ∧ ω.1 = some (0 : Fin 5)} =
      p * ((l-t : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [sixLaw,mixture_fiber_label _ _ _ _ Prod.fst measurable_fst]
  simp [sixWeights,components,rectangle_fst_singleton,hd]

lemma sixLaw_bottom_t (l t u r : ℕ) [NeZero l] (ht : 0<t ∧ t<l) (hu : 0<u ∧ u<l)
    (hr : 0<r ∧ r<l) (p q τ : ℝ≥0∞) (d : Fin l) (hd : t ≤ d.val) :
    sixLaw l t u r ht hu hr p q τ {ω | ω.2.2 = d ∧ ω.1 = some (1 : Fin 5)} =
      p * ((l-t : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [sixLaw,mixture_fiber_label _ _ _ _ Prod.snd measurable_snd]
  simp [sixWeights,components,rectangle_snd_singleton,hd]

lemma sixLaw_top_u (l t u r : ℕ) [NeZero l] (ht : 0<t ∧ t<l) (hu : 0<u ∧ u<l)
    (hr : 0<r ∧ r<l) (p q τ : ℝ≥0∞) (d : Fin l) (hd : d.val < l-u) :
    sixLaw l t u r ht hu hr p q τ {ω | ω.2.1 = d ∧ ω.1 = some (2 : Fin 5)} =
      q * ((l-u : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [sixLaw,mixture_fiber_label _ _ _ _ Prod.fst measurable_fst]
  simp [sixWeights,components,rectangle_fst_singleton,hd]

lemma sixLaw_bottom_u (l t u r : ℕ) [NeZero l] (ht : 0<t ∧ t<l) (hu : 0<u ∧ u<l)
    (hr : 0<r ∧ r<l) (p q τ : ℝ≥0∞) (d : Fin l) (hd : u ≤ d.val) :
    sixLaw l t u r ht hu hr p q τ {ω | ω.2.2 = d ∧ ω.1 = some (3 : Fin 5)} =
      q * ((l-u : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [sixLaw,mixture_fiber_label _ _ _ _ Prod.snd measurable_snd]
  simp [sixWeights,components,rectangle_snd_singleton,hd]

lemma sixLaw_tag (l t u r : ℕ) [NeZero l] (ht : 0<t ∧ t<l) (hu : 0<u ∧ u<l)
    (hr : 0<r ∧ r<l) (p q τ : ℝ≥0∞) :
    sixLaw l t u r ht hu hr p q τ {ω | ω.1 = some (4 : Fin 5)} = τ := by
  have h := mixture_fiber_label (sixWeights p q τ) (1-(2*p+2*q+τ)) (diagonal l)
    (components l t u r ht hu hr) (fun _ => (0 : Fin l)) measurable_const 0 (4 : Fin 5)
  simpa [sixLaw,sixWeights,measure_univ] using h
end

lemma mixture_fiber_real {κ : Type uκ} {D : Type uD} [Fintype κ] [MeasurableSpace κ] [MeasurableSpace D]
    [MeasurableSingletonClass D]
    (p : κ → ℝ≥0∞) (p₀ : ℝ≥0∞) (μ₀ : Measure (D × D))
    (μ : κ → Measure (D × D)) [IsFiniteMeasure μ₀] [∀ i, IsFiniteMeasure (μ i)]
    (hp : ∀ i, p i ≠ ∞) (hp₀ : p₀ ≠ ∞)
    (f : D × D → D) (hf : Measurable f) (d : D) :
    (mixture p p₀ μ₀ μ).real {ω | f ω.2 = d} =
      p₀.toReal * μ₀.real (f ⁻¹' {d}) + ∑ a, (p a).toReal * (μ a).real (f ⁻¹' {d}) := by
  rw [measureReal_def,mixture_fiber _ _ _ _ f hf]
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top hp₀ (measure_ne_top _ _))
    (ENNReal.sum_ne_top.mpr (fun i _ => ENNReal.mul_ne_top (hp i) (measure_ne_top _ _))),
    ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top (hp i) (measure_ne_top _ _))]
  simp [ENNReal.toReal_mul,measureReal_def]

lemma rectangle_fst_real (l a b : ℕ) (ha : a < l) (hp : 0 < a) (hb : b < l) (d : Fin l) :
    (rectangle l a b ha hp hb).real (Prod.fst ⁻¹' {d}) =
      if d.val < a then (a : ℝ)⁻¹ else 0 := by
  rw [measureReal_def,rectangle_fst_singleton]
  split_ifs <;> simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_zero]
lemma rectangle_snd_real (l a b : ℕ) (ha : a < l) (hp : 0 < a) (hb : b < l) (d : Fin l) :
    (rectangle l a b ha hp hb).real (Prod.snd ⁻¹' {d}) =
      if b ≤ d.val then ((l-b : ℕ) : ℝ)⁻¹ else 0 := by
  rw [measureReal_def,rectangle_snd_singleton]
  split_ifs <;> simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_zero]

lemma rectangle_fst_real_le (l a b : ℕ) (ha : a < l) (hp : 0 < a) (hb : b < l) (d : Fin l) :
    (rectangle l a b ha hp hb).real (Prod.fst ⁻¹' {d}) ≤ (a : ℝ)⁻¹ := by
  rw [rectangle_fst_real]
  split_ifs
  · exact le_rfl
  · positivity
lemma rectangle_snd_real_le (l a b : ℕ) (ha : a < l) (hp : 0 < a) (hb : b < l) (d : Fin l) :
    (rectangle l a b ha hp hb).real (Prod.snd ⁻¹' {d}) ≤ ((l-b : ℕ) : ℝ)⁻¹ := by
  rw [rectangle_snd_real]
  split_ifs
  · exact le_rfl
  · positivity

lemma sixLaw_fiber_real_le (l t u r : ℕ) [NeZero l] (ht : 0<t ∧ t<l) (hu : 0<u ∧ u<l)
    (hr : 0<r ∧ r<l) (p q τ : ℝ≥0∞) (hp : 2*p+2*q+τ ≤ 1)
    (f : Fin l × Fin l → Fin l) (hf : Measurable f) (d : Fin l)
    (hdiag : (diagonal l).real (f ⁻¹' {d}) = (l : ℝ)⁻¹)
    (M : Fin 5 → ℝ) (hM : ∀ i, (components l t u r ht hu hr i).real (f ⁻¹' {d}) ≤ M i) :
    (sixLaw l t u r ht hu hr p q τ).real {ω | f ω.2 = d} ≤
      (l : ℝ)⁻¹ + ∑ i, (sixWeights p q τ i).toReal * M i := by
  have hweight (i : Fin 5) : sixWeights p q τ i ≤ 1 := by
    apply le_trans (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ _))
    rwa [sum_sixWeights]
  have hrem : 1-(2*p+2*q+τ) ≤ (1 : ℝ≥0∞) := tsub_le_self
  rw [sixLaw,mixture_fiber_real _ _ _ _
    (fun i => ne_top_of_le_ne_top ENNReal.one_ne_top (hweight i))
    (ne_top_of_le_ne_top ENNReal.one_ne_top hrem) f hf,hdiag]
  apply add_le_add
  · have hrem' : (1-(2*p+2*q+τ)).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top hrem
    convert mul_le_mul_of_nonneg_right hrem' (by positivity : 0 ≤ (l : ℝ)⁻¹) using 1; ring
  · exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hM i) ENNReal.toReal_nonneg)

lemma twoWidth_density_numerical (l t u r : ℕ) (hl : 0 < l)
    (ht : 0 < t ∧ t < l) (hu : 0 < u ∧ u < l) (hr : 0 < r ∧ r < l)
    (a b m κ ρ σ τ : ℝ) (ha : 0 < a) (hb : 0 < b) (hm : 0 < m)
    (_ha' : a  ≤  1) (_hb' : b  ≤  1) (hκ : 0 ≤ κ) (hκ' : κ ≤ 1/100)
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (_hτ : 0 ≤ τ)
    (htlo : (l : ℝ)*a/3  ≤  (t : ℝ)) (hthi : (t : ℝ)  ≤  (l : ℝ)/2)
    (hulo : (l : ℝ)*b/3  ≤  (u : ℝ)) (huhi : (u : ℝ)  ≤  (l : ℝ)/2)
    (hrlo : (l : ℝ)/(2*m)  ≤  (r : ℝ)) (_hrhi : (r : ℝ)  ≤  (l : ℝ)/2)
    (hρα : ρ/a  ≤  κ) (hσb : σ/b  ≤  κ) (hτm : τ  ≤  1/m) :
    (l : ℝ)⁻¹ + ρ*((t : ℝ)⁻¹+((l-t : ℕ) : ℝ)⁻¹) +
      σ*((u : ℝ)⁻¹+((l-u : ℕ) : ℝ)⁻¹) + τ*(r : ℝ)⁻¹  ≤  10/(l : ℝ) := by
  have hlr : (0 : ℝ) < l := by exact_mod_cast hl
  have htr : (0 : ℝ) < t := by exact_mod_cast ht.1
  have hur : (0 : ℝ) < u := by exact_mod_cast hu.1
  have hrr : (0 : ℝ) < r := by exact_mod_cast hr.1
  have hlt : (0 : ℝ) <  (l-t : ℕ) := by exact_mod_cast (Nat.sub_pos_of_lt ht.2)
  have hlu : (0 : ℝ) <  (l-u : ℕ) := by exact_mod_cast (Nat.sub_pos_of_lt hu.2)
  have hrt : (l : ℝ)*a/3  ≤  ((l-t : ℕ) : ℝ) := by
    rw [Nat.cast_sub ht.2.le]; nlinarith
  have hru : (l : ℝ)*b/3  ≤  ((l-u : ℕ) : ℝ) := by
    rw [Nat.cast_sub hu.2.le]; nlinarith
  have bound (w z v : ℝ) (hw : 0 < w) (hz : 0 < z) (_hv : 0 ≤ v)
      (hzw : (l : ℝ)*w/3 ≤ z) (hvw : v/w ≤ κ) : v*z⁻¹  ≤  3*κ/(l : ℝ) := by
    have hp : v  ≤  κ*w := (div_le_iff₀ hw).mp hvw
    rw [← div_eq_mul_inv,div_le_iff₀ hz]
    rw [div_mul_eq_mul_div,le_div_iff₀ hlr]
    nlinarith [mul_le_mul_of_nonneg_left hp hlr.le, mul_le_mul_of_nonneg_left hzw hκ]
  have ht1 := bound a t ρ ha htr hρ htlo hρα
  have ht2 := bound a (l-t : ℕ) ρ ha hlt hρ hrt hρα
  have hu1 := bound b u σ hb hur hσ hulo hσb
  have hu2 := bound b (l-u : ℕ) σ hb hlu hσ hru hσb
  have hr1 : τ*(r : ℝ)⁻¹  ≤  2/(l : ℝ) := by
    rw [← div_eq_mul_inv,div_le_iff₀ hrr]
    rw [div_mul_eq_mul_div,le_div_iff₀ hlr]
    have hrlo' := (div_le_iff₀ (by positivity : 0 < 2*m)).mp hrlo
    have hτm' := (le_div_iff₀ hm).mp hτm
    have hτl : τ*(l : ℝ) ≤ (l : ℝ)/m := by
      have hh := mul_le_mul_of_nonneg_left hτm hlr.le
      simpa only [mul_one_div,mul_comm] using hh
    have hrl : (l : ℝ)/m ≤ 2*(r : ℝ) := by
      rw [div_le_iff₀ hm]
      nlinarith [hrlo']
    exact hτl.trans hrl
  have hk : 12*κ/(l : ℝ)  ≤  (7 : ℝ)/(l : ℝ) := by
    apply div_le_div_of_nonneg_right _ hlr.le
    linarith
  simp only [div_eq_mul_inv] at ht1 ht2 hu1 hu2 hr1 hk ⊢
  nlinarith


end CircleCoupling

end

end OAI
