import Mathlib
import OAI.Probability.IsingPerceptron.NoiseGibbsRegular

namespace OAI

/-! Child Label. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

abbrev ChildLabel := ℕ × ℕ
abbrev WeightCloud := ℕ → ℕ × (ℕ → ℝ)

@[reducible] def labeledTreeSpace : ℕ → RawTreeSpace
  | 0 => ⟨PUnit, inferInstance⟩
  | n+1 => let T := labeledTreeSpace n
    letI := T.space
    ⟨WeightCloud × (ℕ → ℕ → T.carrier), inferInstance⟩

abbrev LabeledTree (n : ℕ) := (labeledTreeSpace n).carrier
instance labeledTreeMeasurableSpace (n : ℕ) : MeasurableSpace (LabeledTree n) :=
  (labeledTreeSpace n).space
instance labeledTreeNonempty : (n : ℕ) → Nonempty (LabeledTree n)
  | 0 => ⟨PUnit.unit⟩
  | n+1 => letI := labeledTreeNonempty n
    inferInstanceAs (Nonempty (WeightCloud × (ℕ → ℕ → LabeledTree n)))

def intensityComponents {E : Type*} [MeasurableSpace E] (μ : Measure E) [SFinite μ] :
    ℕ → FiniteMeasure E := fun n => ⟨sfiniteSeq μ n,inferInstance⟩

lemma intensityComponents_sum {E : Type*} [MeasurableSpace E] (μ : Measure E) [SFinite μ] :
    Measure.sum (fun n => (intensityComponents μ n : Measure E)) = μ :=
  sum_sfiniteSeq μ

def labeledCascadeLaw : (n : ℕ) → (ℕ → ℝ) → ProbabilityMeasure (LabeledTree n)
  | 0, _ => ⟨Measure.dirac PUnit.unit, by
      change IsProbabilityMeasure (Measure.dirac (PUnit.unit : PUnit)); infer_instance⟩
  | n+1, b => ⟨(labeledPoissonLaw (intensityComponents (powerIntensity (b 0)))).prod
      (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
        (labeledCascadeLaw n (fun j => b (j+1)) : Measure (LabeledTree n))))), by
      change IsProbabilityMeasure ((labeledPoissonLaw _).prod
        (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
          (labeledCascadeLaw n (fun j => b (j+1)) : Measure (LabeledTree n))))))
      infer_instance⟩

def labeledTreeForget : (n : ℕ) → LabeledTree n → RawTree n
  | 0, _ => PUnit.unit
  | n+1, ω => labeledMarkedMeasure (ω.1,fun m i => labeledTreeForget n (ω.2 m i))

lemma measurable_labeledTreeForget (n : ℕ) : Measurable (labeledTreeForget n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact measurable_labeledMarkedMeasure.comp
      (measurable_fst.prodMk (Measurable.of_eval (fun m => Measurable.of_eval
        (fun i => ih.comp ((measurable_pi_apply i).comp
          ((measurable_pi_apply m).comp measurable_snd))))))

theorem labeledCascadeLaw_forget (n : ℕ) (b : ℕ → ℝ) :
    (labeledCascadeLaw n b : Measure (LabeledTree n)).map (labeledTreeForget n) =
      rawCascadeLaw n b := by
  induction n generalizing b with
  | zero =>
    change (Measure.dirac (PUnit.unit : PUnit)).map (fun _ => PUnit.unit) = Measure.dirac PUnit.unit
    rw [Measure.map_dirac' measurable_const]
  | succ n ih =>
    let b' := fun j => b (j+1)
    have hp : MeasurePreserving (labeledTreeForget n)
        (labeledCascadeLaw n b' : Measure (LabeledTree n)) (rawCascadeLaw n b') :=
      ⟨measurable_labeledTreeForget n,ih b'⟩
    have hpi : MeasurePreserving (fun ω : ℕ → LabeledTree n => fun i => labeledTreeForget n (ω i))
        (Measure.infinitePi (fun _ : ℕ => (labeledCascadeLaw n b' : Measure (LabeledTree n))))
        (Measure.infinitePi (fun _ : ℕ => (rawCascadeLaw n b' : Measure (RawTree n)))) := by
      refine ⟨Measurable.of_eval (fun _ => (measurable_labeledTreeForget n).comp
        (measurable_pi_apply _)),?_⟩
      rw [Measure.infinitePi_map_pi _ (fun _ => measurable_labeledTreeForget n)]
      simp_rw [hp.map_eq]
    have hppi : MeasurePreserving (fun ω : ℕ → ℕ → LabeledTree n =>
        fun m i => labeledTreeForget n (ω m i))
        (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi
          (fun _ : ℕ => (labeledCascadeLaw n b' : Measure (LabeledTree n)))))
        (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi
          (fun _ : ℕ => (rawCascadeLaw n b' : Measure (RawTree n))))) := by
      refine ⟨Measurable.of_eval (fun _ => hpi.measurable.comp (measurable_pi_apply _)),?_⟩
      rw [Measure.infinitePi_map_pi _ (fun _ => hpi.measurable)]
      simp_rw [hpi.map_eq]
    have hprod := (MeasurePreserving.id
      (labeledPoissonLaw (intensityComponents (powerIntensity (b 0))))).prod hppi
    change ((labeledPoissonLaw (intensityComponents (powerIntensity (b 0)))).prod
      (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi
        (fun _ : ℕ => (labeledCascadeLaw n b' : Measure (LabeledTree n)))))).map
      (labeledMarkedMeasure ∘ Prod.map id (fun ω => fun m i => labeledTreeForget n (ω m i))) = _
    rw [← Measure.map_map measurable_labeledMarkedMeasure hprod.measurable,hprod.map_eq,
      labeledMarkedMeasure_law,rawCascadeLaw_succ]
    apply poissonLaw_congr
    rw [intensityComponents_sum]

@[reducible] def LabeledLeaf : ℕ → Type
  | 0 => PUnit
  | n+1 => ChildLabel × LabeledLeaf n
instance labeledLeafMeasurableSpace : (n : ℕ) → MeasurableSpace (LabeledLeaf n)
  | 0 => inferInstanceAs (MeasurableSpace PUnit)
  | n+1 => letI := labeledLeafMeasurableSpace n
    inferInstanceAs (MeasurableSpace (ChildLabel × LabeledLeaf n))
instance labeledLeafCountable : (n : ℕ) → Countable (LabeledLeaf n)
  | 0 => inferInstanceAs (Countable PUnit)
  | n+1 => letI := labeledLeafCountable n
    inferInstanceAs (Countable (ChildLabel × LabeledLeaf n))
instance labeledLeafSingleton : (n : ℕ) → MeasurableSingletonClass (LabeledLeaf n)
  | 0 => inferInstanceAs (MeasurableSingletonClass PUnit)
  | n+1 => letI := labeledLeafSingleton n
    inferInstanceAs (MeasurableSingletonClass (ChildLabel × LabeledLeaf n))
instance labeledLeafNonempty : (n : ℕ) → Nonempty (LabeledLeaf n)
  | 0 => inferInstanceAs (Nonempty PUnit)
  | n+1 => letI := labeledLeafNonempty n
    inferInstanceAs (Nonempty (ChildLabel × LabeledLeaf n))

def childLabelWeight (ω : WeightCloud) (a : ChildLabel) : ℝ≥0∞ :=
  if a.2 < (ω a.1).1 then ENNReal.ofReal (max ((ω a.1).2 a.2) 0) else 0

def labeledLeafWeight : (n : ℕ) → LabeledTree n → LabeledLeaf n → ℝ≥0∞
  | 0, _, _ => 1
  | n+1, ω, v => childLabelWeight ω.1 v.1 * labeledLeafWeight n (ω.2 v.1.1 v.1.2) v.2

lemma measurable_childLabelWeight (a : ChildLabel) : Measurable (fun ω => childLabelWeight ω a) := by
  unfold childLabelWeight
  apply Measurable.ite
  · exact measurableSet_lt measurable_const (by fun_prop)
  · fun_prop
  · fun_prop

lemma measurable_labeledLeafWeight (n : ℕ) (v : LabeledLeaf n) :
    Measurable (fun ω => labeledLeafWeight n ω v) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact ((measurable_childLabelWeight v.1).comp measurable_fst).mul
      ((ih v.2).comp ((measurable_pi_apply v.1.2).comp
        ((measurable_pi_apply v.1.1).comp measurable_snd)))

def labeledLeafMass (n : ℕ) (ω : LabeledTree n) : Measure (LabeledLeaf n) :=
  Measure.count.withDensity (labeledLeafWeight n ω)

lemma labeledLeafMass_lintegral (n : ℕ) (ω : LabeledTree n) (F : LabeledLeaf n → ℝ≥0∞) :
    (∫⁻ v, F v ∂labeledLeafMass n ω) = ∑' v, labeledLeafWeight n ω v * F v := by
  rw [labeledLeafMass,lintegral_withDensity_eq_lintegral_mul _ (measurable_of_countable _) 
    (measurable_of_countable _),lintegral_count]
  rfl

lemma measurable_labeledLeafMass (n : ℕ) : Measurable (labeledLeafMass n) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [labeledLeafMass,withDensity_apply _ hs,← lintegral_indicator hs,lintegral_count]
  exact Measurable.tsum (fun v => by
    by_cases hv : v ∈ s
    · simpa only [Set.indicator_of_mem hv] using measurable_labeledLeafWeight n v
    · simp only [Set.indicator_of_notMem hv]; exact measurable_const)

lemma finiteCloud_tsum_weight (ω : WeightCloud) (F : ChildLabel → ℝ≥0∞) :
    (∑' a, childLabelWeight ω a * F a) =
      ∑' m, ∑ i : Fin (ω m).1, ENNReal.ofReal (max ((ω m).2 i) 0) * F (m,i) := by
  rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro m
  simp only [childLabelWeight,ite_mul,zero_mul]
  rw [tsum_eq_sum (s := Finset.range (ω m).1)]
  · rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp only [i.isLt,ite_true]
  · intro i hi
    exact ite_eq_right (by simpa using hi)

lemma rawTreeTotal_labeled_eq (n : ℕ) (ω : LabeledTree n) :
    rawTreeTotal n (labeledTreeForget n ω) = ∑' v, labeledLeafWeight n ω v := by
  induction n with
  | zero => simp [rawTreeTotal,labeledLeafWeight]
  | succ n ih =>
    change (∫⁻ p : ℝ × RawTree n, ENNReal.ofReal (max p.1 0) * rawTreeTotal n p.2
      ∂labeledMarkedMeasure (ω.1,fun m i => labeledTreeForget n (ω.2 m i))) = _
    have hm : Measurable (fun p : ℝ × RawTree n => ENNReal.ofReal (max p.1 0) * rawTreeTotal n p.2) :=
      (by fun_prop : Measurable (fun p : ℝ × RawTree n => ENNReal.ofReal (max p.1 0))).mul
        ((measurable_rawTreeTotal n).comp measurable_snd)
    simp only [labeledMarkedMeasure,lintegral_sum_measure,finiteCloudMeasure_lintegral _ hm]
    simp only [ih]
    change _ = ∑' v : ChildLabel × LabeledLeaf n,
      childLabelWeight ω.1 v.1 * labeledLeafWeight n (ω.2 v.1.1 v.1.2) v.2
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left]
    rw [finiteCloud_tsum_weight]

lemma labeledLeafMass_univ (n : ℕ) (ω : LabeledTree n) :
    labeledLeafMass n ω Set.univ = rawTreeTotal n (labeledTreeForget n ω) := by
  rw [← lintegral_one,labeledLeafMass_lintegral]
  simp only [mul_one,rawTreeTotal_labeled_eq]

def labeledLeafLaw (n : ℕ) (ω : LabeledTree n) : Measure (LabeledLeaf n) :=
  normalizeMass (labeledLeafMass n ω)
instance labeledLeafLaw_probability (n : ℕ) (ω : LabeledTree n) :
    IsProbabilityMeasure (labeledLeafLaw n ω) := normalizeMass_probability _
lemma measurable_labeledLeafLaw (n : ℕ) : Measurable (labeledLeafLaw n) :=
  measurable_normalizeMass.comp (measurable_labeledLeafMass n)

variable (A : Type) [MeasurableSpace A]

@[reducible] def markForestSpace : ℕ → RawTreeSpace
  | 0 => ⟨PUnit,inferInstance⟩
  | n+1 => let T := markForestSpace n
    letI := T.space
    ⟨ℕ → ℕ → A × T.carrier,inferInstance⟩

abbrev MarkForest (n : ℕ) := (markForestSpace A n).carrier
instance markForestMeasurableSpace (n : ℕ) : MeasurableSpace (MarkForest A n) :=
  (markForestSpace A n).space
instance markForestNonempty [Nonempty A] : (n : ℕ) → Nonempty (MarkForest A n)
  | 0 => inferInstanceAs (Nonempty PUnit)
  | n+1 => letI := markForestNonempty n
    inferInstanceAs (Nonempty (ℕ → ℕ → A × MarkForest A n))

def markForestLaw : (n : ℕ) → (ℕ → ProbabilityMeasure A) → ProbabilityMeasure (MarkForest A n)
  | 0, _ => ⟨Measure.dirac PUnit.unit,by
      change IsProbabilityMeasure (Measure.dirac (PUnit.unit : PUnit)); infer_instance⟩
  | n+1, μ => ⟨Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ =>
      (μ 0 : Measure A).prod (markForestLaw n (fun j => μ (j+1)) : Measure (MarkForest A n)))),by
        change IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi
          (fun _ : ℕ => (μ 0 : Measure A).prod (markForestLaw n (fun j => μ (j+1)) : Measure (MarkForest A n)))))
        infer_instance⟩

def labeledNoiseJoin : (n : ℕ) → LabeledTree n × MarkForest A n → NoiseTree A n
  | 0, _ => PUnit.unit
  | n+1, p => labeledMarkedMeasure (p.1.1,fun m i =>
      ((p.2 m i).1,labeledNoiseJoin n (p.1.2 m i,(p.2 m i).2)))

@[fun_prop] lemma measurable_labeledNoiseJoin (n : ℕ) : Measurable (labeledNoiseJoin A n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun p : (WeightCloud × (ℕ → ℕ → LabeledTree n)) ×
        (ℕ → ℕ → A × MarkForest A n) => labeledMarkedMeasure (p.1.1,fun m i =>
          ((p.2 m i).1,labeledNoiseJoin A n (p.1.2 m i,(p.2 m i).2))))
    apply measurable_labeledMarkedMeasure.comp
    apply Measurable.prodMk (by fun_prop)
    apply Measurable.of_eval
    intro m
    apply Measurable.of_eval
    intro i
    exact (by fun_prop : Measurable (fun p : LabeledTree (n+1) × MarkForest A (n+1) =>
      (p.2 m i).1)).prodMk (ih.comp (by fun_prop))

lemma infinitePi_prod_join2 {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : Measure E) (ν : Measure F) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ((Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => μ))).prod
      (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => ν)))).map
      (fun p m i => (p.1 m i,p.2 m i)) =
      Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => μ.prod ν)) := by
  rw [show (fun p : (ℕ → ℕ → E) × (ℕ → ℕ → F) => fun m i => (p.1 m i,p.2 m i)) =
      (fun q : ℕ → (ℕ → E) × (ℕ → F) => fun m i => ((q m).1 i,(q m).2 i)) ∘
      (fun p : (ℕ → ℕ → E) × (ℕ → ℕ → F) => fun m => (p.1 m,p.2 m)) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop),infinitePi_prod_join,
    Measure.infinitePi_map_pi _ (f := fun (_ : ℕ) (q : (ℕ → E) × (ℕ → F)) => fun i => (q.1 i,q.2 i))
      (fun _ => by fun_prop)]
  simp_rw [infinitePi_prod_join]

lemma measurePreserving_swap_first_two {E F G : Type*}
    [MeasurableSpace E] [MeasurableSpace F] [MeasurableSpace G]
    (μ : Measure E) (ν : Measure F) (ξ : Measure G)
    [SFinite μ] [SFinite ν] [SFinite ξ] :
    MeasurePreserving (fun p : E × (F × G) => (p.2.1,(p.1,p.2.2)))
      (μ.prod (ν.prod ξ)) (ν.prod (μ.prod ξ)) := by
  exact (measurePreserving_prodAssoc ν μ ξ).comp
    (((Measure.measurePreserving_swap (μ := μ) (ν := ν)).prod (MeasurePreserving.id ξ)).comp
      (measurePreserving_prodAssoc μ ν ξ).symm)

theorem labeledNoiseJoin_law [Nonempty A] (n : ℕ) (b : ℕ → ℝ)
    (μ : ℕ → ProbabilityMeasure A) :
    ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (markForestLaw A n μ)).map (labeledNoiseJoin A n) = noiseCascadeLaw A n b μ := by
  induction n generalizing b μ with
  | zero =>
    change ((Measure.dirac (PUnit.unit : PUnit)).prod (Measure.dirac (PUnit.unit : PUnit))).map
      (fun _ => PUnit.unit) = Measure.dirac PUnit.unit
    rw [Measure.map_const]
    simp
  | succ n ih =>
    let b' := fun j => b (j+1)
    let μ' := fun j => μ (j+1)
    let L : Measure (LabeledTree n) := labeledCascadeLaw n b'
    let M : Measure (MarkForest A n) := markForestLaw A n μ'
    let R : Measure (NoiseTree A n) := noiseCascadeLaw A n b' μ'
    let W := labeledPoissonLaw (intensityComponents (powerIntensity (b 0)))
    have hi : MeasurePreserving (labeledNoiseJoin A n) (L.prod M) R :=
      ⟨measurable_labeledNoiseJoin A n,ih b' μ'⟩
    have hp := ((MeasurePreserving.id (μ 0 : Measure A)).prod hi).comp
      (measurePreserving_swap_first_two L (μ 0 : Measure A) M)
    have hmap : (L.prod ((μ 0 : Measure A).prod M)).map
        (fun p => (p.2.1,labeledNoiseJoin A n (p.1,p.2.2))) = (μ 0 : Measure A).prod R := hp.map_eq
    have hpi : MeasurePreserving
        (fun p : (ℕ → ℕ → LabeledTree n) × (ℕ → ℕ → A × MarkForest A n) =>
          fun m i => ((p.2 m i).1,labeledNoiseJoin A n (p.1 m i,(p.2 m i).2)))
        ((Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => L))).prod
          (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (μ 0 : Measure A).prod M))))
        (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (μ 0 : Measure A).prod R))) := by
      refine ⟨Measurable.of_eval (fun m => Measurable.of_eval (fun i =>
        (by fun_prop : Measurable (fun p : (ℕ → ℕ → LabeledTree n) ×
            (ℕ → ℕ → A × MarkForest A n) => (p.2 m i).1)).prodMk
          ((measurable_labeledNoiseJoin A n).comp (by fun_prop)))),?_⟩
      rw [show (fun p : (ℕ → ℕ → LabeledTree n) × (ℕ → ℕ → A × MarkForest A n) =>
          fun m i => ((p.2 m i).1,labeledNoiseJoin A n (p.1 m i,(p.2 m i).2))) =
          (fun q : ℕ → ℕ → LabeledTree n × (A × MarkForest A n) => fun m i =>
            ((q m i).2.1,labeledNoiseJoin A n ((q m i).1,(q m i).2.2))) ∘
          (fun p => fun m i => (p.1 m i,p.2 m i)) from rfl,
        ← Measure.map_map (by fun_prop) (by fun_prop),infinitePi_prod_join2,
        Measure.infinitePi_map_pi _ (f := fun (_ : ℕ) (q : ℕ → LabeledTree n × (A × MarkForest A n)) => fun i =>
          ((q i).2.1,labeledNoiseJoin A n ((q i).1,(q i).2.2))) (fun _ => by fun_prop)]
      simp_rw [Measure.infinitePi_map_pi _ (f := fun (_ : ℕ) (p : LabeledTree n × (A × MarkForest A n)) =>
        (p.2.1,labeledNoiseJoin A n (p.1,p.2.2))) (fun _ => hp.measurable),hmap]
    have hfull := ((MeasurePreserving.id W).prod hpi).comp
      (measurePreserving_prodAssoc W _ _)
    change ((W.prod (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => L)))).prod
      (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (μ 0 : Measure A).prod M)))).map
      (labeledMarkedMeasure ∘ (fun p => (p.1.1,fun m i =>
        ((p.2 m i).1,labeledNoiseJoin A n (p.1.2 m i,(p.2 m i).2))))) = _
    have hfm : Measurable (fun p : (WeightCloud × (ℕ → ℕ → LabeledTree n)) ×
        (ℕ → ℕ → A × MarkForest A n) => (p.1.1,fun m i =>
          ((p.2 m i).1,labeledNoiseJoin A n (p.1.2 m i,(p.2 m i).2)))) := hfull.measurable
    rw [← Measure.map_map measurable_labeledMarkedMeasure hfm]
    have hfe : ((W.prod (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => L)))).prod
        (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (μ 0 : Measure A).prod M)))).map
        (fun p => (p.1.1,fun m i => ((p.2 m i).1,labeledNoiseJoin A n (p.1.2 m i,(p.2 m i).2)))) =
        W.prod (Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : ℕ => (μ 0 : Measure A).prod R))) := hfull.map_eq
    rw [hfe,labeledMarkedMeasure_law,noiseCascadeLaw_succ]
    apply poissonLaw_congr
    rw [intensityComponents_sum]

end IsingPerceptron

namespace IsingPerceptron

lemma infinitePi_option_join {ι A : Type*} [MeasurableSpace A]
    (μ : Measure A) (ν : ι → Measure A) [IsProbabilityMeasure μ]
    [∀ i, IsProbabilityMeasure (ν i)] :
    (μ.prod (Measure.infinitePi ν)).map (fun p : A × (ι → A) => fun i : Option ι =>
      i.elim p.1 p.2) = Measure.infinitePi (fun i : Option ι => i.elim μ ν) := by
  classical
  let ρ : Option ι → Measure A := fun i => i.elim μ ν
  have : ∀ i, IsProbabilityMeasure (ρ i) := fun i => by cases i <;> dsimp [ρ] <;> infer_instance
  change _ = Measure.infinitePi ρ
  refine Measure.eq_infinitePi ρ (fun I t ht => ?_)
  have hm : Measurable (fun p : A × (ι → A) => fun i : Option ι => i.elim p.1 p.2) := by
    apply Measurable.of_eval
    intro i
    cases i <;> dsimp <;> fun_prop
  rw [Measure.map_apply hm (.pi I.countable_toSet (fun i _ => ht i))]
  have he : (fun p : A × (ι → A) => fun i : Option ι => i.elim p.1 p.2) ⁻¹'
      ((I : Set (Option ι)).pi t) =
      (if none ∈ I then t none else Set.univ) ×ˢ ((I.eraseNone : Set ι).pi (fun i => t (some i))) := by
    ext p
    simp only [Set.mem_preimage,Set.mem_pi,Set.mem_prod,Finset.mem_coe,Finset.mem_eraseNone]
    constructor
    · intro h
      constructor
      · split_ifs with hn
        · exact h none hn
        · trivial
      · intro i hi
        exact h (some i) hi
    · rintro ⟨ha,hb⟩ i hi
      cases i with
      | none => simpa only [ite_eq_left hi,Option.elim_none] using ha
      | some i => exact hb i hi
  rw [he,Measure.prod_prod,Measure.infinitePi_pi _ (fun i _ => ht (some i))]
  by_cases hn : none ∈ I
  · rw [ite_eq_left hn,← Finset.prod_erase_mul _ _ hn]
    have her : I.erase none = I.eraseNone.map (Function.Embedding.some) := by
      ext i
      cases i <;> simp
    rw [her,Finset.prod_map,mul_comm]
    rfl
  · rw [ite_eq_right hn,measure_univ,one_mul]
    have her : I = I.eraseNone.map (Function.Embedding.some) := by
      ext i
      cases i <;> simp [hn]
    rw [her,Finset.prod_map]
    simp only [Finset.eraseNone_map_some]
    rfl

lemma infinitePi_option_split {ι A : Type*} [MeasurableSpace A]
    (μ : Measure A) (ν : ι → Measure A) [IsProbabilityMeasure μ]
    [∀ i, IsProbabilityMeasure (ν i)] :
    (Measure.infinitePi (fun i : Option ι => i.elim μ ν)).map
      (fun g => (g none,fun i => g (some i))) = μ.prod (Measure.infinitePi ν) := by
  rw [← infinitePi_option_join μ ν,Measure.map_map (by fun_prop) (by
    apply Measurable.of_eval
    intro i
    cases i <;> dsimp <;> fun_prop)]
  change (μ.prod (Measure.infinitePi ν)).map id = _
  exact Measure.map_id

lemma infinitePi_triple_curry {I J K A : Type*} [MeasurableSpace A]
    (μ : I → J → K → Measure A) [∀ i j k, IsProbabilityMeasure (μ i j k)] :
    (Measure.infinitePi (fun p : I × (J × K) => μ p.1 p.2.1 p.2.2)).map
      (fun g i j k => g (i,j,k)) =
      Measure.infinitePi (fun i => Measure.infinitePi (fun j => Measure.infinitePi (μ i j))) := by
  rw [show (fun g : (I × (J × K)) → A => fun i j k => g (i,j,k)) =
      (fun q : I → (J × K → A) => fun i j k => q i (j,k)) ∘
      (MeasurableEquiv.curry I (J × K) A) from rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop),Measure.infinitePi_map_curry
      (fun (i : I) (p : J × K) => μ i p.1 p.2)]
  rw [Measure.infinitePi_map_pi _ (f := fun (_ : I) (q : J × K → A) => fun j k => q (j,k))
    (fun _ => by fun_prop)]
  simp only [show (fun q : J × K → A => fun j k => q (j,k)) =
    MeasurableEquiv.curry J K A from rfl,Measure.infinitePi_map_curry]

@[reducible] def ForestVertex : ℕ → Type
  | 0 => PEmpty
  | n+1 => ℕ × (ℕ × Option (ForestVertex n))

instance forestVertexCountable : (n : ℕ) → Countable (ForestVertex n)
  | 0 => inferInstanceAs (Countable PEmpty)
  | n+1 => letI := forestVertexCountable n
    inferInstanceAs (Countable (ℕ × (ℕ × Option (ForestVertex n))))

def forestVertexDepth : (n : ℕ) → ForestVertex n → ℕ
  | 0, v => v.elim
  | _+1, (_,_,none) => 0
  | n+1, (_,_,some v) => forestVertexDepth n v+1

variable (A : Type) [MeasurableSpace A]

def markForestOfCoords : (n : ℕ) → (ForestVertex n → A) → MarkForest A n
  | 0, _ => PUnit.unit
  | n+1, g => fun m i => (g (m,i,none),markForestOfCoords n (fun v => g (m,i,some v)))

@[fun_prop] lemma measurable_markForestOfCoords (n : ℕ) :
    Measurable (markForestOfCoords A n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    apply Measurable.of_eval
    intro m
    apply Measurable.of_eval
    intro i
    exact (measurable_pi_apply (m,i,none)).prodMk (ih.comp (by fun_prop))

theorem markForestOfCoords_law (n : ℕ) (μ : ℕ → ProbabilityMeasure A) :
    (Measure.infinitePi (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure A))).map
      (markForestOfCoords A n) = markForestLaw A n μ := by
  induction n generalizing μ with
  | zero =>
    change (Measure.infinitePi _).map (fun _ => (PUnit.unit : PUnit)) = Measure.dirac PUnit.unit
    rw [Measure.map_const]
    simp
  | succ n ih =>
    let μ' := fun j => μ (j+1)
    let ν : ForestVertex n → Measure A := fun v => μ' (forestVertexDepth n v)
    have (i : Option (ForestVertex n)) : IsProbabilityMeasure (i.elim (μ 0 : Measure A) ν) := by
      cases i <;> dsimp <;> infer_instance
    have hi : MeasurePreserving (markForestOfCoords A n) (Measure.infinitePi ν)
        (markForestLaw A n μ') := ⟨measurable_markForestOfCoords A n,ih μ'⟩
    have hs : MeasurePreserving (fun g : Option (ForestVertex n) → A =>
        (g none,fun v => g (some v)))
        (Measure.infinitePi (fun v => v.elim (μ 0 : Measure A) ν))
        ((μ 0 : Measure A).prod (Measure.infinitePi ν)) :=
      ⟨by fun_prop,infinitePi_option_split (μ 0 : Measure A) ν⟩
    have hp := ((MeasurePreserving.id (μ 0 : Measure A)).prod hi).comp hs
    have hmap : (Measure.infinitePi (fun v : Option (ForestVertex n) =>
        v.elim (μ 0 : Measure A) ν)).map (fun g =>
          (g none,markForestOfCoords A n (fun v => g (some v)))) =
        (μ 0 : Measure A).prod (markForestLaw A n μ') := hp.map_eq
    have hc : (fun v : ForestVertex (n+1) => (μ (forestVertexDepth (n+1) v) : Measure A)) =
        (fun v : ℕ × (ℕ × Option (ForestVertex n)) => v.2.2.elim (μ 0 : Measure A) ν) := by
      funext v
      rcases v with ⟨m,i,v⟩
      cases v <;> rfl
    rw [hc]
    change (Measure.infinitePi (fun v : ℕ × (ℕ × Option (ForestVertex n)) =>
        v.2.2.elim (μ 0 : Measure A) ν)).map
        ((fun q : ℕ → ℕ → Option (ForestVertex n) → A => fun m i =>
          (q m i none,markForestOfCoords A n (fun v => q m i (some v)))) ∘
          (fun g m i v => g (m,i,v))) = _
    rw [← Measure.map_map (by fun_prop) (by fun_prop),infinitePi_triple_curry
        (fun (_ _ : ℕ) (v : Option (ForestVertex n)) => v.elim (μ 0 : Measure A) ν),
      Measure.infinitePi_map_pi _ (f := fun (_ : ℕ) (q : ℕ → Option (ForestVertex n) → A) =>
        fun i => (q i none,markForestOfCoords A n (fun v => q i (some v)))) (fun _ => by fun_prop)]
    simp_rw [Measure.infinitePi_map_pi _
        (f := fun (_ : ℕ) (g : Option (ForestVertex n) → A) =>
          (g none,markForestOfCoords A n (fun v => g (some v)))) (fun _ => hp.measurable),hmap]
    rfl

end IsingPerceptron

namespace IsingPerceptron

theorem labeledNoiseCoordinates_law (A : Type) [MeasurableSpace A] [Nonempty A]
    (n : ℕ) (b : ℕ → ℝ) (μ : ℕ → ProbabilityMeasure A) :
    ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (Measure.infinitePi (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure A)))).map
      (fun p => labeledNoiseJoin A n (p.1,markForestOfCoords A n p.2)) =
      noiseCascadeLaw A n b μ := by
  have hp := (MeasurePreserving.id (labeledCascadeLaw n b : Measure (LabeledTree n))).prod
    (show MeasurePreserving (markForestOfCoords A n)
      (Measure.infinitePi (fun v : ForestVertex n => (μ (forestVertexDepth n v) : Measure A)))
      (markForestLaw A n μ) from ⟨measurable_markForestOfCoords A n,markForestOfCoords_law A n μ⟩)
  change _ = _
  rw [show (fun p : LabeledTree n × (ForestVertex n → A) =>
      labeledNoiseJoin A n (p.1,markForestOfCoords A n p.2)) =
      (labeledNoiseJoin A n) ∘ Prod.map id (markForestOfCoords A n) from rfl,
    ← Measure.map_map (measurable_labeledNoiseJoin A n) hp.measurable,hp.map_eq,
    labeledNoiseJoin_law]

theorem labeledGaussianCoordinates_law {κ : Type} [Fintype κ]
    (n : ℕ) (b : ℕ → ℝ) :
    ((labeledCascadeLaw n b : Measure (LabeledTree n)).prod
      (Measure.infinitePi (fun _ : ForestVertex n × κ => gaussianReal 0 1))).map
      (fun p => labeledNoiseJoin (κ → ℝ) n
        (p.1,markForestOfCoords (κ → ℝ) n (fun v i => p.2 (v,i)))) =
      noiseCascadeLaw (κ → ℝ) n b (fun _ =>
        ⟨Measure.pi (fun _ : κ => gaussianReal 0 1),inferInstance⟩) := by
  let μ : ProbabilityMeasure (κ → ℝ) := ⟨Measure.pi (fun _ : κ => gaussianReal 0 1),inferInstance⟩
  have hc : MeasurePreserving (fun g : (ForestVertex n × κ) → ℝ => fun v i => g (v,i))
      (Measure.infinitePi (fun _ : ForestVertex n × κ => gaussianReal 0 1))
      (Measure.infinitePi (fun _ : ForestVertex n => (μ : Measure (κ → ℝ)))) := by
    refine ⟨by fun_prop,?_⟩
    change (Measure.infinitePi (fun _ : ForestVertex n × κ => gaussianReal 0 1)).map
      (MeasurableEquiv.curry (ForestVertex n) κ ℝ) = _
    rw [Measure.infinitePi_map_curry (fun (_ : ForestVertex n) (_ : κ) => gaussianReal 0 1)]
    simp only [Measure.infinitePi_eq_pi]
    rfl
  have hp := (MeasurePreserving.id (labeledCascadeLaw n b : Measure (LabeledTree n))).prod hc
  have hm : Measurable (fun p : LabeledTree n × (ForestVertex n → κ → ℝ) =>
      labeledNoiseJoin (κ → ℝ) n (p.1,markForestOfCoords (κ → ℝ) n p.2)) := by fun_prop
  rw [show (fun p : LabeledTree n × ((ForestVertex n × κ) → ℝ) =>
      labeledNoiseJoin (κ → ℝ) n (p.1,markForestOfCoords (κ → ℝ) n (fun v i => p.2 (v,i)))) =
      (fun p : LabeledTree n × (ForestVertex n → κ → ℝ) =>
        labeledNoiseJoin (κ → ℝ) n (p.1,markForestOfCoords (κ → ℝ) n p.2)) ∘
      Prod.map id (fun g : (ForestVertex n × κ) → ℝ => fun v i => g (v,i)) from rfl,
    ← Measure.map_map hm hp.measurable,hp.map_eq]
  exact labeledNoiseCoordinates_law (κ → ℝ) n b (fun _ => μ)

lemma labeledMarkedMeasure_lintegral {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (ω : (ℕ → ℕ × (ℕ → E)) × (ℕ → ℕ → F))
    {G : E × F → ℝ≥0∞} (hG : Measurable G) :
    (∫⁻ p, G p ∂labeledMarkedMeasure ω) =
      ∑' m, ∑ i : Fin (ω.1 m).1, G ((ω.1 m).2 i,ω.2 m i) := by
  simp only [labeledMarkedMeasure,lintegral_sum_measure,finiteCloudMeasure_lintegral _ hG]

lemma labeledMarkedMeasure_ae {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (ω : (ℕ → ℕ × (ℕ → E)) × (ℕ → ℕ → F)) {P : E × F → Prop}
    (hP : MeasurableSet {p | P p}) (h : ∀ᵐ p ∂labeledMarkedMeasure ω, P p) :
    ∀ m (i : Fin (ω.1 m).1), P ((ω.1 m).2 i,ω.2 m i) := by
  intro m i
  have hm := (Measure.ae_sum_iff.mp h) m
  rw [finiteCloudMeasure,← Measure.sum_fintype] at hm
  exact (ae_dirac_iff hP).mp ((Measure.ae_sum_iff.mp hm) i)

variable (A : Type) [MeasurableSpace A] [Nonempty A]

def labeledNoiseLeaf : (n : ℕ) → LabeledTree n × MarkForest A n → LabeledLeaf n → NoiseLeaf A n
  | 0, _, _ => PUnit.unit
  | n+1, p, v => ((p.1.1 v.1.1).2 v.1.2,
      ((p.2 v.1.1 v.1.2).1,labeledNoiseLeaf n (p.1.2 v.1.1 v.1.2,(p.2 v.1.1 v.1.2).2) v.2))

omit [Nonempty A] in
@[fun_prop] lemma measurable_labeledNoiseLeaf (n : ℕ) (v : LabeledLeaf n) :
    Measurable (fun p => labeledNoiseLeaf A n p v) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun p : (WeightCloud × (ℕ → ℕ → LabeledTree n)) ×
        (ℕ → ℕ → A × MarkForest A n) =>
      ((p.1.1 v.1.1).2 v.1.2,
        ((p.2 v.1.1 v.1.2).1,labeledNoiseLeaf A n (p.1.2 v.1.1 v.1.2,(p.2 v.1.1 v.1.2).2) v.2)))
    apply Measurable.prodMk (by fun_prop)
    apply Measurable.prodMk (by fun_prop)
    exact (ih v.2).comp (by fun_prop)

theorem labeledLeafMass_noiseMap (n : ℕ) (ω : LabeledTree n) (z : MarkForest A n)
    (hgood : GoodNoiseTree A n (labeledNoiseJoin A n (ω,z))) :
    (labeledLeafMass n ω).map (labeledNoiseLeaf A n (ω,z)) =
      noiseTreeTotal A n (labeledNoiseJoin A n (ω,z)) •
        noiseLeafKernel A n (labeledNoiseJoin A n (ω,z)) := by
  induction n with
  | zero =>
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_map' hF.aemeasurable (measurable_of_countable _).aemeasurable,
      labeledLeafMass_lintegral]
    simp [labeledLeafWeight,labeledNoiseLeaf,noiseTreeTotal,
      rawTreeTotal,noiseLeafKernel,noiseLeafKernelData,Kernel.const_apply]
  | succ n ih =>
    apply Measure.ext_of_lintegral
    intro F hF
    rw [lintegral_map' hF.aemeasurable (measurable_of_countable _).aemeasurable,
      labeledLeafMass_lintegral,lintegral_smul_measure,smul_eq_mul,
      noiseLeafKernel_unnormalized_lintegral n _ hgood.1 hF]
    have hinner : Measurable (fun p : ℝ × (A × NoiseTree A n) =>
        ∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2) :=
      (hF.comp (by fun_prop : Measurable (fun p :
        (ℝ × (A × NoiseTree A n)) × NoiseLeaf A n => (p.1.1,(p.1.2.1,p.2))))).lintegral_kernel_prod_right'
        (κ := (noiseLeafKernel A n).comap (fun p : ℝ × (A × NoiseTree A n) => p.2.2) (by fun_prop))
    have hg := labeledMarkedMeasure_ae _
      ((measurableSet_GoodNoiseTree A n).preimage (by fun_prop)) hgood.2
    change (∑' v : ChildLabel × LabeledLeaf n,
      (childLabelWeight ω.1 v.1 * labeledLeafWeight n (ω.2 v.1.1 v.1.2) v.2) *
        F ((ω.1 v.1.1).2 v.1.2,((z v.1.1 v.1.2).1,
          labeledNoiseLeaf A n (ω.2 v.1.1 v.1.2,(z v.1.1 v.1.2).2) v.2))) =
      ∫⁻ p : ℝ × (A × NoiseTree A n), ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 *
        (∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2) ∂
          labeledMarkedMeasure (ω.1,fun m i => ((z m i).1,labeledNoiseJoin A n (ω.2 m i,(z m i).2)))
    have hG : Measurable (fun p : ℝ × (A × NoiseTree A n) =>
        ENNReal.ofReal (max p.1 0) * noiseTreeTotal A n p.2.2 *
          (∫⁻ v, F (p.1,(p.2.1,v)) ∂noiseLeafKernel A n p.2.2)) :=
      ((by fun_prop : Measurable (fun p : ℝ × (A × NoiseTree A n) => ENNReal.ofReal (max p.1 0))).mul
        ((measurable_noiseTreeTotal A n).comp (measurable_snd.comp measurable_snd))).mul hinner
    rw [labeledMarkedMeasure_lintegral
      (ω.1,fun m i => ((z m i).1,labeledNoiseJoin A n (ω.2 m i,(z m i).2))) hG]
    rw [ENNReal.tsum_prod']
    simp_rw [mul_assoc,ENNReal.tsum_mul_left]
    rw [finiteCloud_tsum_weight]
    apply tsum_congr
    intro m
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    have he := ih (ω.2 m i) (z m i).2 (hg m i)
    have hFi : Measurable (fun v : NoiseLeaf A n => F ((ω.1 m).2 i,((z m i).1,v))) := by fun_prop
    have hh := congrArg (fun ν : Measure (NoiseLeaf A n) => ∫⁻ v, F ((ω.1 m).2 i,((z m i).1,v)) ∂ν) he
    rw [lintegral_map' hFi.aemeasurable (measurable_of_countable _).aemeasurable,
      labeledLeafMass_lintegral,lintegral_smul_measure,smul_eq_mul] at hh
    exact hh

theorem labeledLeafLaw_noiseMap (n : ℕ) (ω : LabeledTree n) (z : MarkForest A n)
    (hgood : GoodNoiseTree A n (labeledNoiseJoin A n (ω,z)))
    (ht : 0 < noiseTreeTotal A n (labeledNoiseJoin A n (ω,z)) ∧
      noiseTreeTotal A n (labeledNoiseJoin A n (ω,z)) < ∞) :
    (labeledLeafLaw n ω).map (labeledNoiseLeaf A n (ω,z)) =
      noiseLeafKernel A n (labeledNoiseJoin A n (ω,z)) := by
  have hm := labeledLeafMass_noiseMap A n ω z hgood
  have htot : labeledLeafMass n ω Set.univ = noiseTreeTotal A n (labeledNoiseJoin A n (ω,z)) := by
    have he := congrArg (fun ν : Measure (NoiseLeaf A n) => ν Set.univ) hm
    simpa only [Measure.map_apply_of_aemeasurable (measurable_of_countable _).aemeasurable MeasurableSet.univ,
      Set.preimage_univ,Measure.smul_apply,smul_eq_mul,measure_univ,mul_one] using he
  rw [labeledLeafLaw,normalizeMass_map _ (measurable_of_countable _) (by simpa only [htot] using ht),
    hm,normalizeMass_smul _ ht (by simp),normalizeMass_of_probability]

end IsingPerceptron

end

end OAI
