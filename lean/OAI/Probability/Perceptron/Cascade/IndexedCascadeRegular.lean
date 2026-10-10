import Mathlib
import OAI.Probability.Perceptron.Cascade.IndexedMarkedPoisson

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

lemma indexedPoissonMeasure_lintegral {A : Type*} [MeasurableSpace A]
    (a : ℕ → ℕ × (ℕ → A)) {f : A → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f x ∂indexedPoissonMeasure a) =
      ∑' i, ∑ j : Fin ((a i).1), f ((a i).2 j.val) := by
  simp only [indexedPoissonMeasure,indexedFiniteCloud,finitePointMeasure,
    lintegral_sum_measure,lintegral_finsetSum_measure,lintegral_dirac' _ hf]

def indexedCascadeRootMass {n : ℕ} (b : IndexedCascadeBase (n+1)) : ℝ≥0∞ :=
  markedStableTotalE (indexedPoissonMeasure b)

lemma indexedCascadeRootMass_measurable (n : ℕ) :
    Measurable (indexedCascadeRootMass (n := n)) :=
  markedStableTotalE_measurable.comp indexedPoissonMeasure_measurable

lemma indexedCascadeRealize_rootMass {S : Type} [MeasurableSpace S] (n : ℕ)
    (b : IndexedCascadeBase (n+1)) (m : IndexedCascadeMarks S (n+1)) :
    markedStableTotalE (indexedCascadeRealize (n+1) (b,m)) = indexedCascadeRootMass b := by
  unfold indexedCascadeRealize indexedCascadeRootMass markedStableTotalE
  rw [indexedPoissonMeasure_lintegral _ (by fun_prop),indexedPoissonMeasure_lintegral _ (by fun_prop)]

def IndexedCascadeGood : (n : ℕ) → IndexedCascadeBase n → Prop
  | 0,_ => True
  | n+1,b => 0 < (indexedCascadeRootMass b).toReal ∧
      ∀ i j : ℕ, IndexedCascadeGood n (((b i).2 j).2)

lemma indexedCascadeBase_child_law (n : ℕ) (z : Fin (n+1) → ℝ) (i j : ℕ) :
    MeasurePreserving (fun b : IndexedCascadeBase (n+1) => (((b i).2 j).2))
      (indexedCascadeBaseLaw (n+1) z) (indexedCascadeBaseLaw n (fun l => z l.succ)) := by
  let B := (indexedCascadeBaseLaw n (fun l => z l.succ) : Measure (IndexedCascadeBase n))
  let ρ := fun i => finiteIntensityMarks (sfiniteSeq (stableLogIntensity (z 0)) i)
  let r := fun i => ((sfiniteSeq (stableLogIntensity (z 0)) i) univ).toNNReal
  exact (measurePreserving_snd (μ := ρ i) (ν := B)).comp
    ((measurePreserving_eval_infinitePi (fun _ : ℕ => (ρ i).prod B) j).comp
      ((measurePreserving_snd (μ := poissonMeasure (r i))
        (ν := Measure.infinitePi (fun _ : ℕ => (ρ i).prod B))).comp
          (measurePreserving_eval_infinitePi (fun i => (poissonMeasure (r i)).prod
            (Measure.infinitePi (fun _ : ℕ => (ρ i).prod B))) i)))

lemma indexedCascadeRootMass_pos (n : ℕ) (z : Fin (n+1) → ℝ)
    (hz0 : 0 < z 0) (hz1 : z 0 < 1) :
    ∀ᵐ b ∂(indexedCascadeBaseLaw (n+1) z : Measure (IndexedCascadeBase (n+1))),
      0 < (indexedCascadeRootMass b).toReal := by
  let B := (indexedCascadeBaseLaw n (fun l => z l.succ) : Measure (IndexedCascadeBase n))
  let κ := stableLogIntensity (z 0)
  have hl : (indexedCascadeBaseLaw (n+1) z : Measure (IndexedCascadeBase (n+1))).map
      indexedPoissonMeasure = poissonRandomMeasureLaw (κ.prod B) := by
    change (Measure.infinitePi (fun i => (poissonMeasure (((sfiniteSeq κ i) univ).toNNReal)).prod
      (Measure.infinitePi (fun _ : ℕ => (finiteIntensityMarks (sfiniteSeq κ i)).prod B)))).map
        indexedPoissonMeasure = _
    rw [indexedPoissonMeasure_law,countablePoissonLaw_product_intensity]
  have hreg := (markedStable_regular B hz0 hz1).mono fun η hη => hη.2
  rw [← hl] at hreg
  exact (ae_map_iff indexedPoissonMeasure_measurable.aemeasurable
    (measurableSet_lt measurable_const markedStableTotal_measurable)).mp hreg

lemma indexedCascadeGood_ae (n : ℕ) (z : Fin n → ℝ)
    (hz0 : ∀ i, 0 < z i) (hz1 : ∀ i, z i < 1) :
    ∀ᵐ b ∂(indexedCascadeBaseLaw n z : Measure (IndexedCascadeBase n)), IndexedCascadeGood n b := by
  induction n with
  | zero => exact ae_of_all _ fun _ => trivial
  | succ n ih =>
    have ht (i j : ℕ) : ∀ᵐ b ∂(indexedCascadeBaseLaw (n+1) z : Measure (IndexedCascadeBase (n+1))),
        IndexedCascadeGood n (((b i).2 j).2) :=
      (indexedCascadeBase_child_law n z i j).quasiMeasurePreserving.ae
        (ih (fun l => z l.succ) (fun l => hz0 l.succ) (fun l => hz1 l.succ))
    filter_upwards [indexedCascadeRootMass_pos n z (hz0 0) (hz1 0),
      ae_all_iff.mpr (fun i => ae_all_iff.mpr (ht i))] with b hb ht
    exact ⟨hb,ht⟩

lemma indexedCascadeGood_countKernel {S : Type} [MeasurableSpace S] {n : ℕ}
    {b : IndexedCascadeBase (n+1)} (hb : IndexedCascadeGood (n+1) b)
    (m : IndexedCascadeMarks S (n+1)) :
    markedStableCountKernel (indexedCascadeRealize (n+1) (b,m)) =
      indexedCascadeRealize (n+1) (b,m) := by
  apply markedStableCountKernel_eq
  · rw [indexedCascadeRealize_rootMass]
    exact (ENNReal.toReal_pos_iff.mp hb.1).2.ne
  · change 0 < (markedStableTotalE (indexedCascadeRealize (n+1) (b,m))).toReal
    rw [indexedCascadeRealize_rootMass]
    exact hb.1

@[reducible] def IndexedLeaf : ℕ → MeasCat
  | 0 => MeasCat.of Unit
  | n+1 => MeasCat.of (ℕ × ℕ × IndexedLeaf n)

instance indexedLeaf_countable (n : ℕ) : Countable (IndexedLeaf n) := by
  induction n with
  | zero => dsimp [IndexedLeaf]; infer_instance
  | succ n ih => dsimp [IndexedLeaf]; infer_instance

instance indexedLeaf_nonempty (n : ℕ) : Nonempty (IndexedLeaf n) := by
  induction n with
  | zero => exact ⟨()⟩
  | succ n ih => dsimp [IndexedLeaf]; infer_instance

instance indexedLeaf_measurableSingleton (n : ℕ) : MeasurableSingletonClass (IndexedLeaf n) := by
  induction n with
  | zero => dsimp [IndexedLeaf]; infer_instance
  | succ n ih => dsimp [IndexedLeaf]; infer_instance

def indexedLeafWeight : (n : ℕ) → IndexedCascadeBase n → IndexedLeaf n → ℝ≥0
  | 0,_,_ => 1
  | n+1,b,l => if l.2.1 < (b l.1).1 then
      (Real.exp (((b l.1).2 l.2.1).1)).toNNReal *
        indexedLeafWeight n (((b l.1).2 l.2.1).2) l.2.2 else 0

lemma indexedLeafWeight_measurable (n : ℕ) :
    Measurable (Function.uncurry (indexedLeafWeight n)) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    apply measurable_from_prod_countable_left
    intro l
    change Measurable (fun b : ℕ → ℕ × (ℕ → ℝ × IndexedCascadeBase n) =>
      if l.2.1 < (b l.1).1 then (Real.exp (((b l.1).2 l.2.1).1)).toNNReal *
        indexedLeafWeight n (((b l.1).2 l.2.1).2) l.2.2 else 0)
    apply Measurable.ite (measurableSet_lt measurable_const (by fun_prop))
    · exact (by fun_prop : Measurable (fun b : ℕ → ℕ × (ℕ → ℝ × IndexedCascadeBase n) =>
          (Real.exp (((b l.1).2 l.2.1).1)).toNNReal)).mul
        (ih.comp (show Measurable (fun b : ℕ → ℕ × (ℕ → ℝ × IndexedCascadeBase n) =>
          ((((b l.1).2 l.2.1).2),l.2.2)) from by fun_prop))
    · exact measurable_const

def indexedLeafMeasure (n : ℕ) (b : IndexedCascadeBase n) : Measure (IndexedLeaf n) :=
  Measure.sum (fun l => (indexedLeafWeight n b l : ℝ≥0∞) • Measure.dirac l)

instance indexedLeafMeasure_sfinite (n : ℕ) (b : IndexedCascadeBase n) :
    SFinite (indexedLeafMeasure n b) := by
  unfold indexedLeafMeasure
  infer_instance

lemma indexedLeafMeasure_measurable (n : ℕ) : Measurable (indexedLeafMeasure n) := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [indexedLeafMeasure,Measure.sum_apply _ hs,Measure.smul_apply]
  apply Measurable.tsum
  intro l
  exact (((indexedLeafWeight_measurable n).comp (measurable_id.prodMk measurable_const)).coe_nnreal_ennreal).mul_const _

lemma indexedLeafMeasure_lintegral (n : ℕ) (b : IndexedCascadeBase n) (f : IndexedLeaf n → ℝ≥0∞) :
    (∫⁻ l, f l ∂indexedLeafMeasure n b) = ∑' l, (indexedLeafWeight n b l : ℝ≥0∞)*f l := by
  simp only [indexedLeafMeasure,lintegral_sum_measure,lintegral_smul_measure,lintegral_dirac,smul_eq_mul]

lemma indexedLeafMeasure_lintegral_succ (n : ℕ) (b : IndexedCascadeBase (n+1))
    (f : IndexedLeaf (n+1) → ℝ≥0∞) :
    (∫⁻ l, f l ∂indexedLeafMeasure (n+1) b) =
      ∑' i, ∑ j : Fin ((b i).1), ENNReal.ofReal (Real.exp (((b i).2 j.val).1))*
        ∫⁻ l, f (i,j.val,l) ∂indexedLeafMeasure n (((b i).2 j.val).2) := by
  rw [indexedLeafMeasure_lintegral]
  change (∑' l : ℕ × ℕ × IndexedLeaf n, (indexedLeafWeight (n+1) b l : ℝ≥0∞)*f l) = _
  rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro i
  rw [ENNReal.tsum_prod']
  have he (j : ℕ) : (∑' l : IndexedLeaf n,
      (indexedLeafWeight (n+1) b (i,j,l) : ℝ≥0∞)*f (i,j,l)) =
      if j < (b i).1 then ENNReal.ofReal (Real.exp (((b i).2 j).1))*
        (∫⁻ l, f (i,j,l) ∂indexedLeafMeasure n (((b i).2 j).2)) else 0 := by
    by_cases hj : j < (b i).1
    · simp only [indexedLeafWeight,ite_eq_left hj,ENNReal.coe_mul]
      change (∑' l : IndexedLeaf n, ENNReal.ofReal (Real.exp (((b i).2 j).1)) *
        (indexedLeafWeight n (((b i).2 j).2) l : ℝ≥0∞)*f (i,j,l)) = _
      rw [indexedLeafMeasure_lintegral,← ENNReal.tsum_mul_left]
      exact tsum_congr (fun l => mul_assoc _ _ _)
    · simp [indexedLeafWeight,hj]
  simp_rw [he]
  rw [tsum_eq_sum (s := Finset.range ((b i).1)) (fun j hj => by simp [Finset.mem_range.not.mp hj])]
  rw [Fin.sum_univ_eq_sum_range (fun j => ENNReal.ofReal (Real.exp (((b i).2 j).1)) *
    ∫⁻ l, f (i,j,l) ∂indexedLeafMeasure n (((b i).2 j).2))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [ite_eq_left (Finset.mem_range.mp hj)]

def indexedLeafState {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    (step : X × S → X) : (n : ℕ) → X × IndexedCascadeMarks S n → IndexedLeaf n → X
  | 0,p,_ => p.1
  | n+1,p,l => indexedLeafState step n (step (p.1,(p.2 l.1 l.2.1).1),
      (p.2 l.1 l.2.1).2) l.2.2

lemma indexedLeafState_measurable {X S : Type} [MeasurableSpace X] [MeasurableSpace S]
    {step : X × S → X} (hs : Measurable step) (n : ℕ) :
    Measurable (Function.uncurry (indexedLeafState step n)) := by
  induction n with
  | zero => exact measurable_fst.fst
  | succ n ih =>
    apply measurable_from_prod_countable_left
    intro l
    change Measurable (fun p : X × (ℕ → ℕ → S × IndexedCascadeMarks S n) =>
      indexedLeafState step n (step (p.1,(p.2 l.1 l.2.1).1),(p.2 l.1 l.2.1).2) l.2.2)
    exact ih.comp (show Measurable (fun p : X × (ℕ → ℕ → S × IndexedCascadeMarks S n) =>
      ((step (p.1,(p.2 l.1 l.2.1).1),(p.2 l.1 l.2.1).2),l.2.2)) from by fun_prop)

end SphericalPerceptronFreeEnergy

end

end OAI
