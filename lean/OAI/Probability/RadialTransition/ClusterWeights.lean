import OAI.Probability.RadialTransition.ConvolutionFock

namespace OAI

universe uX uM uY uZ

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition
attribute [local instance] Classical.propDecidable

lemma configurationMultiset_card {X : Type uX} {ι : Type} [Fintype ι] (x : ι → X) :
    (configurationMultiset x).card = Fintype.card ι := by
  rw [configurationMultiset_val, Multiset.card_map]
  exact Finset.card_univ

lemma configurationMultiset_sum_map {X : Type uX} {M : Type uM} [AddCommMonoid M] {ι : Type} [Fintype ι]
    (x : ι → X) (f : X → M) : ((configurationMultiset x).map f).sum = ∑ i, f (x i) := by
  rw [configurationMultiset_val, Multiset.map_map]
  rfl

lemma configurationMultiset_prod_map {X : Type uX} {M : Type uM} [CommMonoid M] {ι : Type} [Fintype ι]
    (x : ι → X) (f : X → M) : ((configurationMultiset x).map f).prod = ∏ i, f (x i) := by
  rw [configurationMultiset_val, Multiset.map_map]
  rfl

def nearCube (r : ℝ) (x : Position) : Set Position :=
  {y | ∀ k, |y k-x k| ≤ r}

def nearMask (r : ℝ) (x y : Position) : ℝ≥0∞ := (nearCube r x).indicator (fun _ => 1) y

def regionMask (A : Set Position) (x : Position) : ℝ≥0∞ := A.indicator (fun _ => 1) x

def starWeight (A : Set Position) (r : ℝ) (s : Multiset Position) : ℝ≥0∞ :=
  (s.map (fun x => regionMask A x * (s.map (nearMask r x)).prod)).sum

def emptyWeight {X : Type uX} (s : Multiset X) : ℝ≥0∞ := if s.card = 0 then 1 else 0

def cellClusterWeight (t α r : ℝ) (k : Cell) (s : Multiset Position) : ℝ≥0∞ :=
  emptyWeight s + if s.card ≤ 4 then ENNReal.ofReal (Real.exp (-t*α))*starWeight (gridRegion k) r s else 0

lemma measurable_regionMask {A : Set Position} (hA : MeasurableSet A) : Measurable (regionMask A) :=
  measurable_const.indicator hA

lemma measurable_nearMask (r : ℝ) : Measurable (Function.uncurry (nearMask r)) := by
  have hs : MeasurableSet {p : Position × Position | ∀ k, |p.2 k-p.1 k| ≤ r} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro k
    exact measurableSet_le (((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) k).comp continuous_snd).sub
      ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) k).comp continuous_fst)).abs.measurable measurable_const
  exact measurable_const.indicator hs

lemma measurable_multiset_prod {Y : Type uY} {Z : Type uZ} [MeasurableSpace Y]
    (s : Multiset Z) (f : Z → Y → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    Measurable (fun x => (s.map (fun i => f i x)).prod) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact measurable_mul.comp ((hf a).prodMk ih)

lemma measurable_starWeight {A : Set Position} (hA : MeasurableSet A) (r : ℝ) :
    MeasurableConfiguration (starWeight A r) := by
  intro s ι _
  classical
  have hprod (a : (ι → Position) → Position) (ha : Measurable a) :
      Measurable (fun y => ((s+configurationMultiset y).map (nearMask r (a y))).prod) := by
    simp only [Multiset.map_add, Multiset.prod_add, configurationMultiset_prod_map]
    apply Measurable.mul
    · apply measurable_multiset_prod
      intro v
      exact (measurable_nearMask r).comp (ha.prodMk measurable_const)
    · apply Finset.measurable_prod
      intro i _
      exact (measurable_nearMask r).comp (ha.prodMk (measurable_pi_apply i))
  have he (x : ι → Position) : starWeight A r (s+configurationMultiset x) =
      (s.map (fun a => regionMask A a * ((s+configurationMultiset x).map (nearMask r a)).prod)).sum +
      ∑ i, regionMask A (x i) * ((s+configurationMultiset x).map (nearMask r (x i))).prod := by
    unfold starWeight
    rw [Multiset.map_add, Multiset.sum_add, configurationMultiset_sum_map]
  simp_rw [he]
  apply Measurable.add
  · apply measurable_multiset_sum
    intro a
    exact measurable_const.mul (hprod (fun _ => a) measurable_const)
  · apply Finset.measurable_sum
    intro i _
    exact ((measurable_regionMask hA).comp (measurable_pi_apply i)).mul
      (hprod (fun x => x i) (measurable_pi_apply i))

lemma measurable_emptyWeight {X : Type uX} [MeasurableSpace X] :
    MeasurableConfiguration (emptyWeight (X := X)) := by
  intro s ι _
  simp only [emptyWeight, Multiset.card_add, configurationMultiset_card]
  exact measurable_const

lemma measurable_cellClusterWeight (t α r : ℝ) (k : Cell) :
    MeasurableConfiguration (cellClusterWeight t α r k) := by
  intro s ι _
  simp only [cellClusterWeight, Multiset.card_add, configurationMultiset_card]
  split_ifs
  · exact (measurable_emptyWeight s ι).add (measurable_const.mul (measurable_starWeight (measurableSet_gridRegion k) r s ι))
  · exact (measurable_emptyWeight s ι).add measurable_const

end RadialTransition
end

end OAI
