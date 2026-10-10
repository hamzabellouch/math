import Mathlib
import OAI.Probability.SKRatio.Matrices.PlantedGOE
import OAI.Probability.SKRatio.Matrices.WeightedDiagonalSquares

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open SKRatioClock.Regression MatrixNet
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma continuous_affineDisorder (β : ℝ) : Continuous (affineDisorder (n := n) β) := by
  unfold affineDisorder
  fun_prop

lemma diagonal_affine_hasLaw (hn : 0<n) (β : ℝ) (μ : Measure (Fin n → ℝ)) [SFinite μ] :
    HasLaw (fun p : (Fin n → ℝ) × Disorder n => (p.1,affineDisorder β p.2))
      (μ.prod (law β n)) (μ.prod (standardArrayLaw (Edge n))) := by
  refine ⟨(continuous_fst.prodMk ((continuous_affineDisorder β).comp continuous_snd)).aemeasurable,?_⟩
  change Measure.map (Prod.map id (affineDisorder β)) _ = _
  rw [←Measure.map_prod_map μ _ measurable_id (continuous_affineDisorder β).measurable,
    Measure.map_id,(affineDisorder_hasLaw hn β).map_eq]

def diagonalSquareError {X : Type*} (β : ℝ) (G : X × X → ℝ) (b : ℝ → X)
    (p : (Fin n → ℝ) × Disorder n) (i : Fin n) : ℝ :=
  ∑ e : incidentEdges i, (p.2 e^2-β^2/(n:ℝ))*
    G (b (diagonalField p.1 p.2 i),b (diagonalField p.1 p.2 (otherEnd i e)))

lemma continuous_diagonalSquareError {X : Type*} [TopologicalSpace X]
    (β : ℝ) {G : X × X → ℝ} (hG : Continuous G) {b : ℝ → X} (hb : Continuous b)
    (i : Fin n) : Continuous (fun p => diagonalSquareError β G b p i) := by
  apply continuous_finsetSum
  intro e _
  apply Continuous.mul (by fun_prop)
  exact hG.comp ((hb.comp (continuous_diagonalField i)).prodMk
    (hb.comp (continuous_diagonalField (otherEnd i e))))

lemma diagonal_square_event_measurable {X : Type*} [TopologicalSpace X]
    (β : ℝ) {G : X × X → ℝ} (hG : Continuous G) {b : ℝ → X} (hb : Continuous b)
    (u : ℝ) : MeasurableSet {p : (Fin n → ℝ) × Disorder n |
      ∃ i, u < |diagonalSquareError β G b p i|} := by
  simp only [ofPred_exists]
  exact MeasurableSet.iUnion (fun i => isOpen_lt continuous_const
    (continuous_diagonalSquareError β hG hb i).abs |>.measurableSet)

theorem planted_weighted_diagonal_rare {X : Type} [PseudoMetricSpace X] [CompactSpace X]
    (G : X × X → ℝ) (hG : Continuous G) (b : ℝ → X) {K : ℝ≥0} (hb : LipschitzWith K b)
    (β : ℝ) (μ : ∀ n, Measure (Fin n → ℝ)) [∀ n, IsProbabilityMeasure (μ n)]
    {u : ℝ} (hu : 0<u) :
    ExponentiallyRare (fun n => (μ n).prod (law β n))
      (fun n => {p | ∃ i : Fin n, u < |diagonalSquareError β G b p i|}) := by
  obtain ⟨C,c,hC,hc,ht⟩ := continuous_weighted_diagonal_rare G hG b hb β μ hu
  refine ⟨C,c,hC,hc,?_⟩
  filter_upwards [ht,eventually_gt_atTop 0] with n hn hn0
  rw [←(diagonal_affine_hasLaw hn0 β (μ n)).measure_eq
    (diagonal_square_event_measurable β hG hb.continuous u)]
  refine (measure_mono ?_).trans hn
  rintro p ⟨i,hi⟩
  exact ⟨i,b (diagonalField p.1 (affineDisorder β p.2) i),hi⟩

def augmentedDiagonal (β : ℝ) (g : (Fin n × Fin n) → ℝ) : Fin n → ℝ :=
  fun i => augmented β g i i

lemma augmentedPair_gaussian (β : ℝ) :
    HasGaussianLaw (fun g : (Fin n × Fin n) → ℝ =>
      (augmentedDiagonal β g,augmentedDisorder β g)) (standardArrayLaw (Fin n × Fin n)) := by
  let L : ((Fin n × Fin n) → ℝ) →L[ℝ] ((Fin n → ℝ) × Disorder n) :=
    (β • ContinuousLinearMap.pi (fun i : Fin n => (entryCLM i i).comp (goeCLM n))).prod
      (β • ContinuousLinearMap.pi (fun e : Edge n => (entryCLM e.1.1 e.1.2).comp (goeCLM n)))
  let c := ((fun _ : Fin n => β^2/(n:ℝ)),(fun _ : Edge n => β^2/(n:ℝ)))
  have hL := coordinates_gaussian.map_fun L
  have h : HasGaussianLaw (fun g => L g+c) (standardArrayLaw (Fin n × Fin n)) := by
    have := hL.isGaussian_map
    refine ⟨by fun_prop, ?_⟩
    change IsGaussian ((standardArrayLaw (Fin n × Fin n)).map ((fun x => x+c) ∘ L))
    rw [← AEMeasurable.map_map_of_aemeasurable
      (by fun_prop : AEMeasurable (fun x => x+c) ((standardArrayLaw (Fin n × Fin n)).map L)) hL.aemeasurable]
    infer_instance
  apply h.congr
  exact Eventually.of_forall (fun g => by
    ext x <;> simp [L,c,entryCLM_apply,goeCLM_apply,augmented,augmentedDiagonal,augmentedDisorder])

lemma augmentedDiagonal_independent (hn : 0<n) (β : ℝ) :
    IndepFun (augmentedDiagonal (n := n) β) (augmentedDisorder β)
      (standardArrayLaw (Fin n × Fin n)) := by
  apply (augmentedPair_gaussian β).indepFun_of_covariance_eval
  intro i e
  change cov[fun g => augmented β g i i,fun g => augmented β g e.1.1 e.1.2;
    standardArrayLaw (Fin n × Fin n)] = 0
  rw [augmented_covariance hn]
  have h1 : ¬(i=e.1.1 ∧ i=e.1.2) := by rintro ⟨rfl,h⟩; exact (ne_of_lt e.2) h
  have h2 : ¬(i=e.1.2 ∧ i=e.1.1) := by rintro ⟨h,rfl⟩; exact (ne_of_lt e.2) h
  simp only [ite_eq_right h1,ite_eq_right h2,add_zero,mul_zero]

def diagonalLaw (β : ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  (standardArrayLaw (Fin n × Fin n)).map (augmentedDiagonal β)

lemma continuous_augmentedDiagonal (β : ℝ) : Continuous (augmentedDiagonal (n := n) β) := by
  unfold augmentedDiagonal augmented goe
  fun_prop

instance diagonalLaw_probability (β : ℝ) : IsProbabilityMeasure (diagonalLaw β n) :=
  (Measure.isProbabilityMeasure_map_iff (continuous_augmentedDiagonal β).aemeasurable).2
    inferInstance

lemma augmentedPair_hasLaw (hn : 0<n) (β : ℝ) :
    HasLaw (fun g : (Fin n × Fin n) → ℝ => (augmentedDiagonal β g,augmentedDisorder β g))
      ((diagonalLaw β n).prod (law β n)) (standardArrayLaw (Fin n × Fin n)) :=
  (augmentedDiagonal_independent hn β).hasLaw_prod
    ⟨(continuous_augmentedDiagonal β).aemeasurable,rfl⟩ (augmentedDisorder_hasLaw hn β)

lemma diagonalField_augmented (β : ℝ) (g : (Fin n × Fin n) → ℝ) (i : Fin n) :
    diagonalField (augmentedDiagonal β g) (augmentedDisorder β g) i = augmentedField β g i := by
  have h := coupling_augmentedDisorder β g
  change augmented β g i i+∑ j, coupling (augmentedDisorder β g) i j = _
  simp_rw [show coupling (augmentedDisorder β g) = fun i j =>
    augmented β g i j - Matrix.diagonal (fun k => augmented β g k k) i j from h]
  simp [Finset.sum_sub_distrib,Matrix.diagonal_apply,augmentedField]

theorem augmented_weighted_diagonal_rare {X : Type} [PseudoMetricSpace X] [CompactSpace X]
    (G : X × X → ℝ) (hG : Continuous G) (b : ℝ → X) {K : ℝ≥0} (hb : LipschitzWith K b)
    (β : ℝ) {u : ℝ} (hu : 0<u) :
    ExponentiallyRare (fun n => standardArrayLaw (Fin n × Fin n))
      (fun n => {g | ∃ i : Fin n, u < |∑ e : incidentEdges i,
        (augmentedDisorder β g e^2-β^2/(n:ℝ))*
          G (b (augmentedField β g i),b (augmentedField β g (otherEnd i e)))|}) := by
  obtain ⟨C,c,hC,hc,ht⟩ := planted_weighted_diagonal_rare G hG b hb β (diagonalLaw β) hu
  refine ⟨C,c,hC,hc,?_⟩
  filter_upwards [ht,eventually_gt_atTop 0] with n hn hn0
  have hl := (augmentedPair_hasLaw hn0 β).measure_eq
    (diagonal_square_event_measurable β hG hb.continuous u)
  simpa only [diagonalSquareError,diagonalField_augmented] using hl.le.trans hn

end SKRatio.Planted

end
end

end OAI
