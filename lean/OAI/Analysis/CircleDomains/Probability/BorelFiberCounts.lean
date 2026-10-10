import OAI.Analysis.CircleDomains.Probability.HausdorffZeroCounting
import OAI.Analysis.CircleDomains.Probability.AnalyticFiniteMeasurability
import Mathlib.MeasureTheory.Measure.WithDensityFinite

namespace OAI

/-! Finite distinct-point witnesses make fiber counts universally
measurable. The image of each Borel configuration space is analytic. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology Classical
noncomputable section
namespace CircleDomainRigidity

def pointCount {X : Type*} (S : Set X) : ℝ≥0∞ :=
  ∑' x, if x ∈ S then 1 else 0

def finitePointWitness {X : Type*} (S : Set X) (n : ℕ) : Prop :=
  ∃ g : Fin n → X, Injective g ∧ ∀ i, g i ∈ S

lemma pointCount_eq_iSup {X : Type*} (S : Set X) :
    pointCount S = ⨆ n : ℕ, if finitePointWitness S n then (n : ℝ≥0∞) else 0 := by
  classical
  apply le_antisymm
  · rw [pointCount, ENNReal.tsum_eq_iSup_sum]
    apply iSup_le
    intro F
    let E := F.filter (· ∈ S)
    let e : Fin (Fintype.card E) ≃ E := (Fintype.equivFin E).symm
    have hw : finitePointWitness S (Fintype.card E) :=
      ⟨fun i => (e i).val, Subtype.val_injective.comp e.injective,
        fun i => (Finset.mem_filter.mp (e i).property).2⟩
    have hn : (Fintype.card E : ℝ≥0∞) ≤ ⨆ n : ℕ,
        if finitePointWitness S n then (n : ℝ≥0∞) else 0 :=
      (ite_eq_left hw).symm.le.trans (le_iSup
        (fun n : ℕ => if finitePointWitness S n then (n : ℝ≥0∞) else 0) _)
    simpa only [Finset.sum_boole, Fintype.card_coe] using hn
  · apply iSup_le
    intro n
    split_ifs with hn
    · obtain ⟨g, hg, hS⟩ := hn
      calc
        (n : ℝ≥0∞) = ∑' i : Fin n, if g i ∈ S then (1 : ℝ≥0∞) else 0 := by
          simp only [hS, ite_true, tsum_fintype, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, mul_one]
        _ ≤ pointCount S := ENNReal.tsum_comp_le_tsum_of_injective hg
          (fun x => if x ∈ S then (1 : ℝ≥0∞) else 0)
    · exact zero_le

lemma pointCount_eq_hausdorff_zero {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {S : Set X} (hS : MeasurableSet S) :
    pointCount S = (μH[0] : Measure X) S := by
  rw [hausdorff_zero_eq_count, Measure.count_apply hS]
  exact (tsum_subtype S (fun _ => (1 : ℝ≥0∞))).symm.trans (ENNReal.tsum_set_one S)

lemma nullMeasurableSet_analytic_sfinite {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [SFinite μ]
    {A : Set X} (hA : AnalyticSet A) : NullMeasurableSet A μ := by
  have h := nullMeasurableSet_analytic_finite μ.toFinite hA
  change EventuallyMeasurableSet _ (ae μ) A
  change EventuallyMeasurableSet _ (ae μ.toFinite) A at h
  rcases h with ⟨B, hB, hBA⟩
  refine ⟨B, hB, ?_⟩
  simpa only [ae_toFinite] using hBA

lemma analytic_finite_fiber_witness
    {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {A : Set X} (hA : MeasurableSet A) {f : X → Y} (hf : Continuous f) (n : ℕ) :
    AnalyticSet {y | finitePointWitness (A ∩ f ⁻¹' {y}) n} := by
  let C : Set ((Fin n → X) × Y) := {p | Injective p.1 ∧
    (∀ i, p.1 i ∈ A) ∧ ∀ i, f (p.1 i) = p.2}
  have hci : MeasurableSet {p : (Fin n → X) × Y | Injective p.1} := by
    simp only [Injective, ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    by_cases hij : i = j
    · simp only [hij, implies_true, ofPred_true, MeasurableSet.univ]
    · simpa only [hij, imp_false, compl_ofPred] using
        (isClosed_eq (by fun_prop : Continuous (fun p : (Fin n → X) × Y => p.1 i))
          (by fun_prop : Continuous (fun p : (Fin n → X) × Y => p.1 j))).measurableSet.compl
  have hca : MeasurableSet {p : (Fin n → X) × Y | ∀ i, p.1 i ∈ A} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter (fun i => hA.preimage (by fun_prop))
  have hcf : MeasurableSet {p : (Fin n → X) × Y | ∀ i, f (p.1 i) = p.2} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter (fun i => (isClosed_eq
      (hf.comp (by fun_prop)) continuous_snd).measurableSet)
  have hc : MeasurableSet C := hci.inter (hca.inter hcf)
  have heq : Prod.snd '' C = {y | finitePointWitness (A ∩ f ⁻¹' {y}) n} := by
    ext y
    constructor
    · rintro ⟨⟨g, y⟩, hg, rfl⟩
      exact ⟨g, hg.1, fun i => ⟨hg.2.1 i, hg.2.2 i⟩⟩
    · rintro ⟨g, hg, hmem⟩
      exact ⟨(g, y), ⟨hg, (fun i => (hmem i).1), fun i => (hmem i).2⟩, rfl⟩
  rw [← heq]
  exact hc.analyticSet.image_of_continuous continuous_snd

lemma aemeasurable_hausdorff_zero_fiber
    {X Y : Type*} [MetricSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [MetricSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {A : Set X} (hA : MeasurableSet A) {f : X → Y} (hf : Continuous f)
    (μ : Measure Y) [SFinite μ] :
    AEMeasurable (fun y => (μH[0] : Measure X) (A ∩ f ⁻¹' {y})) μ := by
  have heq : (fun y => (μH[0] : Measure X) (A ∩ f ⁻¹' {y})) =
      fun y => ⨆ n : ℕ, if finitePointWitness (A ∩ f ⁻¹' {y}) n then (n : ℝ≥0∞) else 0 := by
    funext y
    rw [← pointCount_eq_hausdorff_zero (hA.inter (hf.measurable (measurableSet_singleton y))),
      pointCount_eq_iSup]
  rw [heq]
  apply NullMeasurable.aemeasurable
  change @Measurable (NullMeasurableSpace Y μ) ℝ≥0∞ _ _ _
  apply Measurable.iSup
  intro n
  exact Measurable.ite (nullMeasurableSet_analytic_sfinite μ
    (analytic_finite_fiber_witness hA hf n)) measurable_const measurable_const

end CircleDomainRigidity

end

end OAI
