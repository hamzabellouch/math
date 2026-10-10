import Mathlib
import OAI.Probability.Perceptron.Cascade.IndexedCascadeRegular

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma injective_of_simple_count_map {I A : Type*} [Countable I]
    [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (p : I → A) (hp : Measurable p)
    (hs : ∀ᵐ x ∂(Measure.count.map p), (Measure.count.map p) {x} = 1) :
    Function.Injective p := by
  classical
  have h : ∀ i, (Measure.count.map p) {p i} = 1 :=
    Measure.ae_count_iff.mp (ae_of_ae_map hp.aemeasurable hs)
  intro i j hij
  by_contra hn
  have hle : (Measure.count : Measure I) {i,j} ≤ 1 := by
    rw [← h i,Measure.map_apply hp (measurableSet_singleton _)]
    apply measure_mono
    intro k hk
    rcases hk with rfl | hk
    · rfl
    · simpa only [mem_singleton_iff] using hk ▸ hij.symm
  have htwo : (Measure.count : Measure I) {i,j} = 2 := by
    have he : (↑({i,j} : Finset I) : Set I) = {i,j} := by ext k; simp
    rw [← he,Measure.count_apply_finset]
    simp [hn]
  rw [htwo] at hle
  norm_num at hle

lemma markedStableMassKernel_count_map {I S : Type*} [Countable I]
    [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace S]
    (p : I → ℝ×S) (hp : Measurable p) :
    markedStableMassKernel (Measure.count.map p) =
      (normalizedMeasure (Measure.count.withDensity
        (fun i => ENNReal.ofReal (Real.exp (p i).1)))).map p := by
  rw [normalizedMeasure_map _ hp]
  change normalizedMeasure ((Measure.count.map p).withDensity
    (fun t : ℝ×S => ENNReal.ofReal (Real.exp t.1))) = _
  rw [map_withDensity_comp Measure.count hp (by fun_prop)]
  rfl

lemma stableMassKernel_count_map_atom {I S : Type*} [Countable I]
    [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace S]
    (p : I → ℝ×S) (hp : Measurable p) (hinj : Function.Injective (fun i => (p i).1))
    (i : I) :
    stableMassKernel ((Measure.count.map p).map Prod.fst) {(p i).1} =
      ((∑' j, ENNReal.ofReal (Real.exp (p j).1))⁻¹) *
        ENNReal.ofReal (Real.exp (p i).1) := by
  rw [Measure.map_map measurable_fst hp]
  change normalizedMeasure ((Measure.count.map (fun j => (p j).1)).withDensity
    (fun x => ENNReal.ofReal (Real.exp x))) {(p i).1} = _
  have hp' : Measurable (fun j => (p j).1) := hp.fst
  rw [map_withDensity_comp Measure.count hp' (by fun_prop),
    ← normalizedMeasure_map _ hp',
    Measure.map_apply hp' (measurableSet_singleton _)]
  have hpre : (fun j => (p j).1) ⁻¹' {(p i).1} = {i} := by
    ext j
    simp only [mem_preimage,mem_singleton_iff,hinj.eq_iff]
  rw [hpre,normalizedMeasure,Measure.smul_apply,smul_eq_mul,
    withDensity_apply _ (measurableSet_singleton i),withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,lintegral_count]
  simp

def countedBlockProbability {I S : Type*} (p : I → ℝ×S) :
    List (ℕ×(S → ℝ≥0∞)) → {m : ℕ} → (Fin m → ℝ) → ℝ≥0∞
  | [],_,_ => 1
  | nf::ns,_,z => ∑' i, if ∃ j, z j = (p i).1 then 0 else
      (((∑' k, ENNReal.ofReal (Real.exp (p k).1))⁻¹)*
        ENNReal.ofReal (Real.exp (p i).1))^nf.1 * nf.2 (p i).2 *
          countedBlockProbability p ns (Fin.cons (p i).1 z)

lemma markedBlockProbability_count_map {I S : Type*} [Countable I]
    [MeasurableSpace I] [MeasurableSingletonClass I] [MeasurableSpace S]
    (p : I → ℝ×S) (hp : Measurable p) (hinj : Function.Injective (fun i => (p i).1))
    (ns : List (ℕ×(S → ℝ≥0∞)))
    (hn : ∀ nf ∈ ns, 1 ≤ nf.1) (hm : ∀ nf ∈ ns, Measurable nf.2)
    {m : ℕ} (z : Fin m → ℝ) :
    markedBlockProbability ns (Measure.count.map p) z = countedBlockProbability p ns z := by
  classical
  induction ns generalizing m with
  | nil => rfl
  | cons nf ns ih =>
    have hnf := hn nf (by simp)
    have hn' : ∀ n ∈ ns, 1 ≤ n.1 := fun n h => hn n (by simp [h])
    have hm' : ∀ n ∈ ns, Measurable n.2 := fun n h => hm n (by simp [h])
    unfold markedBlockProbability countedBlockProbability
    rw [markedStableMassKernel_count_map p hp]
    have ha : Measurable (fun t : ℝ×S =>
        stableMassKernel ((Measure.count.map p).map Prod.fst) {t.1}) :=
      stableMassAtom_measurable_comp measurable_const measurable_fst
    have ht : Measurable (fun t : ℝ×S =>
        markedBlockProbability ns (Measure.count.map p) (Fin.cons t.1 z)) :=
      (markedBlockProbability_measurable ns hm' (m+1)).comp
        (measurable_const.prodMk (measurable_fin_cons measurable_fst measurable_const))
    have hf : Measurable (fun t : ℝ×S => if ∃ j, z j = t.1 then (0:ℝ≥0∞) else
        (stableMassKernel ((Measure.count.map p).map Prod.fst) {t.1})^(nf.1-1)*
          nf.2 t.2*markedBlockProbability ns (Measure.count.map p) (Fin.cons t.1 z)) :=
      measurable_const.ite (cascadeMeasurableSet_exists fun j =>
        measurableSet_eq_fun measurable_const measurable_fst)
        (((ha.pow_const _).mul ((hm nf (by simp)).comp measurable_snd)).mul ht)
    have hweight : Measurable (fun i => ENNReal.ofReal (Real.exp (p i).1)) :=
      hp.fst.exp.ennreal_ofReal
    have hfp : Measurable (fun i => if ∃ j, z j = (p i).1 then (0:ℝ≥0∞) else
        (stableMassKernel ((Measure.count.map p).map Prod.fst) {(p i).1})^(nf.1-1)*
          nf.2 (p i).2*markedBlockProbability ns (Measure.count.map p) (Fin.cons (p i).1 z)) :=
      hf.comp hp
    rw [lintegral_map hf hp,normalizedMeasure,lintegral_smul_measure,smul_eq_mul,
      withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      lintegral_withDensity_eq_lintegral_mul _ hweight hfp,
      lintegral_count,lintegral_count,← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro i
    simp only [Pi.mul_apply]
    split_ifs with hi
    · simp
    · rw [stableMassKernel_count_map_atom p hp hinj,ih hn' hm']
      have hpw := pow_succ (((∑' k, ENNReal.ofReal (Real.exp (p k).1))⁻¹)*
        ENNReal.ofReal (Real.exp (p i).1)) (nf.1-1)
      rw [Nat.sub_add_cancel hnf] at hpw
      rw [hpw]
      ring

instance finiteSigmaMeasurableSingleton (k : ℕ → ℕ) :
    MeasurableSingletonClass (Σ j, Fin (k j)) := by
  constructor
  intro x
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro j
  change MeasurableSet ((Sigma.mk j) ⁻¹' {x})
  exact (Set.toFinite _).measurableSet

lemma indexedPoissonMeasure_eq_map_count {A : Type*} [MeasurableSpace A]
    (a : ℕ → ℕ×(ℕ → A)) :
    indexedPoissonMeasure a = Measure.count.map
      (fun i : Σ j, Fin ((a j).1) => (a i.1).2 i.2.val) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [indexedPoissonMeasure_lintegral a hf,
    lintegral_map hf (measurable_of_countable _),lintegral_count,ENNReal.tsum_sigma']
  simp only [tsum_fintype]

end SphericalPerceptronFreeEnergy
end

end OAI
