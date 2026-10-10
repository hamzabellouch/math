import Mathlib
import OAI.Probability.Ballisticity.Estimates.JointPastMoments

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

lemma shared_limit_normalJointPast {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (T : ℝ) (hT : 0 < T) (x : ℕ → Lattice d)
    (μ : ℕ → ProbabilityMeasure RealPathPair) (V : ProbabilityMeasure RealPathPair)
    (hweak : Tendsto μ atTop (𝓝 V)) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    (∀ i, (μ i : Measure RealPathPair)=(sharedConditionedPairLaw ν ℓ (x i) (x i)).map
      (sharedLinearPairPath ℓ f (θ i) (r i) (n i) T (x i) (x i))) →
    NormalJointPast (V : Measure RealPathPair) (Real.toNNReal (T/(2*commonMeanWidth ν ℓ))) := by
  dsimp only
  intro hμ
  apply normal_past_of_uc_tests
  intro q v s t hv hst ht b F G hG
  have hh := shared_limit_interior_past_identity ν hue e f hef htrans r hr T hT x μ V hweak
    v s t hv hst ht F G hG b hμ
  have hc := commonMeanWidth_ge_one ν (realPosition (step e)) htrans
    (signedHeight e) (signedHeight_projection e) (signedHeight_step_le e)
  have he : Real.toNNReal (T*((t:ℝ)-s)/(2*commonMeanWidth ν (realPosition (step e)))) =
      Real.toNNReal (T/(2*commonMeanWidth ν (realPosition (step e)))) * Real.toNNReal ((t:ℝ)-s) := by
    rw [← Real.toNNReal_mul (by positivity : 0 ≤ T/(2*commonMeanWidth ν (realPosition (step e))))]
    congr 1
    ring
  simpa only [he] using hh

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def gridOccupationMass (μ : Measure RealPathPair) (a ρ : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (⌊a⌋₊+1), μ.real {P | |layerGap P (layerGridPoint a j)| ≤ ρ})/a

lemma gap_open_measure_le_grid (μ : Measure RealPathPair) [IsProbabilityMeasure μ]
    {a ρ δ : ℝ} (ha : 0 < a) (hδ : 1/a ≤ δ) :
    (μ.prod volume) {z : RealPathPair × unitInterval | |layerGap z.1 z.2| < ρ/2} ≤
      ENNReal.ofReal (gridOccupationMass μ a ρ) +
        μ {P | P.1 ∈ ContinuousOscillation (ρ/4) δ ∨ P.2 ∈ ContinuousOscillation (ρ/4) δ} := by
  let E := fun j => {P : RealPathPair | |layerGap P (layerGridPoint a j)| ≤ ρ}
  let C := fun j => {t : unitInterval | ⌊a*(t:ℝ)⌋₊ = j}
  let B := {P : RealPathPair | P.1 ∈ ContinuousOscillation (ρ/4) δ ∨ P.2 ∈ ContinuousOscillation (ρ/4) δ}
  have hsub : {z : RealPathPair × unitInterval | |layerGap z.1 z.2| < ρ/2} ⊆
      (⋃ j ∈ Finset.range (⌊a⌋₊+1), E j ×ˢ C j) ∪ (B ×ˢ Set.univ) := by
    rintro ⟨P,t⟩ ht
    change |layerGap P t| < ρ/2 at ht
    by_cases hB : P ∈ B
    · exact Or.inr ⟨hB,Set.mem_univ _⟩
    · have h1 : P.1 ∉ ContinuousOscillation (ρ/4) δ := fun h => hB (Or.inl h)
      have h2 : P.2 ∉ ContinuousOscillation (ρ/4) δ := fun h => hB (Or.inr h)
      have hc := gap_grid_close ha hδ P t h1 h2
      have hj : ⌊a*(t:ℝ)⌋₊ ∈ Finset.range (⌊a⌋₊+1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono (mul_le_of_le_one_right ha.le t.2.2)))
      apply Or.inl
      apply Set.mem_iUnion.mpr
      refine ⟨⌊a*(t:ℝ)⌋₊,Set.mem_iUnion.mpr ⟨hj,?_,rfl⟩⟩
      have hab := abs_sub_le (layerGap P (layerGridPoint a ⌊a*(t:ℝ)⌋₊)) (layerGap P t) 0
      rw [sub_zero,sub_zero,abs_sub_comm] at hab
      change |layerGap P (layerGridPoint a ⌊a*(t:ℝ)⌋₊)| ≤ ρ
      linarith only [hab,hc,ht]
  have hsum : (∑ j ∈ Finset.range (⌊a⌋₊+1), μ (E j))*ENNReal.ofReal (1/a) =
      ENNReal.ofReal (gridOccupationMass μ a ρ) := by
    rw [show gridOccupationMass μ a ρ =
      (∑ j ∈ Finset.range (⌊a⌋₊+1), μ.real (E j))*(1/a) by dsimp [gridOccupationMass,E]; ring]
    rw [ENNReal.ofReal_mul (Finset.sum_nonneg (fun j hj => measureReal_nonneg)),
      ENNReal.ofReal_sum_of_nonneg (fun j hj => measureReal_nonneg)]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
  calc
    _ ≤ (μ.prod volume) ((⋃ j ∈ Finset.range (⌊a⌋₊+1), E j ×ˢ C j) ∪ (B ×ˢ Set.univ)) := measure_mono hsub
    _ ≤ (μ.prod volume) (⋃ j ∈ Finset.range (⌊a⌋₊+1), E j ×ˢ C j) + (μ.prod volume) (B ×ˢ Set.univ) :=
      measure_union_le _ _
    _ ≤ (∑ j ∈ Finset.range (⌊a⌋₊+1), μ (E j)*ENNReal.ofReal (1/a))+μ B := by
      apply add_le_add
      · apply (measure_biUnion_finset_le _ _).trans
        apply Finset.sum_le_sum
        intro j hj
        rw [Measure.prod_prod]
        exact mul_le_mul le_rfl (volume_layer_cell_le ha j) (by positivity) (by positivity)
      · simp only [Measure.prod_prod,measure_univ,mul_one,le_refl]
    _ = _ := by rw [← Finset.sum_mul,hsum]

end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

theorem joint_limit_diagonal_time_zero (μ : ℕ → ProbabilityMeasure RealPathPair)
    (V : ProbabilityMeasure RealPathPair) (hweak : Tendsto μ atTop (𝓝 V))
    (ht : IsTightMeasureSet (Set.range (fun i => (μ i : Measure RealPathPair))))
    (a : ℕ → ℝ) (ha : Tendsto a atTop atTop)
    (hocc : ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ᶠ i in atTop, gridOccupationMass (μ i) (a i) ρ ≤ ε) :
    ((V : Measure RealPathPair).prod volume) {z : RealPathPair × unitInterval | layerGap z.1 z.2 = 0} = 0 := by
  have ht1 : IsTightMeasureSet (Set.range (fun i => (μ i : Measure RealPathPair).map Prod.fst)) := by
    convert ht.map (f := Prod.fst) continuous_fst using 1
    ext η
    simp
  have ht2 : IsTightMeasureSet (Set.range (fun i => (μ i : Measure RealPathPair).map Prod.snd)) := by
    convert ht.map (f := Prod.snd) continuous_snd using 1
    ext η
    simp
  let U : ProbabilityMeasure unitInterval := ⟨volume,inferInstance⟩
  have hprod : Tendsto (fun i => (μ i).prod U) atTop (𝓝 (V.prod U)) :=
    ProbabilityMeasure.continuous_prod.tendsto (V,U) |>.comp (hweak.prodMk_nhds tendsto_const_nhds)
  apply le_antisymm _ (by positivity)
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  simp only [zero_add]
  have he : 0 < (ε:ℝ)/3 := by exact div_pos hε (by norm_num)
  obtain ⟨ρ,hρ,hocc⟩ := hocc ((ε:ℝ)/3) he
  obtain ⟨δ1,hd1,hm1⟩ := tight_path_modulus _ ht1 (by positivity : 0 < ρ/4) he
  obtain ⟨δ2,hd2,hm2⟩ := tight_path_modulus _ ht2 (by positivity : 0 < ρ/4) he
  let δ := min δ1 δ2
  have hd : 0 < δ := lt_min hd1 hd2
  have hb (i : ℕ) : (μ i : Measure RealPathPair)
      {P | P.1 ∈ ContinuousOscillation (ρ/4) δ ∨ P.2 ∈ ContinuousOscillation (ρ/4) δ} ≤
        ENNReal.ofReal ((ε:ℝ)/3)+ENNReal.ofReal ((ε:ℝ)/3) := by
    apply (measure_union_le _ _).trans
    apply add_le_add
    · have hs : {P : RealPathPair | P.1 ∈ ContinuousOscillation (ρ/4) δ} ⊆
          Prod.fst ⁻¹' ContinuousOscillation (ρ/4) δ1 := fun P h =>
        continuousOscillation_mono (min_le_left _ _) h
      apply (measure_mono hs).trans
      rw [← Measure.map_apply measurable_fst (isOpen_continuousOscillation _ _).measurableSet]
      exact hm1 i
    · have hs : {P : RealPathPair | P.2 ∈ ContinuousOscillation (ρ/4) δ} ⊆
          Prod.snd ⁻¹' ContinuousOscillation (ρ/4) δ2 := fun P h =>
        continuousOscillation_mono (min_le_right _ _) h
      apply (measure_mono hs).trans
      rw [← Measure.map_apply measurable_snd (isOpen_continuousOscillation _ _).measurableSet]
      exact hm2 i
  have hinv : Tendsto (fun i => 1/a i) atTop (𝓝 (0:ℝ)) :=
    tendsto_const_nhds.div_atTop ha
  have hevent : ∀ᶠ i in atTop,
      ((↑((μ i).prod U)) : Measure (RealPathPair × unitInterval))
        {z | |layerGap z.1 z.2| < ρ/2} ≤ (ε:ℝ≥0∞) := by
    filter_upwards [hocc,ha.eventually_gt_atTop 0,hinv.eventually_lt_const hd] with i hi hai hdi
    have hg := gap_open_measure_le_grid (ρ := ρ) (μ i) hai hdi.le
    have hc := hg.trans (add_le_add (ENNReal.ofReal_le_ofReal hi) (hb i))
    have heq : ENNReal.ofReal ((ε:ℝ)/3)+(ENNReal.ofReal ((ε:ℝ)/3)+ENNReal.ofReal ((ε:ℝ)/3)) = ε := by
      rw [← ENNReal.ofReal_add he.le,← ENNReal.ofReal_add he.le]
      have heq : (ε:ℝ)/3+((ε:ℝ)/3+(ε:ℝ)/3) = ε := by ring
      rw [heq,ENNReal.ofReal_coe_nnreal]
      all_goals positivity
    exact hc.trans_eq heq
  have hopen : IsOpen {z : RealPathPair × unitInterval | |layerGap z.1 z.2| < ρ/2} :=
    isOpen_lt continuous_layerGap.abs continuous_const
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hprod hopen
  have hlim : liminf (fun i => ((↑((μ i).prod U)) : Measure (RealPathPair × unitInterval))
      {z | |layerGap z.1 z.2| < ρ/2}) atTop ≤ (ε:ℝ≥0∞) :=
    (liminf_le_limsup (by isBoundedDefault) (by isBoundedDefault)).trans (limsup_le_of_le (by isBoundedDefault) hevent)
  apply (measure_mono (show {z : RealPathPair × unitInterval | layerGap z.1 z.2 = 0} ⊆
    {z | |layerGap z.1 z.2| < ρ/2} from ?_)).trans (hport.trans hlim)
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz ⊢
  rw [hz,abs_zero]
  positivity

end DirectionalTransience

end

end

end OAI
