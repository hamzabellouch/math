import Mathlib
import OAI.Probability.Ballisticity.Estimates.RecordIndexTime

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

noncomputable def cappedExp (t : ℝ) (N : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => min (N : ℝ) (Real.exp (t*x)))
    (by fun_prop) N (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (le_min (Nat.cast_nonneg _) (Real.exp_pos _).le)]
      exact min_le_left _ _)

lemma cappedExp_nonneg (t : ℝ) (N : ℕ) (x : ℝ) : 0 ≤ cappedExp t N x :=
  le_min (Nat.cast_nonneg _) (Real.exp_pos _).le

lemma integral_cappedExp_tendsto (m : ℝ) (v : ℝ≥0) (t : ℝ) :
    Tendsto (fun N => ∫ x, cappedExp t N x ∂gaussianReal m v) atTop
      (𝓝 (Real.exp (m*t+v*t^2/2))) := by
  have hh := tendsto_integral_of_dominated_convergence (μ := gaussianReal m v)
    (F := fun N : ℕ => fun x => cappedExp t N x) (f := fun x => Real.exp (t*x))
    (fun x => Real.exp (t*x)) (fun N => (cappedExp t N).continuous.measurable.aestronglyMeasurable)
    (integrable_exp_mul_gaussianReal t) (fun N => ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (cappedExp_nonneg _ _ _)]
      exact min_le_right _ _)) (ae_of_all _ (fun x => by
        apply tendsto_const_nhds.congr'
        filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (Real.exp (t*x)))] with N hN
        exact (min_eq_right hN).symm))
  have he : (∫ x, Real.exp (t*x) ∂gaussianReal m v) = Real.exp (m*t+v*t^2/2) := by
    simpa only [mgf,id_eq] using (mgf_gaussianReal (p := gaussianReal m v) (X := id) (μ := m) (v := v) (by simp) t)
  rwa [he] at hh

lemma gaussian_mean_eq_of_test_domination (m₁ m₂ : ℝ) (v : ℝ≥0) {p : ℝ} (hp : 0 < p)
    (h : ∀ f : ℝ →ᵇ ℝ, (∀ x, 0 ≤ f x) →
      p*(∫ x, f x ∂gaussianReal m₁ v) ≤ ∫ x, f x ∂gaussianReal m₂ v) : m₁ = m₂ := by
  have hmgf (t : ℝ) : Real.log p + m₁*t ≤ m₂*t := by
    have hh := le_of_tendsto_of_tendsto ((integral_cappedExp_tendsto m₁ v t).const_mul p)
      (integral_cappedExp_tendsto m₂ v t)
      (Eventually.of_forall (fun N => h (cappedExp t N) (cappedExp_nonneg t N)))
    rw [← Real.exp_log hp,← Real.exp_add] at hh
    have := Real.exp_le_exp.mp hh
    linarith
  by_contra hne
  have hh := hmgf ((1-Real.log p)/(m₁-m₂))
  have he : (m₁-m₂)*((1-Real.log p)/(m₁-m₂)) = 1-Real.log p :=
    mul_div_cancel₀ _ (sub_ne_zero.mpr hne)
  nlinarith

lemma weak_test_domination {μ ν : ℕ → ProbabilityMeasure ℝ} {M N : ProbabilityMeasure ℝ}
    (hμ : Tendsto μ atTop (𝓝 M)) (hν : Tendsto ν atTop (𝓝 N)) {p : ℝ} (hp : 0 ≤ p)
    (hdom : ∀ i, ENNReal.ofReal p • (μ i : Measure ℝ) ≤ (ν i : Measure ℝ))
    (f : ℝ →ᵇ ℝ) (hf : ∀ x, 0 ≤ f x) :
    p*(∫ x, f x ∂(M : Measure ℝ)) ≤ ∫ x, f x ∂(N : Measure ℝ) := by
  apply le_of_tendsto_of_tendsto
    ((ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ f).const_mul p)
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν f)
  apply Eventually.of_forall
  intro i
  have h := integral_mono_measure (hdom i) (ae_of_all _ hf) (f.integrable (ν i))
  simpa only [integral_smul_measure,ENNReal.toReal_ofReal hp,smul_eq_mul] using h

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

abbrev RecordWord {d : ℕ} (ℓ : Vector d) (k : ℕ) :=
  {w : List (Direction d) // wordPath 0 w ∈ RecordIndexPrefix ℓ k w.length}

lemma recordWord_prefix {d : ℕ} (ℓ : Vector d) (k : ℕ) (w : RecordWord ℓ k)
    {X : Path d} (hX : X ∈ wordCylinder 0 w.val) : X ∈ RecordIndexPrefix ℓ k w.val.length :=
  (recordIndexPrefix_prefix ℓ k w.val.length X (wordPath 0 w.val) hX).mpr w.property

lemma recordWord_position {d : ℕ} (ℓ : Vector d) (k : ℕ) (w : RecordWord ℓ k)
    {X : Path d} (hX : X ∈ wordCylinder 0 w.val) :
    recordIndexPosition ℓ k X = wordPath 0 w.val w.val.length := by
  rw [recordIndexPosition,recordIndexTime_eq ℓ k w.val.length X (recordWord_prefix ℓ k w hX)]
  exact hX _ le_rfl

lemma recordWord_cylinders_disjoint {d : ℕ} (ℓ : Vector d) (k : ℕ) :
    Pairwise (fun u v : RecordWord ℓ k => Disjoint (wordCylinder 0 u.val) (wordCylinder 0 v.val)) := by
  intro u v huv
  apply Set.disjoint_left.mpr
  intro X hu hv
  have h1 := recordWord_prefix ℓ k u hu
  have h2 := recordWord_prefix ℓ k v hv
  by_cases hlen : u.val.length = v.val.length
  · exact huv (Subtype.ext (word_eq_of_cylinders 0 u.val v.val X hu hv hlen))
  · exact Set.disjoint_left.mp (recordIndexPrefix_disjoint ℓ k hlen) h1 h2

lemma conditioned_recordWord_cover {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) {k : ℕ} (hk : 0 < k) :
    ∀ᵐ X ∂conditionedLaw ν ℓ, ∃ w : RecordWord ℓ k, X ∈ wordCylinder 0 w.val := by
  filter_upwards [conditioned_recordIndexPrefix_exists ν ℓ htrans hk,
    (conditionedLaw_absolutelyContinuous ν ℓ).ae_le (annealed_nearest_neighbor ν),
    (conditionedLaw_absolutelyContinuous ν ℓ).ae_le (annealed_initial ν)] with X hrec hnn h0
  obtain ⟨n,hn⟩ := hrec
  obtain ⟨w,hw,hcy⟩ := exists_word_prefix X hnn n
  rw [h0] at hcy
  have hp : wordPath 0 w ∈ RecordIndexPrefix ℓ k w.length := by
    apply (recordIndexPrefix_prefix ℓ k w.length X (wordPath 0 w) hcy).mp
    simpa only [hw] using hn
  exact ⟨⟨w,hp⟩,hcy⟩

lemma recordWord_position_add {d : ℕ} (ℓ : Vector d) (k j : ℕ) (w : RecordWord ℓ k)
    {X : Path d} (hX : X ∈ wordCylinder 0 w.val)
    (hD : (fun i => X (w.val.length+i)-wordPath 0 w.val w.val.length) ∈ NoDrop ℓ 0)
    (hR : ∃ m, (fun i => X (w.val.length+i)-wordPath 0 w.val w.val.length) ∈ RecordIndexPrefix ℓ j m) :
    recordIndexPosition ℓ (k+j) X = wordPath 0 w.val w.val.length +
      recordIndexPosition ℓ j (fun i => X (w.val.length+i)-wordPath 0 w.val w.val.length) := by
  let n := w.val.length
  let Z : Path d := fun i => X (n+i)-X n
  have he : (fun i => X (w.val.length+i)-wordPath 0 w.val w.val.length) = Z := by
    funext i
    rw [show wordPath 0 w.val w.val.length = X n from (hX _ le_rfl).symm]
  rw [he] at hD hR ⊢
  obtain ⟨m,hm⟩ := hR
  have hpre := recordWord_prefix ℓ k w hX
  have hDX : X ∈ NoDrop ℓ 0 := recordIndexPrefix_noDrop ℓ k n
    ⟨hpre,(suffix_noDrop_iff ℓ X n).mp hD⟩
  have ha : X ∈ RecordIndexPrefix ℓ (k+j) (n+m) := by
    refine ⟨Nat.add_pos_left hpre.1 m,?_,?_,fun i _ => hDX i⟩
    · exact (strictRecord_suffix_iff ℓ X hpre.2.1 hm.1).mp hm.2.1
    · rw [recordCount_add ℓ X hpre.2.1,hpre.2.2.1,hm.2.2.1]
  rw [recordIndexPosition,recordIndexTime_eq ℓ (k+j) (n+m) X ha,
    recordIndexPosition,recordIndexTime_eq ℓ j m Z hm]
  change X (n+m) = wordPath 0 w.val w.val.length+(X (n+m)-X n)
  rw [← hX n le_rfl]
  abel

lemma conditioned_prefix_mass_le_raw {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0)
    (A : Set (Path d)) (hA : MeasurableSet A) :
    annealedLaw ν (NoDrop ℓ 0) * conditionedLaw ν ℓ A ≤ annealedLaw ν A := by
  rw [conditionedLaw,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply hA,← mul_assoc,
    ENNReal.mul_inv_cancel hp (measure_ne_top _ _),one_mul]
  exact measure_mono Set.inter_subset_left

lemma conditioned_record_convolution_domination {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    {k j : ℕ} (hk : 0 < k) (hj : 0 < j) :
    annealedLaw ν (NoDrop ℓ 0) •
      (independentConditionedPairLaw ν ℓ).map (fun P =>
        recordIndexPosition ℓ k P.1 + recordIndexPosition ℓ j P.2) ≤
      (conditionedLaw ν ℓ).map (recordIndexPosition ℓ (k+j)) := by
  let μ := conditionedLaw ν ℓ
  let p := annealedLaw ν (NoDrop ℓ 0)
  have hp : p ≠ 0 := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let : IsProbabilityMeasure μ := conditionedLaw_probability ν ℓ hp
  apply Measure.le_iff.mpr
  intro A hA
  let B := fun w : RecordWord ℓ k =>
    (fun Y => wordPath 0 w.val w.val.length + recordIndexPosition ℓ j Y) ⁻¹' A
  have hB (w : RecordWord ℓ k) : MeasurableSet (B w) :=
    hA.preimage (measurable_const.add (measurable_recordIndexPosition ℓ j))
  let R : Set (Path d) := (⋃ m, RecordIndexPrefix ℓ j m) ∩ NoDrop ℓ 0
  have hRm : MeasurableSet R :=
    (MeasurableSet.iUnion (measurableSet_recordIndexPrefix ℓ j)).inter (measurableSet_noDrop ℓ 0)
  have hR : ∀ᵐ Y ∂μ, Y ∈ R := by
    filter_upwards [conditioned_recordIndexPrefix_exists ν ℓ htrans hj,
      conditionedLaw_noDrop ν ℓ] with Y hY hD
    exact ⟨Set.mem_iUnion.mpr hY,hD⟩
  let E := fun w : RecordWord ℓ k =>
    (fun X : Path d => fun i => X (w.val.length+i)-wordPath 0 w.val w.val.length) ⁻¹'
      (B w ∩ R) ∩ wordCylinder 0 w.val
  have hEm (w : RecordWord ℓ k) : MeasurableSet (E w) :=
    ((hB w).inter hRm).preimage (by fun_prop) |>.inter (measurableSet_wordCylinder 0 w.val)
  have hEd : Pairwise (fun u v : RecordWord ℓ k => Disjoint (E u) (E v)) :=
    fun u v huv => (recordWord_cylinders_disjoint ℓ k huv).mono Set.inter_subset_right Set.inter_subset_right
  have hEsub (w : RecordWord ℓ k) : E w ⊆ (recordIndexPosition ℓ (k+j)) ⁻¹' A := by
    intro X hX
    have hadd := recordWord_position_add ℓ k j w hX.2 hX.1.2.2
      (Set.mem_iUnion.mp hX.1.2.1)
    change recordIndexPosition ℓ (k+j) X ∈ A
    rw [hadd]
    exact hX.1.1
  have hmass (w : RecordWord ℓ k) : μ (E w) = annealedLaw ν (wordCylinder 0 w.val)*μ (B w) := by
    have he : μ (B w ∩ R) = μ (B w) := measure_congr (hR.mono fun Y hY => propext ⟨fun h => h.1,fun h => ⟨h,hY⟩⟩)
    rw [show μ (E w) = annealedLaw ν (wordCylinder 0 w.val)*μ (B w ∩ R) from
      conditioned_record_word_factor ν ℓ w.val w.property.2.1 w.property.2.2.2
        (B w ∩ R) ((hB w).inter hRm) (fun _ h => h.2.2),he]
  have hCd : Pairwise (fun u v : RecordWord ℓ k =>
      Disjoint (wordCylinder 0 u.val ×ˢ B u) (wordCylinder 0 v.val ×ˢ B v)) := by
    intro u v huv
    apply Set.disjoint_left.mpr
    exact fun P hu hv => Set.disjoint_left.mp (recordWord_cylinders_disjoint ℓ k huv) hu.1 hv.1
  have heq : (μ.prod μ) ((fun P => recordIndexPosition ℓ k P.1 + recordIndexPosition ℓ j P.2) ⁻¹' A) =
      ∑' w : RecordWord ℓ k, μ (wordCylinder 0 w.val)*μ (B w) := by
    simp_rw [← Measure.prod_prod]
    rw [← measure_iUnion hCd (fun w => (measurableSet_wordCylinder 0 w.val).prod (hB w))]
    apply measure_congr
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (conditioned_recordWord_cover ν ℓ htrans hk)] with P hP
    obtain ⟨w,hw⟩ := hP
    apply propext
    constructor
    · intro h
      change recordIndexPosition ℓ k P.1 + recordIndexPosition ℓ j P.2 ∈ A at h
      exact Set.mem_iUnion.mpr ⟨w,hw,by simpa only [B,Set.mem_preimage,← recordWord_position ℓ k w hw] using h⟩
    · intro h
      obtain ⟨v,hv,hBv⟩ := Set.mem_iUnion.mp h
      change recordIndexPosition ℓ k P.1 + recordIndexPosition ℓ j P.2 ∈ A
      simpa only [B,Set.mem_preimage,← recordWord_position ℓ k v hv] using hBv
  rw [Measure.smul_apply,smul_eq_mul,Measure.map_apply
    (show Measurable (fun P : Path d × Path d => recordIndexPosition ℓ k P.1 + recordIndexPosition ℓ j P.2) from
      ((measurable_recordIndexPosition ℓ k).comp measurable_fst).add
        ((measurable_recordIndexPosition ℓ j).comp measurable_snd)) hA,
    Measure.map_apply (measurable_recordIndexPosition ℓ (k+j)) hA]
  change p * (μ.prod μ) _ ≤ μ _
  rw [heq,← ENNReal.tsum_mul_left]
  calc
    _ ≤ ∑' w : RecordWord ℓ k, μ (E w) := by
      apply ENNReal.tsum_le_tsum
      intro w
      rw [hmass,← mul_assoc]
      gcongr
      exact conditioned_prefix_mass_le_raw ν ℓ hp _ (measurableSet_wordCylinder 0 w.val)
    _ = μ (⋃ w : RecordWord ℓ k, E w) := (measure_iUnion hEd hEm).symm
    _ ≤ _ := measure_mono (Set.iUnion_subset hEsub)

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction

end
end

end OAI
