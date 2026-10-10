import Mathlib
import OAI.Probability.Ballisticity.Estimates.NormalizedSharedRestrict
import OAI.Probability.Ballisticity.Walk.RegularPath

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
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
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
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma regularPath_cross {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℝ)
    {X : Path d} (hX : X ∈ RegularPath ℓ x) (hD : X ∈ NoDrop ℓ x) : X ∈ Cross ℓ x H := by
  obtain ⟨n,hn⟩ := (hX.2.2.eventually_ge_atTop (dot (realPosition x) ℓ+H)).exists
  exact ⟨n,hn,fun j _ => hD j⟩

lemma hitWordsEvent_compl_on {d : ℕ} (x y : Lattice d) (S T : Set (Lattice d))
    (hST : Disjoint S T) (E : Set (HitWord x S T × HitWord y S T))
    {Z : Path d × Path d} (hZ : Z ∈ hitWordsEvent x y S T Set.univ) :
    Z ∈ hitWordsEvent x y S T Eᶜ ↔ Z ∉ hitWordsEvent x y S T E := by
  obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hZ
  obtain ⟨_,hw⟩ := Set.mem_iUnion.mp hw
  have hu (v : HitWord x S T × HitWord y S T)
      (hv : Z ∈ wordCylinder x v.1.val ×ˢ wordCylinder y v.2.val) : v = w := by
    by_contra h
    exact Set.disjoint_left.mp (hitWords_pair_cylinders_disjoint x y S T hST h) hv hw
  constructor
  · intro hc he
    obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hc
    obtain ⟨hv,hcy⟩ := Set.mem_iUnion.mp hv
    obtain ⟨u,hu'⟩ := Set.mem_iUnion.mp he
    obtain ⟨hu',hcy'⟩ := Set.mem_iUnion.mp hu'
    rw [hu v hcy] at hv
    rw [hu u hcy'] at hu'
    exact hv hu'
  · intro hn
    refine Set.mem_iUnion.mpr ⟨w,Set.mem_iUnion.mpr ⟨?_,hw⟩⟩
    exact fun h => hn (Set.mem_iUnion.mpr ⟨w,Set.mem_iUnion.mpr ⟨h,hw⟩⟩)

lemma regularPath_hitWords_cover {d : ℕ} (ℓ : Vector d) (x y : Lattice d)
    (hxy : dot (realPosition x) ℓ = dot (realPosition y) ℓ) (H : ℝ)
    {Z : Path d × Path d}
    (hZ : (Z.1 ∈ RegularPath ℓ x ∧ Z.1 ∈ NoDrop ℓ x) ∧
      (Z.2 ∈ RegularPath ℓ y ∧ Z.2 ∈ NoDrop ℓ y)) :
    Z ∈ hitWordsEvent x y (Strip ℓ x H) (Upper ℓ x H) Set.univ := by
  have hx := regularPath_cross ℓ x H hZ.1.1 hZ.1.2
  have hy := regularPath_cross ℓ y H hZ.2.1 hZ.2.2
  rw [cross_eq_hit] at hx hy
  have hs : Strip ℓ y H = Strip ℓ x H := by unfold Strip; rw [hxy]
  have ht : Upper ℓ y H = Upper ℓ x H := by unfold Upper; rw [hxy]
  rw [hs,ht] at hy
  obtain ⟨u,hu⟩ := (hitWord_cover x _ _ Z.1 hZ.1.1.1 hZ.1.1.2.1).mp hx
  obtain ⟨v,hv⟩ := (hitWord_cover y _ _ Z.2 hZ.2.1.1 hZ.2.1.2.1).mp hy
  exact Set.mem_iUnion.mpr ⟨(u,v),Set.mem_iUnion.mpr ⟨Set.mem_univ _,hu,hv⟩⟩

lemma prefix_event_real_compl {d : ℕ} (μ : Measure (Path d × Path d)) [IsProbabilityMeasure μ]
    (x y : Lattice d) (S T : Set (Lattice d)) (hST : Disjoint S T)
    (hcover : ∀ᵐ Z ∂μ, Z ∈ hitWordsEvent x y S T Set.univ)
    (E : Set (HitWord x S T × HitWord y S T)) :
    μ.real (hitWordsEvent x y S T Eᶜ) = 1-μ.real (hitWordsEvent x y S T E) := by
  have he : μ (hitWordsEvent x y S T Eᶜ) = μ (hitWordsEvent x y S T E)ᶜ := by
    apply measure_congr
    filter_upwards [hcover] with Z hZ
    exact propext (hitWordsEvent_compl_on x y S T hST E hZ)
  change (μ _).toReal = _
  rw [he]
  simpa only [Measure.real,measure_univ,ENNReal.toReal_one] using
    (measureReal_compl (μ := μ) (measurableSet_hitWordsEvent x y S T E))

noncomputable def prefixVariation {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (x y : Lattice d) (H : ℝ) : ℝ :=
  sSup (Set.range fun E : Set (HitWord x (Strip ℓ x H) (Upper ℓ x H) ×
      HitWord y (Strip ℓ x H) (Upper ℓ x H)) =>
    |(sharedConditionedPairLaw ν ℓ x y).real (hitWordsEvent x y (Strip ℓ x H) (Upper ℓ x H) E)-
      ((conditionedFrom ν ℓ x).prod (conditionedFrom ν ℓ y)).real
        (hitWordsEvent x y (Strip ℓ x H) (Upper ℓ x H) E)|)

lemma prefixVariation_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (x y : Lattice d)
    (hxy : dot (realPosition x) ℓ = dot (realPosition y) ℓ) (H : ℝ) :
    prefixVariation ν ℓ x y H ≤
      (sharedConditionedPairLaw ν ℓ x y).real (PrefixContact (Strip ℓ x H)) +
      ((sharedNoDropMass ν ℓ x y)⁻¹ *
        ((annealedLaw ν (NoDrop ℓ 0))^2-sharedNoDropMass ν ℓ x y +
          2*annealedLaw ν (Cross ℓ 0 H \ NoDrop ℓ 0))).toReal := by
  let μ := sharedConditionedPairLaw ν ℓ x y
  let η := (conditionedFrom ν ℓ x).prod (conditionedFrom ν ℓ y)
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  have hp₂ := ne_of_gt (sharedNoDropMass_pos ν hue ℓ hℓ htrans x y)
  let : IsProbabilityMeasure μ := sharedConditionedPairLaw_probability ν ℓ x y hp₂
  let : IsProbabilityMeasure (conditionedFrom ν ℓ x) := conditionedFrom_probability ν ℓ x hp
  let : IsProbabilityMeasure (conditionedFrom ν ℓ y) := conditionedFrom_probability ν ℓ y hp
  have hc₁ : ∀ᵐ Z ∂μ, Z ∈ hitWordsEvent x y (Strip ℓ x H) (Upper ℓ x H) Set.univ :=
    (sharedConditioned_regularPath ν ℓ htrans x y).mono fun _ h => regularPath_hitWords_cover ℓ x y hxy H h
  have hc₂ : ∀ᵐ Z ∂η, Z ∈ hitWordsEvent x y (Strip ℓ x H) (Upper ℓ x H) Set.univ := by
    have hmeas : MeasurableSet {Z : Path d × Path d |
        (Z.1 ∈ RegularPath ℓ x ∧ Z.1 ∈ NoDrop ℓ x) ∧
        (Z.2 ∈ RegularPath ℓ y ∧ Z.2 ∈ NoDrop ℓ y)} :=
      ((measurableSet_regularPath ℓ x).inter (measurableSet_noDrop ℓ x)).prod
        ((measurableSet_regularPath ℓ y).inter (measurableSet_noDrop ℓ y))
    have hr := (Measure.ae_prod_iff_ae_ae hmeas).mpr (show ∀ᵐ X ∂conditionedFrom ν ℓ x,
      ∀ᵐ Y ∂conditionedFrom ν ℓ y, (X ∈ RegularPath ℓ x ∧ X ∈ NoDrop ℓ x) ∧
        (Y ∈ RegularPath ℓ y ∧ Y ∈ NoDrop ℓ y) from
      (conditionedFrom_regularPath ν ℓ htrans x).mono fun X hX =>
        (conditionedFrom_regularPath ν ℓ htrans y).mono fun Y hY => ⟨hX,hY⟩)
    exact hr.mono fun _ h => regularPath_hitWords_cover ℓ x y hxy H h
  let δ := (sharedNoDropMass ν ℓ x y)⁻¹ *
        ((annealedLaw ν (NoDrop ℓ 0))^2-sharedNoDropMass ν ℓ x y +
          2*annealedLaw ν (Cross ℓ 0 H \ NoDrop ℓ 0))
  have hδ : δ ≠ ∞ := by
    apply ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hp₂)
    finiteness
  let F := hitWordsEvent x y (Strip ℓ x H) (Upper ℓ x H)
  have hb E : μ.real (F E) ≤ η.real (F E)+μ.real (PrefixContact (Strip ℓ x H))+δ.toReal := by
    have hh := conditioned_prefix_comparison ν hue ℓ hℓ htrans x y hxy H E
    have hh' := ENNReal.toReal_mono (show η (F E)+μ (PrefixContact (Strip ℓ x H))+δ ≠ ∞ by finiteness) hh
    simpa only [Measure.real,ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
      ENNReal.toReal_add (by finiteness : η (F E)+μ (PrefixContact (Strip ℓ x H)) ≠ ∞) hδ] using hh'
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨E,rfl⟩
  have hb₁ := hb E
  have hb₂ := hb Eᶜ
  rw [prefix_event_real_compl μ x y _ _ (disjoint_strip_upper ℓ x H) hc₁,
    prefix_event_real_compl η x y _ _ (disjoint_strip_upper ℓ x H) hc₂] at hb₂
  exact abs_sub_le_iff.mpr ⟨by linarith,by linarith⟩

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma sharedNoDropMass_tendsto_gap {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (f : Direction d) (x y : ℕ → Lattice d)
    (hgap : Tendsto (fun i => |signedCoordinate f (y i-x i)|) atTop atTop) :
    Tendsto (fun i => (sharedNoDropMass ν ℓ (x i) (y i)).toReal) atTop
      (𝓝 ((annealedLaw ν (NoDrop ℓ 0)).toReal^2)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := sharedNoDropMass_mixing ν ℓ hε
  filter_upwards [hgap.eventually_gt_atTop (2*(N:ℝ))] with i hi
  rw [Real.dist_eq]
  apply hN
  apply latticeBall_disjoint_of_coordinate_gap f.1
  have he : |signedCoordinate f (y i-x i)| = (|(x i) f.1-(y i) f.1| : ℝ) := by
    simp only [signedCoordinate,Pi.sub_apply,apply_ite abs,abs_neg,ite_self,Int.cast_sub]
    exact abs_sub_comm _ _
  rw [he] at hi
  exact_mod_cast hi

lemma prefix_error_tendsto_zero {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (f : Direction d)
    (x y : ℕ → Lattice d) (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (hgap : Tendsto (fun i => |signedCoordinate f (y i-x i)|) atTop atTop) :
    Tendsto (fun i => ((sharedNoDropMass ν ℓ (x i) (y i))⁻¹ *
      ((annealedLaw ν (NoDrop ℓ 0))^2-sharedNoDropMass ν ℓ (x i) (y i) +
        2*annealedLaw ν (Cross ℓ 0 (H i) \ NoDrop ℓ 0))).toReal) atTop (𝓝 0) := by
  let p := annealedLaw ν (NoDrop ℓ 0)
  let q := fun i => sharedNoDropMass ν ℓ (x i) (y i)
  have hp : p ≠ 0 := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  have hpfin : p^2 ≠ ∞ := by finiteness
  have hqfin (i : ℕ) : q i ≠ ∞ := ne_of_lt ((sharedNoDropMass_le_one ν ℓ (x i) (y i)).trans_lt (by simp))
  have hq : Tendsto q atTop (𝓝 (p^2)) := (ENNReal.tendsto_toReal_iff hqfin hpfin).mp (by
    simpa only [ENNReal.toReal_pow] using sharedNoDropMass_tendsto_gap ν ℓ f x y hgap)
  have hdiff : Tendsto (fun i => p^2-q i) atTop (𝓝 0) := by
    simpa only [tsub_self,Function.comp_def] using (ENNReal.tendsto_sub (Or.inl hpfin)).comp
      (tendsto_const_nhds.prodMk_nhds hq)
  have herr : Tendsto (fun i => 2*annealedLaw ν (Cross ℓ 0 (H i) \ NoDrop ℓ 0)) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_def] using ENNReal.Tendsto.const_mul ((cross_error_tendsto_zero ν ℓ).comp hH)
      (Or.inr (by norm_num : (2:ℝ≥0∞) ≠ ∞))
  have hinv : Tendsto (fun i => (q i)⁻¹) atTop (𝓝 (p^2)⁻¹) := tendsto_inv_iff.mpr hq
  have hsum := hdiff.add herr
  rw [zero_add] at hsum
  have hprod := ENNReal.Tendsto.mul hinv (Or.inr ENNReal.zero_ne_top) hsum
    (Or.inr (ENNReal.inv_ne_top.mpr (pow_ne_zero _ hp)))
  rw [mul_zero] at hprod
  simpa only [ENNReal.toReal_zero,Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hprod

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
