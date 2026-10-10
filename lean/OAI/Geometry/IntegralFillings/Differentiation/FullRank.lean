import Mathlib
import OAI.Geometry.IntegralFillings.Differentiation.Partitions
import OAI.Geometry.IntegralFillings.Differentiation.Degenerate

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace SharpIntegralFillings.MetricDifferentiation
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
lemma exists_nat_lower_bound_iff {p : Seminorm ℝ E} (hp : Continuous p) :
    (∃ n : ℕ, ∀ v : E, ‖v‖ ≤ ((n : ℝ)+1)*p v) ↔ ∀ v, p v = 0 → v = 0 := by
  constructor
  · rintro ⟨n,hn⟩ v hv
    have := hn v
    rw [hv,mul_zero] at this
    exact norm_eq_zero.mp (le_antisymm this (norm_nonneg v))
  · intro hp0
    by_cases hE : Subsingleton E
    · exact ⟨0, fun v => by simp [Subsingleton.elim v 0]⟩
    let : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    obtain ⟨v,hv⟩ := exists_ne (0 : E)
    have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hs : (Metric.sphere (0 : E) 1).Nonempty := by
      refine ⟨‖v‖⁻¹ • v,?_⟩
      simp only [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_inv,abs_of_pos hnorm,inv_mul_cancel₀ hnorm.ne']
    obtain ⟨w,hw,hwmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hs hp.continuousOn
    have hwnorm : ‖w‖ = 1 := by simpa using hw
    have hw0 : w ≠ 0 := by intro h; simp [h] at hwnorm
    have hpw : 0 < p w := lt_of_le_of_ne (apply_nonneg p w) (by
      intro h; exact hw0 (hp0 w h.symm))
    obtain ⟨n,hn⟩ := exists_nat_gt (1 / p w)
    refine ⟨n,fun z => ?_⟩
    by_cases hz : z = 0
    · simp [hz]
    have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hzunit : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : E) 1 := by
      simp only [Metric.mem_sphere,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_inv,abs_of_pos hznorm,inv_mul_cancel₀ hznorm.ne']
    have hmin : p w ≤ p (‖z‖⁻¹ • z) := hwmin hzunit
    rw [map_smul_eq_mul,Real.norm_eq_abs,abs_inv,abs_of_pos hznorm] at hmin
    have hn' : 1 ≤ ((n : ℝ)+1)*p w := by
      have hh : 1 < (n : ℝ)*p w := (div_lt_iff₀ hpw).mp hn
      nlinarith
    calc ‖z‖ = ‖z‖*1 := (mul_one _).symm
      _ ≤ ‖z‖*(((n : ℝ)+1)*p w) := mul_le_mul_of_nonneg_left hn' (norm_nonneg z)
      _ ≤ ‖z‖*(((n : ℝ)+1)*(‖z‖⁻¹*p z)) := by
        gcongr
      _ = ((n : ℝ)+1)*p z := by field_simp

end SharpIntegralFillings.MetricDifferentiation

namespace SharpIntegralFillings.MetricDifferentiation
open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X] [SeparableSpace X] [Nonempty X]
  {f : E → X} {K : ℝ≥0}

lemma measurableSet_metricSeminorm_lower_bound (hf : LipschitzWith K f) (A : ℝ) :
    MeasurableSet {x : E | ∀ v : E, ‖v‖ ≤ A * metricSeminorm f x v} := by
  have heq : {x : E | ∀ v : E, ‖v‖ ≤ A * metricSeminorm f x v} =
      ⋂ i : ℕ, {x : E | ‖denseSeq E i‖ ≤ A * metricSeminorm f x (denseSeq E i)} := by
    ext x
    simp only [mem_ofPred_eq,mem_iInter]
    constructor
    · exact fun h i => h _
    · intro h v
      exact (denseRange_denseSeq E).induction_on v
        (isClosed_le continuous_norm ((metricSeminorm_lipschitz hf x).continuous.const_mul A)) h
  rw [heq]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le measurable_const ((measurable_metricSeminorm_apply hf _).const_mul A)

theorem exists_ae_bilipschitz_partition_of_bound
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ (⊤ : ℝ≥0∞))
    {A : ℝ≥0} (hA : 0 < A)
    (hbound : ∀ x ∈ s, ∀ v : E, ‖v‖ ≤ (A : ℝ)*metricSeminorm f x v) :
    ∃ t : ℕ → Set E,
      (∀ i, MeasurableSet (t i)) ∧ (∀ i, t i ⊆ s) ∧
      Pairwise (fun i j => Disjoint (t i) (t j)) ∧ μ (s \ ⋃ i, t i) = 0 ∧
      ∀ i, LipschitzWith K (fun x : t i => f x) ∧
        AntilipschitzWith (2*A) (fun x : t i => f x) := by
  obtain ⟨c,t,htm,hts,hdisj,ht0,hcs,hineq⟩ :=
    exists_ae_nearIsometric_partition μ hf hs hsf
      (show 0 < (A : ℝ) from hA) hbound (show (0 : ℝ) < 1/2 by norm_num)
  refine ⟨t,htm,hts,hdisj,ht0,fun i => ⟨LipschitzWith.of_dist_le_mul (fun a b => hf.dist_le_mul a b),?_⟩⟩
  apply AntilipschitzWith.of_le_mul_dist
  intro a b
  have hlo := (hineq i a a.property b b.property).1
  have hb := hbound (c i) (hcs i ⟨a,a.property⟩) ((a : E)-(b : E))
  change dist (a : E) (b : E) ≤ (↑(2*A) : ℝ)*dist (f a) (f b)
  rw [dist_eq_norm]
  push_cast
  nlinarith [mul_nonneg (show 0 ≤ (A : ℝ) from A.coe_nonneg)
    (show 0 ≤ dist (f a) (f b) - (1-(1:ℝ)/2)*metricSeminorm f (c i) ((a : E)-(b : E)) from sub_nonneg.mpr hlo)]

theorem exists_bilipschitz_fullRank_pieces
    (μ : Measure E) [μ.IsAddHaarMeasure] (hf : LipschitzWith K f)
    {s : Set E} (hs : MeasurableSet s) (hsf : μ s ≠ (⊤ : ℝ≥0∞)) :
    ∃ (t : ℕ → Set E) (J : ℕ → ℝ≥0),
      (∀ i, MeasurableSet (t i)) ∧ (∀ i, t i ⊆ s) ∧
      Pairwise (fun i j => Disjoint (t i) (t j)) ∧
      μ ((s ∩ {x | ∃ n : ℕ, ∀ v : E,
        ‖v‖ ≤ ((n : ℝ)+1)*metricSeminorm f x v}) \ ⋃ i, t i) = 0 ∧
      ∀ i, LipschitzWith K (fun x : t i => f x) ∧
        AntilipschitzWith (J i) (fun x : t i => f x) := by
  classical
  let U : ℕ → Set E := fun n => s ∩ {x | ∀ v : E,
    ‖v‖ ≤ ((n : ℝ)+1)*metricSeminorm f x v}
  have hU (n : ℕ) : MeasurableSet (U n) :=
    hs.inter (measurableSet_metricSeminorm_lower_bound hf _)
  have hUf (n : ℕ) : μ (U n) ≠ (⊤ : ℝ≥0∞) :=
    ((measure_mono inter_subset_left).trans_lt hsf.lt_top).ne
  have H (n : ℕ) := exists_ae_bilipschitz_partition_of_bound μ hf (hU n) (hUf n)
    (A := n+1) (by positivity) (by
      intro x hx v
      simpa using hx.2 v)
  choose T hTm hTs hTd hT0 hTb using H
  let e : ℕ ≃ ℕ × ℕ := Nat.pairEquiv.symm
  let V : ℕ → Set E := fun i => T (e i).1 (e i).2
  let t := disjointed V
  have htV (i : ℕ) : t i ⊆ T (e i).1 (e i).2 := disjointed_le V i
  have hcover (n : ℕ) : (⋃ j, T n j) ⊆ ⋃ i, t i := by
    rw [iUnion_disjointed]
    intro x hx
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    refine mem_iUnion.mpr ⟨e.symm (n,j),?_⟩
    simpa [V] using hj
  refine ⟨t,fun i => 2*((e i).1+1),
    fun i => MeasurableSet.disjointed (fun j => hTm _ _) i,
    fun i => (htV i).trans ((hTs _ _).trans inter_subset_left),disjoint_disjointed V,?_,?_⟩
  · have hnull (n : ℕ) : μ (U n \ ⋃ i, t i) = 0 :=
      measure_mono_null (sdiff_subset_sdiff_right (hcover n)) (hT0 n)
    apply measure_mono_null _ (measure_iUnion_null hnull)
    intro x hx
    obtain ⟨n,hn⟩ := hx.1.2
    exact mem_iUnion.mpr ⟨n,⟨⟨hx.1.1,hn⟩,hx.2⟩⟩
  · intro i
    refine ⟨LipschitzWith.of_dist_le_mul (fun a b => hf.dist_le_mul a b),?_⟩
    apply AntilipschitzWith.of_le_mul_dist
    intro a b
    exact (hTb _ _).2.le_mul_dist ⟨a,htV i a.property⟩ ⟨b,htV i b.property⟩

end SharpIntegralFillings.MetricDifferentiation

namespace SharpIntegralFillings.MetricDifferentiation
open MeasureTheory Filter Set Metric
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X]

theorem exists_lipschitz_chart_decomposition {n : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : MeasurableSet s) (hsf : volume s ≠ (⊤ : ℝ≥0∞))
    {f : s → X} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∃ (t : ℕ → Set (EuclideanSpace ℝ (Fin n)))
      (J : ℕ → ℝ≥0) (hts : ∀ i, t i ⊆ s),
      (∀ i, MeasurableSet (t i)) ∧ Pairwise (fun i j => Disjoint (t i) (t j)) ∧
      (∀ i, LipschitzWith K (fun x : t i => f ⟨x,hts i x.property⟩) ∧
        AntilipschitzWith (J i) (fun x : t i => f ⟨x,hts i x.property⟩)) ∧
      ∀ (π : Fin n → X → ℝ), (∀ i, ∃ L : ℝ≥0, LipschitzWith L (π i)) →
        ∀ᵐ x ∂volume.restrict s, x ∉ ⋃ i, t i →
          Matrix.det (fun i j => fderivWithin ℝ (scalarOn f (π i)) s x
            (EuclideanSpace.single j 1)) = 0 := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let Y := Set.range f
  let : SeparableSpace Y := (isSeparable_range hf.continuous).separableSpace
  let F : s → Y := fun x => ⟨f x,x,rfl⟩
  let e := kuratowskiEmbedding Y
  have he : Isometry e := kuratowskiEmbedding.isometry Y
  let F₀ : E → ↥(lp (fun _ : ℕ => ℝ) (⊤ : ENNReal)) :=
    fun x => if hx : x ∈ s then e (F ⟨x,hx⟩) else 0
  have hF₀ : LipschitzOnWith K F₀ s := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    dsimp only [F₀]
    rw [dite_eq_left hx,dite_eq_left hy,he.dist_eq]
    exact hf.dist_le_mul ⟨x,hx⟩ ⟨y,hy⟩
  obtain ⟨g,hg,heq⟩ := hF₀.extend_lp_infty
  let Z := Set.range g
  let : SeparableSpace Z := (isSeparable_range hg.continuous).separableSpace
  let : Nonempty Z := ⟨⟨g 0,0,rfl⟩⟩
  let G : E → Z := fun x => ⟨g x,x,rfl⟩
  have hG : LipschitzWith K G := LipschitzWith.of_dist_le_mul hg.dist_le_mul
  have hdist (y z : s) : dist (G y) (G z) = dist (f y) (f z) := by
    change dist (g y) (g z) = _
    rw [←heq y.property, ←heq z.property]
    dsimp only [F₀]
    rw [dite_eq_left y.property,dite_eq_left z.property]
    exact he.dist_eq (F y) (F z)
  let p := metricSeminorm G
  have hdiff : ∀ᵐ x ∂volume.restrict s, ∀ hx : x ∈ s,
      HasCenteredMetricDifferentialWithin s f (p x) ⟨x,hx⟩ := by
    have hd := (ae_hasCenteredMetricDifferential volume hG).filter_mono
      (ae_mono (Measure.restrict_le_self (μ := volume) (s := s)))
    filter_upwards [hd] with x hx hxs
    have hc : Tendsto (fun y : s => (y : E)) (𝓝 (⟨x,hxs⟩ : s)) (𝓝 x) :=
      continuous_subtype_val.tendsto _
    have hr := hx.comp_tendsto hc
    change (fun y : s => dist (G (y : E)) (G ((⟨x,hxs⟩ : s) : E)) -
      p x ((y : E)-x)) =o[𝓝 (⟨x,hxs⟩ : s)] (fun y : s => (y : E)-x) at hr
    have hdist' (y : s) : dist (G (y : E)) (G x) = dist (f y) (f ⟨x,hxs⟩) :=
      hdist y ⟨x,hxs⟩
    simpa only [HasCenteredMetricDifferentialWithin,hdist'] using hr
  obtain ⟨t,J,htm,hts,htd,ht0,htb⟩ := exists_bilipschitz_fullRank_pieces volume hG hs hsf
  refine ⟨t,J,hts,htm,htd,?_,?_⟩
  · intro i
    constructor
    · apply LipschitzWith.of_dist_le_mul
      intro a b
      exact hf.dist_le_mul ⟨a,hts i a.property⟩ ⟨b,hts i b.property⟩
    · apply AntilipschitzWith.of_le_mul_dist
      intro a b
      have hh := (htb i).2.le_mul_dist a b
      change dist (a : E) (b : E) ≤ (J i : ℝ)*dist (G a) (G b) at hh
      rw [hdist ⟨a,hts i a.property⟩ ⟨b,hts i b.property⟩] at hh
      exact hh
  · intro π hπ
    have hcover : ∀ᵐ x ∂volume.restrict s, (∀ v, p x v = 0 → v = 0) → x ∈ ⋃ i, t i := by
      have hz : ∀ᵐ x ∂volume, x ∉
          (s ∩ {x | ∃ n : ℕ, ∀ v : E, ‖v‖ ≤ ((n : ℝ)+1)*metricSeminorm G x v}) \ ⋃ i, t i :=
        ae_iff.mpr (by
          convert ht0 using 1
          congr 1
          ext x
          simp only [mem_ofPred_eq,not_not]
          rfl)
      filter_upwards [hz.filter_mono (ae_mono Measure.restrict_le_self),ae_restrict_mem hs] with x hx hxs hp0
      have hbound := (exists_nat_lower_bound_iff (metricSeminorm_lipschitz hG x).continuous).2 hp0
      by_contra hnot
      exact hx ⟨⟨hxs,hbound⟩,hnot⟩
    filter_upwards [hcover,ae_scalarOn_det_eq_zero_of_degenerate hs hf hdiff π hπ] with x hx hv hnot
    apply hv
    exact fun hp0 => hnot (hx hp0)

end SharpIntegralFillings.MetricDifferentiation

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

end

end OAI
