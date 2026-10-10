import Mathlib
import OAI.Geometry.CAT0Fillings.Sobolev.Completion
import OAI.Geometry.CAT0Fillings.Compactness.Ascoli
import OAI.Geometry.CAT0Fillings.Sobolev.AlmostSharp
import OAI.Geometry.CAT0Fillings.Compactness.Interpolation

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closed_sobolev_bound {p : ℝ≥0∞} {A B C : ℝ} (hA : 0 < A)
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ (u : X → ℝ) (K : ℝ≥0), LipschitzWith K u →
      A*lpNorm u p (MassMeasure.currentMassMeasure hT)^2 ≤
        B*(q.energyMeasure u).real univ+C*lpNorm u 2 (MassMeasure.currentMassMeasure hT)^2)
    (P : q.Sobolev) :
    MemLp (q.inclusion P) p (MassMeasure.currentMassMeasure hT) ∧
      A*lpNorm (q.inclusion P) p (MassMeasure.currentMassMeasure hT)^2 ≤
        B*‖q.closedGradient P‖^2+C*‖q.inclusion P‖^2 := by
  let μ := MassMeasure.currentMassMeasure hT
  obtain ⟨u,K,hu,hlim⟩ := q.exists_lipschitz_approximants P
  have hv := (q.valueProjection.continuous.tendsto (P : q.GraphAmbient)).comp hlim
  have hg := (q.gradientProjection.continuous.tendsto (P : q.GraphAmbient)).comp hlim
  change Tendsto (fun j => value (hu j)) atTop (𝓝 (q.inclusion P)) at hv
  change Tendsto (fun j => q.gradient (hu j)) atTop (𝓝 (q.closedGradient P)) at hg
  obtain ⟨s,hs,hae⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  have he : ∀ᵐ x ∂μ, ∀ j, (value (hT := hT) (hu j)) x = u j x := by
    apply ae_all_iff.mpr
    intro j
    exact ((Foundations.boundedLip_of_lipschitz (hu j)).memLp 2).coeFn_toLp
  have ha : ∀ᵐ x ∂μ, Tendsto (fun j => u (s j) x) atTop (𝓝 ((q.inclusion P) x)) := by
    filter_upwards [hae,he] with x hx hxe
    exact hx.congr' (Eventually.of_forall fun j => hxe (s j))
  let R : ℕ → ℝ := fun j => Real.sqrt ((B*‖q.gradient (hu j)‖^2+C*‖value (hT := hT) (hu j)‖^2)/A)
  let r : ℝ := Real.sqrt ((B*‖q.closedGradient P‖^2+C*‖q.inclusion P‖^2)/A)
  have hR : Tendsto R atTop (𝓝 r) :=
    (((hg.norm.pow 2).const_mul B).add ((hv.norm.pow 2).const_mul C)).div_const A |>.sqrt
  have hbu : ∀ j, eLpNorm (u j) p μ ≤ ENNReal.ofReal (R j) := by
    intro j
    rw [←ofReal_lpNorm ((Foundations.boundedLip_of_lipschitz (hu j)).memLp p)]
    apply ENNReal.ofReal_le_ofReal
    apply (Real.le_sqrt lpNorm_nonneg (div_nonneg (add_nonneg
      (mul_nonneg hB (sq_nonneg _)) (mul_nonneg hC (sq_nonneg _))) hA.le)).mpr
    apply (le_div_iff₀ hA).mpr
    have hh := hb (u j) (K j) (hu j)
    rw [q.gradient_norm_sq (hu j),norm_value]
    nlinarith
  have hfat := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := p)
    (fun j => (hu (s j)).continuous.aestronglyMeasurable) (q.inclusion P)
    (Lp.aestronglyMeasurable (q.inclusion P)) ha
  have hmaj := Filter.liminf_le_liminf (f := atTop) (Eventually.of_forall fun j => hbu (s j))
  have hlimR := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hR.comp hs.tendsto_atTop)
  simp only [Function.comp_def] at hlimR
  rw [hlimR.liminf_eq] at hmaj
  have hpbound : eLpNorm (q.inclusion P) p μ ≤ ENNReal.ofReal r := hfat.trans hmaj
  have hp : MemLp (q.inclusion P) p μ :=
    hpbound.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hp,?_⟩
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hpbound
  rw [toReal_eLpNorm,ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hreal
  have hsquare := (sq_le_sq₀ lpNorm_nonneg (Real.sqrt_nonneg _)).mpr hreal
  rw [Real.sq_sqrt (div_nonneg (add_nonneg (mul_nonneg hB (sq_nonneg _))
    (mul_nonneg hC (sq_nonneg _))) hA.le)] at hsquare
  have hh := (le_div_iff₀ hA).mp hsquare
  nlinarith

end CAT0Fillings.ChartGeometry

namespace CAT0Fillings
open Set Filter MeasureTheory MassMeasure Rearrangement RadialSobolev
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem extremal_closed_sobolev {k : ℕ} (hk : 0 < k) (hX : IsCAT0 X)
    {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hz : boundarySucc T = 0)
    (hm : 0 < mass T) (q : ChartGeometry hT.1) {d r : ℝ} (hd : 0 < d) (hr : 1 < r)
    (hfill : ∀ P : Functional X (k+1), IsIntegral (k+1) P → boundarySucc P = 0 →
      ∃ R : Functional X (k+2), IsIntegral (k+2) R ∧ boundarySucc R = P ∧
        mass R ≤ fillingCoefficient (k+1)*(mass P)^(fillingPower (k+1)))
    (hext : ∀ B : Functional X (k+2), IsIntegral (k+2) B → boundarySucc B = 0 →
      d*((mass T)^r-(mass B)^r) ≤ fillingVolume (T-B))
    {ε : ℝ} (hε : 0 < ε) (hεS : ε < (k+2:ℝ)*sphereArea (k+2)^(2/(k+2:ℝ))) :
    ∃ C ≥ (0:ℝ), ∀ P : q.Sobolev,
      MemLp (q.inclusion P) (ENNReal.ofReal (sobolevP (k+2))) (currentMassMeasure hT.1) ∧
      ((k+2:ℝ)*sphereArea (k+2)^(2/(k+2:ℝ))-ε)*
        lpNorm (q.inclusion P) (ENNReal.ofReal (sobolevP (k+2))) (currentMassMeasure hT.1)^2 ≤
      4/((k+2:ℝ)-2)*‖q.closedGradient P‖^2 + C*‖q.inclusion P‖^2 := by
  obtain ⟨C,hC,hb⟩ := extremal_almost_sobolev hk hX hT hz hm q hd hr hfill hext hε hεS
  refine ⟨C,hC,fun P => q.closed_sobolev_bound (sub_pos.mpr hεS) ?_ hC hb P⟩
  apply div_nonneg (by norm_num)
  have : (0:ℝ) < k := by exact_mod_cast hk
  linarith

end CAT0Fillings
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
open JointBV Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma norm_valueProjection_le (P : q.GraphAmbient) : ‖q.valueProjection P‖ ≤ ‖P‖ := by
  have := q.graph_norm_sq P
  nlinarith [norm_nonneg P,sq_nonneg ‖q.gradientProjection P‖]
lemma norm_gradientProjection_le (P : q.GraphAmbient) : ‖q.gradientProjection P‖ ≤ ‖P‖ := by
  have := q.graph_norm_sq P
  nlinarith [norm_nonneg P,sq_nonneg ‖q.valueProjection P‖]

lemma totallyBounded_inclusion {ι : Type*}
    (h : Slicing.NormalApprox (k+1) T) (hz : boundarySucc T = 0) (hX : IsCAT0 X)
    {p A B C : ℝ} (hp : 2 < p) (hA : 0 < A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ (u : X → ℝ) (K : ℝ≥0), LipschitzWith K u →
      A*lpNorm u (ENNReal.ofReal p) (MassMeasure.currentMassMeasure hT)^2 ≤
        B*(q.energyMeasure u).real univ+C*lpNorm u 2 (MassMeasure.currentMassMeasure hT)^2)
    (P : ι → q.Sobolev) (M : ℝ≥0) (hM : ∀ i, ‖P i‖ ≤ M) :
    TotallyBounded (range fun i => q.inclusion (P i)) := by
  classical
  apply totallyBounded_range_of_uniform_approx
  intro ε hε
  let δ := min ε 1
  have hδ : 0 < δ := lt_min hε zero_lt_one
  have ha (i : ι) : ∃ (u : X → ℝ) (K : ℝ≥0) (hu : LipschitzWith K u),
      dist (P i : q.GraphAmbient) (q.graphPoint hu) < δ := by
    have hm : (P i : q.GraphAmbient) ∈ closure (q.lipschitzGraph : Set q.GraphAmbient) := (P i).property
    obtain ⟨b,hb,hnear⟩ := Metric.mem_closure_iff.mp hm δ hδ
    obtain ⟨u,K,hu,rfl⟩ := hb
    exact ⟨u,K,hu,hnear⟩
  choose u K hu hd using ha
  have hn (i : ι) : ‖q.graphPoint (hu i)‖ ≤ (M:ℝ)+1 := by
    have hh := norm_add_le (q.graphPoint (hu i)-(P i : q.GraphAmbient)) (P i : q.GraphAmbient)
    rw [sub_add_cancel,←dist_eq_norm,dist_comm] at hh
    have hb : dist (P i : q.GraphAmbient) (q.graphPoint (hu i)) < 1 := (hd i).trans_le (min_le_right _ _)
    have hMi : ‖(P i : q.GraphAmbient)‖ ≤ M := hM i
    linarith
  have hv (i : ι) : ‖value (hT := hT) (hu i)‖ ≤ (M:ℝ)+1 :=
    (q.norm_valueProjection_le (q.graphPoint (hu i))).trans (hn i)
  have hg (i : ι) : ‖q.gradient (hu i)‖ ≤ (M:ℝ)+1 :=
    (q.norm_gradientProjection_le (q.graphPoint (hu i))).trans (hn i)
  have hUi (i : ι) : ∃ U : ℝ≥0, ∀ x, |u i x| ≤ U := by
    obtain ⟨R,hR⟩ := (boundedLip_of_lipschitz (hu i)).2
    exact ⟨⟨max R 0,le_max_right _ _⟩,fun x => (hR x).trans (le_max_left _ _)⟩
  choose U hU using hUi
  let D := Real.sqrt (((B+C)*((M:ℝ)+1)^2)/A)
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have huv (i : ι) : lpNorm (u i) (ENNReal.ofReal p) (MassMeasure.currentMassMeasure hT) ≤ D := by
    apply (Real.le_sqrt lpNorm_nonneg (div_nonneg (mul_nonneg (add_nonneg hB hC) (sq_nonneg _)) hA.le)).mpr
    apply (le_div_iff₀ hA).mpr
    have hh := hb (u i) (K i) (hu i)
    rw [←q.gradient_norm_sq (hu i),←norm_value (hu i)] at hh
    have hv2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ (M:ℝ)+1)).mpr (hv i)
    have hg2 := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ (M:ℝ)+1)).mpr (hg i)
    nlinarith [mul_le_mul_of_nonneg_left hv2 hC,mul_le_mul_of_nonneg_left hg2 hB]
  refine ⟨fun i => value (hT := hT) (hu i),
    q.totallyBounded_value h hz hX u K U hu hU (M+1) hv hg hp ⟨D,hD⟩ huv,?_⟩
  intro i
  have hh := q.norm_valueProjection_le ((P i : q.GraphAmbient)-q.graphPoint (hu i))
  rw [map_sub] at hh
  have hh' : dist (q.inclusion (P i)) (value (hT := hT) (hu i)) ≤
      dist (P i : q.GraphAmbient) (q.graphPoint (hu i)) := by
        simpa [dist_eq_norm,inclusion] using hh
  exact hh'.trans_lt ((hd i).trans_le (min_le_left _ _))

theorem inclusion_compact
    (h : Slicing.NormalApprox (k+1) T) (hz : boundarySucc T = 0) (hX : IsCAT0 X)
    {p A B C : ℝ} (hp : 2 < p) (hA : 0 < A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ (u : X → ℝ) (K : ℝ≥0), LipschitzWith K u →
      A*lpNorm u (ENNReal.ofReal p) (MassMeasure.currentMassMeasure hT)^2 ≤
        B*(q.energyMeasure u).real univ+C*lpNorm u 2 (MassMeasure.currentMassMeasure hT)^2) :
    IsCompactOperator q.inclusion := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall q.inclusion.toLinearMap zero_lt_one).mpr
  have ht := q.totallyBounded_inclusion h hz hX hp hA hB hC hb
    (fun P : closedBall (0 : q.Sobolev) 1 => (P : q.Sobolev)) 1
    (fun P => by simpa only [mem_closedBall,dist_zero_right,NNReal.coe_one] using P.property)
  have he : (range fun P : closedBall (0 : q.Sobolev) 1 => q.inclusion (P : q.Sobolev)) =
      q.inclusion '' closedBall 0 1 := by ext u; simp
  rw [he] at ht
  exact isCompact_iff_totallyBounded_isComplete.mpr ⟨ht.closure,isClosed_closure.isComplete⟩

end CAT0Fillings.ChartGeometry
end

end OAI
