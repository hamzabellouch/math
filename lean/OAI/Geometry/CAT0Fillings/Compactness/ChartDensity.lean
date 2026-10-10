import Mathlib
import OAI.Geometry.CAT0Fillings.Gradient.Pairing
import OAI.Geometry.CAT0Fillings.Compactness.IntrinsicBV

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
open Foundations MassMeasure Slicing BorelCoefficients BorelRestriction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma exists_exact_inverse_coordinates (i : ℕ) :
    ∃ (F : Fin n → X → ℝ) (K : ℝ≥0), (∀ a, LipschitzWith K (F a)) ∧
      (∀ z ∈ (q.chart i).domain, coordinateMap F ((q.chart i).paramExtended z) = z) ∧
      ∀ᵐ z ∂volume.restrict (q.chart i).domain, (q.chart i).jacobian F z = 1 := by
  obtain ⟨K₁,K₂,hK₁,hK₂⟩ := (q.chart i).bilipschitz
  have hrow : ∀ a y (hy : y ∈ (q.chart i).domain) z (hz : z ∈ (q.chart i).domain),
      |EuclideanSpace.proj a y-EuclideanSpace.proj a z| ≤
        (K₂:ℝ)*dist ((q.chart i).param ⟨y,hy⟩) ((q.chart i).param ⟨z,hz⟩) := by
    intro a y hy z hz
    have hh := PiLp.norm_apply_le (p := (2:ℝ≥0∞)) (y-z) a
    have he : |EuclideanSpace.proj a y-EuclideanSpace.proj a z| ≤ dist y z := by
      change |y.ofLp a-z.ofLp a| ≤ ‖y-z‖
      simpa only [Real.norm_eq_abs,PiLp.sub_apply] using hh
    exact he.trans (hK₂.le_mul_dist ⟨y,hy⟩ ⟨z,hz⟩)
  obtain ⟨F,hF,hFeq,hjac⟩ := (q.chart i).exists_inverse_coordinate_tests
    (q.chart i).borel subset_rfl (fun a => EuclideanSpace.proj a) K₂ hrow
  refine ⟨F,K₂,hF,?_,?_⟩
  · intro z hz
    ext a
    have hh := hFeq a z hz
    change F a ((q.chart i).paramExtended z) = (EuclideanSpace.proj a) z
    simpa only [IntegerChart.scalar,IntegerChart.paramExtended,dite_eq_left hz] using hh
  · have he : (Matrix.of fun i j : Fin n => EuclideanSpace.proj i (EuclideanSpace.single j (1:ℝ))) = 1 := by
      ext i j
      simp [Matrix.one_apply]
    simpa only [he,Matrix.det_one] using hjac

lemma chart_isolated_action (i : ℕ) {b : X → ℝ} (hb : BoundedLip b)
    (F : Fin n → X → ℝ) (hF : ∀ a, ∃ K : ℝ≥0, LipschitzWith K (F a)) :
    currentBorelAction T ((q.chart i).image.indicator b) F = (q.chart i).action b F := by
  rw [currentBorelAction_eq hT,←restrictCurrent_apply hT (q.chart i).image ⟨hb,hF⟩]
  rw [chartFamily_restrict_eq hT q.chart q.disjoint q.current q.summable q.action i]

lemma ae_isolated_projected_density (h : NormalApprox n T) (hX : IsCAT0 X)
    (i : ℕ) (F : Fin n → X → ℝ) {K : ℝ≥0} (hF : ∀ a, LipschitzWith K (F a))
    (hFinv : ∀ z ∈ (q.chart i).domain, coordinateMap F ((q.chart i).paramExtended z) = z)
    (hjac : ∀ᵐ z ∂volume.restrict (q.chart i).domain, (q.chart i).jacobian F z = 1)
    {u : X → ℝ} {L : ℝ≥0} (hu : LipschitzWith L u) :
    (fun z => currentBorelAction (fullSlice h F z) ((q.chart i).image.indicator u) (fun j => Fin.elim0 j)) =ᵐ[volume]
      (q.chart i).domain.indicator (fun z => ((q.chart i).multiplicity z:ℝ)*u ((q.chart i).paramExtended z)) := by
  let C := q.chart i
  obtain ⟨U,hU⟩ := (boundedLip_of_lipschitz hu).2
  let B : ℝ≥0 := ⟨max U 0,le_max_right _ _⟩
  have huB x : |u x| ≤ B := (hU x).trans (le_max_left _ _)
  have hbu : Measurable (C.image.indicator u) := hu.continuous.measurable.indicator C.measurableSet_image
  have hbb x : |C.image.indicator u x| ≤ B := by
    by_cases hx : x ∈ C.image
    · simpa only [indicator_of_mem hx] using huB x
    · simpa only [indicator_of_notMem hx,abs_zero] using B.coe_nonneg
  have hi := (fullSlice_borel_integral h hX F (fun a => boundedLip_of_lipschitz (hF a)) hbu B hbb).1
  have hden := integrable_weighted_comp (volume.restrict C.domain) C.measurable_paramExtended
    C.integrable hu.continuous.measurable ⟨B,huB⟩
  have hden' : Integrable (C.domain.indicator (fun z => (C.multiplicity z:ℝ)*u (C.paramExtended z))) :=
    (integrable_indicator_iff C.borel).mpr hden
  apply ae_eq_of_integral_contDiff_smul_eq hi.locallyIntegrable hden'.locallyIntegrable
  intro φ hφ hφs
  obtain ⟨J,hJ⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφs hφ (by simp)
  obtain ⟨M,hM⟩ := coordinateMap_lipschitz F hF
  have hφb : BoundedLip φ := by
    obtain ⟨V,hV⟩ := hφ.continuous.bounded_above_of_compact_support hφs
    exact ⟨⟨J,hJ⟩,V,fun x => by simpa only [Real.norm_eq_abs] using hV x⟩
  obtain ⟨V,hV⟩ := hφb.2
  let D : ℝ≥0 := ⟨max V 0,le_max_right _ _⟩
  have hφD x : |φ x| ≤ D := (hV x).trans (le_max_left _ _)
  have hw := fullSlice_borel_weighted_integral h hX F hF hbu B hbb hφ.continuous.measurable D hφD
  have he : (fun x => φ (coordinateMap F x)*C.image.indicator u x) =
      C.image.indicator (fun x => φ (coordinateMap F x)*u x) := by
    ext x; by_cases hx : x ∈ C.image <;> simp [hx]
  simp only [smul_eq_mul]
  have hbφ : BoundedLip (fun x => φ (coordinateMap F x)) := boundedLip_of_lipschitz (hJ.comp hM)
  have hprod := hbφ.mul (boundedLip_of_lipschitz hu)
  rw [←hw.2,he,q.chart_isolated_action i hprod F (fun a => ⟨K,hF a⟩)]
  rw [IntegerChart.action,ite_eq_left ⟨hprod,fun a => ⟨K,hF a⟩⟩]
  have hei : (fun z => φ z*C.domain.indicator (fun z => (C.multiplicity z:ℝ)*u (C.paramExtended z)) z) =
      C.domain.indicator (fun z => φ z*((C.multiplicity z:ℝ)*u (C.paramExtended z))) := by
    ext z; by_cases hz : z ∈ C.domain <;> simp [hz]
  rw [hei,integral_indicator C.borel]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem C.borel,hjac] with z hz hjz
  have hh := hFinv z hz
  simp only [IntegerChart.scalar,IntegerChart.paramExtended,dite_eq_left hz] at hh ⊢
  change (C.multiplicity z:ℝ)*(_)*C.jacobian F z = _
  rw [hjz,hh]
  have hzC : z ∈ C.domain := hz
  simp only [dite_eq_left hzC]
  ring

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory Matrix Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {n : ℕ} {T : Functional X n}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma ae_chart_jacobian_le (i : ℕ) {K : ℝ≥0}
    (hK : LipschitzWith K (q.chart i).param) :
    ∀ᵐ z ∂volume.restrict (q.chart i).domain,
      Real.sqrt (q.gram i z).det ≤ (K:ℝ)^n := by
  filter_upwards [q.differential i,ae_restrict_mem (q.chart i).borel,
    Besicovitch.ae_tendsto_measure_inter_div volume (q.chart i).domain] with z hz hzi hzd
  have hb : ∀ v, q.field i z v ≤ (K:ℝ)*‖v‖ := by
    apply (hz.1 hzi).seminorm_le_on_piece volume subset_rfl hzd (q := normSeminorm ℝ (Euc n))
    intro y hy
    change dist ((q.chart i).param ⟨y,hy⟩) ((q.chart i).param ⟨z,hzi⟩) ≤ (K:ℝ)*‖y-z‖
    simpa only [Subtype.dist_eq,dist_eq_norm] using hK.dist_le_mul ⟨y,hy⟩ ⟨z,hzi⟩
  apply sqrt_det_le_pow_of_quadratic_bound _
    (polarizationMatrix_posDef _ _ hz.2.2 hz.2.1).posSemidef K.coe_nonneg
  intro v
  let w : Euc n := WithLp.toLp 2 v
  have hrepr : (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.repr w = v := by ext j; simp [w]
  have he : v ⬝ᵥ (q.gram i z).mulVec v = (q.field i z w)^2 := by
    simpa only [gram,hrepr] using polarizationMatrix_quadratic
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (q.field i z) hz.2.2 hz.2.1 w
  change Real.sqrt (v ⬝ᵥ (q.gram i z).mulVec v) ≤ _
  rw [he,Real.sqrt_sq (apply_nonneg _ _)]
  exact hb w

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
lemma integral_abs_mul_le_lpNorm_two {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, |f x| * |g x| ∂μ) ≤ lpNorm f 2 μ*lpNorm g 2 μ := by
  have hp : (2:ℝ).HolderConjugate 2 := by norm_num [Real.holderConjugate_iff]
  have hh := integral_mul_norm_le_Lp_mul_Lq hp (by simpa using hf) (by simpa using hg)
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf.aestronglyMeasurable,
    lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hg.aestronglyMeasurable]
  simpa only [Real.norm_eq_abs,ENNReal.toReal_ofNat,one_div] using hh

namespace BorelCoefficients
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ]

noncomputable def lipToL2 : lipAlgebra (X := X) →ₗ[ℝ] Lp ℝ 2 μ :=
  (ContinuousMap.toLp 2 μ ℝ).toLinearMap.comp (lipAlgebra (X := X)).val.toLinearMap

lemma lipToL2_dense : DenseRange (lipToL2 μ) := by
  apply (ContinuousMap.toLp_denseRange ℝ μ ℝ (by simp : (2:ℝ≥0∞) ≠ ∞)).comp
    lipAlgebra_dense (ContinuousMap.toLp 2 μ ℝ).continuous

lemma exists_lipschitz_L2_approximation {b : X → ℝ} (hb : MemLp b 2 μ) :
    ∃ f : ℕ → lipAlgebra (X := X),
      Tendsto (fun j => lpNorm (fun x => (f j).val x-b x) 2 μ) atTop (𝓝 0) := by
  obtain ⟨u,hu,hulim⟩ := mem_closure_iff_seq_limit.mp ((lipToL2_dense μ) (hb.toLp b))
  choose f hf using hu
  have hfun : (fun j => lipToL2 μ (f j)) = u := funext hf
  have hnorm := (tendsto_iff_norm_sub_tendsto_zero).mp (hfun ▸ hulim)
  refine ⟨f,?_⟩
  convert hnorm using 1
  funext j
  rw [←lpNorm_Lp]
  rw [←toReal_eLpNorm,←toReal_eLpNorm]
  congr 1
  apply eLpNorm_congr_ae
  filter_upwards [Lp.coeFn_sub (lipToL2 μ (f j)) (hb.toLp b),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ (f j).val,hb.coeFn_toLp] with x hx hfx hbx
  change (f j).val x-b x = (lipToL2 μ (f j)-hb.toLp b) x
  rw [hx]
  change _ = (ContinuousMap.toLp 2 μ ℝ (f j).val) x-(hb.toLp b) x
  rw [hfx,hbx]

end BorelCoefficients
end CAT0Fillings
end

end OAI
