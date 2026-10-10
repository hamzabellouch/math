import OAI.Geometry.Perimeter.Regularity.ExistsDiameterCoverOfHausdorffZero

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
namespace RPI.Boundary

theorem continuousWithinAt_surfaceGradient_of_local_level {n : ℕ}
    {S U : Set (Space n)} {f g : Space n → ℝ} {x : Space n}
    (hU : IsOpen U) (hxU : x ∈ U) (hxS : x ∈ S)
    (hf : ContDiffOn ℝ 1 f U) (hdf : ∀ y ∈ U, fderiv ℝ f y ≠ 0)
    (hlevel : ∀ y ∈ U, y ∈ S ↔ f y = 0)
    (hg : ContDiffAt ℝ 1 g x) :
    ContinuousWithinAt (surfaceGradient S g) S x := by
  let F : Space n → Space n := fun y ↦ gradient g y -
    (inner ℝ (gradient f y) (gradient g y) / ‖gradient f y‖ ^ 2) • gradient f y
  have hformula : ∀ y ∈ S ∩ U, surfaceGradient S g y = F y := by
    intro y hy
    apply surfaceGradient_eq_level_formula (hf.contDiffAt (hU.mem_nhds hy.2)) (hdf y hy.2)
    filter_upwards [hU.mem_nhds hy.2] with z hz
    rw [(hlevel y hy.2).mp hy.1]
    exact hlevel z hz
  have hf' : ContinuousAt (gradient f) x :=
    continuousAt_gradient_of_contDiffAt (hf.contDiffAt (hU.mem_nhds hxU))
  have hg' : ContinuousAt (gradient g) x := continuousAt_gradient_of_contDiffAt hg
  have hgn : gradient f x ≠ 0 := by
    intro he
    apply hdf x hxU
    rw [← toDual_gradient, he, map_zero]
  have hF : ContinuousAt F x :=
    hg'.sub (((hf'.inner hg').div (hf'.norm.pow 2)
      (pow_ne_zero _ (norm_ne_zero_iff.mpr hgn))).smul hf')
  apply hF.continuousWithinAt.congr_of_eventuallyEq _ (hformula x ⟨hxS, hxU⟩)
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hxU)] with y hyS hyU
  exact hformula y ⟨hyS, hyU⟩

end RPI.Boundary

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
namespace RPI.Boundary

theorem surfaceGradient_aestronglyMeasurable_of_regular_locus {n : ℕ} (hn : 8 ≤ n)
    {S Z : Set (Space n)} (hS : MeasurableSet S) (hZ : MeasurableSet Z)
    (hdim : dimH Z ≤ (n - 8 : ℕ))
    (hreg : ∀ x ∈ S \ Z, ∃ U : Set (Space n), IsOpen U ∧ x ∈ U ∧
      ∃ f : Space n → ℝ, ContDiffOn ℝ 1 f U ∧
        (∀ y ∈ U, fderiv ℝ f y ≠ 0) ∧
        (∀ y ∈ U, y ∈ S ↔ f y = 0))
    {g : Space n → ℝ} (hg : ContDiff ℝ 1 g) :
    AEStronglyMeasurable (surfaceGradient S g) (surfaceMeasure S) := by
  have hc : ContinuousOn (surfaceGradient S g) (S \ Z) := by
    intro x hx
    obtain ⟨U, hU, hxU, f, hf, hdf, hlevel⟩ := hreg x hx
    exact (continuousWithinAt_surfaceGradient_of_local_level hU hxU hx.1 hf hdf
      hlevel hg.contDiffAt).mono sdiff_subset
  have hs : ∀ᵐ x ∂surfaceMeasure S, x ∈ S := ae_restrict_mem hS
  have hz : ∀ᵐ x ∂surfaceMeasure S, x ∉ Z := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using
      surfaceMeasure_zero_of_singular_dim hn S Z hdim
  have hregular : ∀ᵐ x ∂surfaceMeasure S, x ∈ S \ Z := by
    filter_upwards [hs, hz] with x hx hzx
    exact ⟨hx, hzx⟩
  have hmeas := hc.aestronglyMeasurable (μ := surfaceMeasure S) (hS.diff hZ)
  rwa [Measure.restrict_eq_self_of_ae_mem hregular] at hmeas

end RPI.Boundary

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
namespace RPI.Boundary

theorem exists_geometric_capacity_sequence {n : ℕ} (hn : 8 ≤ n)
    {S Z : Set (Space n)} (hS : IsClosed S) (V : Set (Space n))
    (hZc : IsCompact Z) (hZd : dimH Z ≤ (n - 8 : ℕ))
    (hreg : ∀ x ∈ S \ Z, ∃ U : Set (Space n), IsOpen U ∧ x ∈ U ∧
      ∃ f : Space n → ℝ, ContDiffOn ℝ 1 f U ∧
        (∀ y ∈ U, fderiv ℝ f y ≠ 0) ∧
        (∀ y ∈ U, y ∈ S ↔ f y = 0))
    {A r₀ : ℝ} (hA : 0 < A) (hr₀ : 0 < r₀)
    (hgrowth : ∀ c ∈ Z, ∀ r : ℝ, 0 < r → r < r₀ →
      (surfaceMeasure S).restrict V (Metric.ball c r) ≤
        ENNReal.ofReal (A * r ^ (n - 1))) :
    ∃ χ : ℕ → Space n → ℝ,
      (∀ i, ContDiff ℝ ∞ (χ i) ∧ (∀ x, χ i x ∈ Icc (0 : ℝ) 1) ∧
        (∃ U : Set (Space n), IsOpen U ∧ Z ⊆ U ∧ ∀ x ∈ U, χ i x = 0) ∧
        MemLp (surfaceGradient S (χ i)) 2 ((surfaceMeasure S).restrict V)) ∧
      (∀ᵐ x ∂(surfaceMeasure S).restrict V,
        Tendsto (fun i ↦ χ i x) atTop (𝓝 1)) ∧
      Tendsto (fun i ↦ vectorEnergy ((surfaceMeasure S).restrict V)
        (surfaceGradient S (χ i))) atTop (𝓝 0) := by
  apply exists_memLp_capacity_sequence hn S V Z hZc hZd _ hA hr₀ hgrowth
  intro f hf
  exact (surfaceGradient_aestronglyMeasurable_of_regular_locus hn hS.measurableSet
    hZc.isClosed.measurableSet hZd hreg (hf.of_le (by norm_num))).mono_measure
      Measure.restrict_le_self

end RPI.Boundary

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
namespace RPI

theorem vectorEnergy_sub_tendsto_zero_of_toLp_tendsto
    {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {μ : Measure X} {F : ℕ → X → V} {G : X → V}
    (hF : ∀ i, MemLp (F i) 2 μ) (hG : MemLp G 2 μ)
    (ht : Tendsto (fun i ↦ (hF i).toLp (F i)) atTop (𝓝 (hG.toLp G))) :
    Tendsto (fun i ↦ vectorEnergy μ (fun x ↦ F i x - G x)) atTop (𝓝 0) := by
  have he : (fun i ↦ vectorEnergy μ (fun x ↦ F i x - G x)) =
      (fun i ↦ ‖(hF i).toLp (F i) - hG.toLp G‖ₑ ^ 2) := by
    funext i
    exact vectorEnergy_eq_enorm_toLp_sq ((hF i).sub hG)
  rw [he]
  simpa only [sub_self, enorm_zero, zero_pow (by decide : 2 ≠ 0)] using
    (ENNReal.Tendsto.pow (ht.sub (tendsto_const_nhds (x := hG.toLp G))).enorm (n := 2))

namespace Boundary

theorem exists_compact_energy_approximants_of_mem_sobolevGraph {n : ℕ}
    (S V : Set (Space n)) (hV : Bornology.IsBounded V) (hVm : MeasurableSet V)
    {h : Space n → ℝ} {G : Space n → Space n}
    (hh : MemLp h 2 ((surfaceMeasure S).restrict V))
    (hG : MemLp G 2 ((surfaceMeasure S).restrict V))
    (hp : (hh.toLp h, hG.toLp G) ∈ closure (smoothGradientGraph S V)) :
    ∃ φ : ℕ → Space n → ℝ,
      (∀ j, ContDiff ℝ ∞ (φ j) ∧ HasCompactSupport (φ j)) ∧
      Tendsto (fun j ↦ ∫⁻ x, ENNReal.ofReal (|φ j x - h x| ^ 2)
        ∂(surfaceMeasure S).restrict V) atTop (𝓝 0) ∧
      Tendsto (fun j ↦ ∫⁻ x, ENNReal.ofReal
        (‖surfaceGradient S (φ j) x - G x‖ ^ 2)
        ∂(surfaceMeasure S).restrict V) atTop (𝓝 0) := by
  obtain ⟨φ, hφs, hφ, hDφ, hlim⟩ :=
    exists_compact_approximants_of_mem_sobolevGraph S V hV hVm hh hG hp
  refine ⟨φ, hφs, ?_, ?_⟩
  · simpa only [vectorEnergy, Real.norm_eq_abs] using
      vectorEnergy_sub_tendsto_zero_of_toLp_tendsto hφ hh hlim.fst_nhds
  · exact vectorEnergy_sub_tendsto_zero_of_toLp_tendsto hDφ hG hlim.snd_nhds

end Boundary
end RPI

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
namespace RPISingularHarnack
abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)

def HasHalfspaceBlowup {n : ℕ} (E : Set (Euc n)) (x v : Euc n) : Prop :=
  ‖v‖ = 1 ∧
  Tendsto (fun r : ℝ =>
    (r ^ n)⁻¹ * ∫ y in Metric.ball x r,
      |E.indicator (fun _ => (1 : ℝ)) y -
        {z | inner ℝ (z - x) v < 0}.indicator (fun _ => (1 : ℝ)) y|)
    (𝓝[>] (0 : ℝ)) (𝓝 0)

def approximateNormal {n : ℕ} (E : Set (Euc n)) (x : Euc n) : Euc n := by
  classical
  exact if h : ∃ v, HasHalfspaceBlowup E x v then Classical.choose h else 0

def tangentialGradient {n : ℕ} (E : Set (Euc n)) (φ : Euc n → ℝ)
    (x : Euc n) : Euc n :=
  gradient φ x - (inner ℝ (gradient φ x) (approximateNormal E x)) •
    approximateNormal E x

theorem eventually_sublevel_membership {n : ℕ} {E : Set (Euc n)}
    {f : Euc n → ℝ} {x z : Euc n} {L : Euc n →L[ℝ] ℝ}
    (hd : HasFDerivAt f L x) (hx : f x = 0)
    (hlocal : ∀ᶠ y in 𝓝 x, y ∈ E ↔ f y < 0) (hz : L z ≠ 0) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, x + r • z ∈ E ↔ L z < 0 := by
  have hp : HasDerivAt (fun r : ℝ ↦ x + r • z) z 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const z).const_add x
  have hc : HasDerivAt (fun r : ℝ ↦ f (x + r • z)) (L z) 0 := by
    exact (show HasFDerivAt f L (x + (0 : ℝ) • z) from by simpa using hd).comp_hasDerivAt 0 hp
  have ht : Tendsto (fun r : ℝ ↦ r⁻¹ * f (x + r • z)) (𝓝[>] 0) (𝓝 (L z)) := by
    simpa [hx] using hc.tendsto_slope_zero_right
  have hm : ∀ᶠ r : ℝ in 𝓝[>] 0, x + r • z ∈ E ↔ f (x + r • z) < 0 :=
    (show Tendsto (fun r : ℝ ↦ x + r • z) (𝓝[>] 0) (𝓝 x) from
      (show Tendsto (fun r : ℝ ↦ x + r • z) (𝓝 0) (𝓝 x) from by
        simpa [ContinuousAt] using hp.continuousAt).mono_left nhdsWithin_le_nhds).eventually hlocal
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · filter_upwards [hm, ht.eventually (gt_mem_nhds hneg), self_mem_nhdsWithin] with r hm hr hpr
    have hfr : f (x + r • z) < 0 := by
      have hi : 0 < r⁻¹ := inv_pos.mpr hpr
      nlinarith
    simp only [hm, hfr, hneg]
  · filter_upwards [hm, ht.eventually (lt_mem_nhds hpos), self_mem_nhdsWithin] with r hm hr hpr
    have hfr : 0 < f (x + r • z) := by
      have hi : 0 < r⁻¹ := inv_pos.mpr hpr
      nlinarith
    simp only [hm, not_lt.mpr hfr.le, not_lt.mpr hpos.le]

theorem normalized_ball_integral {n : ℕ} (g : Euc n → ℝ) (x : Euc n)
    {r : ℝ} (hr : 0 < r) :
    (r ^ n)⁻¹ * ∫ y in Metric.ball x r, g y =
      ∫ z in Metric.ball (0 : Euc n) 1, g (x + r • z) := by
  have hc := Measure.integral_comp_smul_of_nonneg (volume : Measure (Euc n))
    (fun y ↦ (Metric.ball x r).indicator g (x + y)) r (hR := hr.le)
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul,
    integral_add_left_eq_self, integral_indicator measurableSet_ball] at hc
  rw [← hc, ← integral_indicator measurableSet_ball]
  apply integral_congr_ae
  filter_upwards [] with z
  have hm : x + r • z ∈ Metric.ball x r ↔ z ∈ Metric.ball (0 : Euc n) 1 := by
    simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
      sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    constructor <;> intro h <;> nlinarith
  by_cases hz : z ∈ Metric.ball (0 : Euc n) 1
  · simp [hz, hm.mpr hz]
  · have hn : x + r • z ∉ Metric.ball x r := fun h ↦ hz (hm.mp h)
    rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hz]

theorem ae_linear_ne_zero {n : ℕ} {L : Euc n →L[ℝ] ℝ} (hL : L ≠ 0) :
    ∀ᵐ z ∂(volume : Measure (Euc n)), L z ≠ 0 := by
  have hk : L.ker ≠ ⊤ := by
    intro hk
    apply hL
    ext z
    have hz : z ∈ L.ker := hk ▸ Submodule.mem_top
    exact hz
  have hn : (volume : Measure (Euc n)) {z | L z = 0} = 0 :=
    Measure.addHaar_submodule (volume : Measure (Euc n)) L.ker hk
  simpa only [ae_iff, not_not] using hn

theorem halfspace_indicator_rescale {n : ℕ} (x v z : Euc n) {r : ℝ} (hr : 0 < r) :
    {y | inner ℝ (y - x) v < 0}.indicator (fun _ ↦ (1 : ℝ)) (x + r • z) =
      {y | inner ℝ y v < 0}.indicator (fun _ ↦ (1 : ℝ)) z := by
  have hm : inner ℝ ((x + r • z) - x) v < 0 ↔ inner ℝ z v < 0 := by
    simp only [add_sub_cancel_left, real_inner_smul_left]
    constructor <;> intro h <;> nlinarith
  simp only [Set.indicator, Set.mem_ofPred_eq, hm]

theorem hasHalfspaceBlowup_of_regular_sublevel {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) {f : Euc n → ℝ} {x v : Euc n} {L : Euc n →L[ℝ] ℝ}
    (hd : HasFDerivAt f L x) (hx : f x = 0)
    (hlocal : ∀ᶠ y in 𝓝 x, y ∈ E ↔ f y < 0)
    (hv : ‖v‖ = 1) {a : ℝ} (ha : 0 < a)
    (hL : ∀ z, L z = a * inner ℝ z v) : HasHalfspaceBlowup E x v := by
  have hLn : L ≠ 0 := by
    intro he
    have hval := hL v
    simp only [he, zero_apply, real_inner_self_eq_norm_sq, hv,
      one_pow, mul_one] at hval
    linarith
  let H : Set (Euc n) := {z | inner ℝ z v < 0}
  have hH : MeasurableSet H :=
    (isOpen_lt (continuous_id.inner continuous_const) continuous_const).measurableSet
  let F : ℝ → Euc n → ℝ := fun r z ↦
    |E.indicator (fun _ ↦ (1 : ℝ)) (x + r • z) - H.indicator (fun _ ↦ (1 : ℝ)) z|
  have hsign : ∀ z, L z < 0 ↔ inner ℝ z v < 0 := by
    intro z
    rw [hL]
    constructor <;> intro h <;> nlinarith
  have hmeas : ∀ r, AEStronglyMeasurable (F r)
      (volume.restrict (Metric.ball (0 : Euc n) 1)) := by
    intro r
    have he : Measurable (E.indicator (fun _ : Euc n ↦ (1 : ℝ))) :=
      measurable_const.indicator hE
    have hh : Measurable (H.indicator (fun _ : Euc n ↦ (1 : ℝ))) :=
      measurable_const.indicator hH
    have hm : Measurable (fun z : Euc n ↦ x + r • z) :=
      measurable_const.add (measurable_id.const_smul r)
    exact ((he.comp hm).sub hh).abs.aestronglyMeasurable
  have hb : ∀ r, ∀ᵐ z ∂volume.restrict (Metric.ball (0 : Euc n) 1), ‖F r z‖ ≤ 1 := by
    intro r
    filter_upwards [] with z
    by_cases he : x + r • z ∈ E <;> by_cases hh : z ∈ H <;> simp [F, he, hh]
  have ht : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : Euc n) 1),
      Tendsto (fun r ↦ F r z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    filter_upwards [ae_restrict_of_ae (ae_linear_ne_zero hLn)] with z hz
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_sublevel_membership hd hx hlocal hz] with r hr
    have hmem : x + r • z ∈ E ↔ z ∈ H := hr.trans (hsign z)
    by_cases he : x + r • z ∈ E
    · simp [F, he, hmem.mp he]
    · have hhn : z ∉ H := fun hh ↦ he (hmem.mpr hh)
      simp only [F, Set.indicator_of_notMem he, Set.indicator_of_notMem hhn,
        sub_self, abs_zero]
  have hi : Integrable (fun _ : Euc n ↦ (1 : ℝ))
      (volume.restrict (Metric.ball 0 1)) := integrableOn_const measure_ball_lt_top.ne
  have hconv := tendsto_integral_filter_of_dominated_convergence
    (fun _ : Euc n ↦ (1 : ℝ)) (Eventually.of_forall hmeas) (Eventually.of_forall hb) hi ht
  refine ⟨hv, ?_⟩
  have heq : ∀ᶠ r : ℝ in 𝓝[>] 0,
      (r ^ n)⁻¹ * (∫ y in Metric.ball x r,
        |E.indicator (fun _ ↦ (1 : ℝ)) y -
          {z | inner ℝ (z - x) v < 0}.indicator (fun _ ↦ (1 : ℝ)) y|) =
        ∫ z in Metric.ball (0 : Euc n) 1, F r z := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [normalized_ball_integral _ x hr]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [halfspace_indicator_rescale x v z hr, F, H]
  exact (show Tendsto (fun r ↦ ∫ z in Metric.ball (0 : Euc n) 1, F r z)
    (𝓝[>] (0 : ℝ)) (𝓝 0) from by simpa only [integral_zero] using hconv).congr' (Filter.EventuallyEq.symm heq)

theorem hasHalfspaceBlowup_gradient {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) {f : Euc n → ℝ} {x : Euc n}
    (hd : DifferentiableAt ℝ f x) (hx : f x = 0) (hdf : fderiv ℝ f x ≠ 0)
    (hlocal : ∀ᶠ y in 𝓝 x, y ∈ E ↔ f y < 0) :
    HasHalfspaceBlowup E x (‖gradient f x‖⁻¹ • gradient f x) := by
  have hg : gradient f x ≠ 0 := by
    intro he
    apply hdf
    ext z
    rw [← inner_gradient_left, he, inner_zero_left]
    rfl
  have hng : 0 < ‖gradient f x‖ := norm_pos_iff.mpr hg
  apply hasHalfspaceBlowup_of_regular_sublevel hE hd.hasFDerivAt hx hlocal
    (a := ‖gradient f x‖)
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hng.le), inv_mul_cancel₀ hng.ne']
  · exact hng
  · intro z
    rw [real_inner_smul_right, ← inner_gradient_left, real_inner_comm]
    field_simp

theorem halfspace_wedge_nonempty {n : ℕ} {v w : Euc n}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) (hne : v ≠ w) :
    (Metric.ball (0 : Euc n) 1 ∩
      {z | inner ℝ z v < 0} ∩ {z | 0 < inner ℝ z w}).Nonempty := by
  have hdiff : 0 < ‖w - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  have hinner : inner ℝ w v < 1 := by
    have hs := norm_sub_sq_real w v
    rw [hv, hw] at hs
    nlinarith [sq_pos_of_pos hdiff]
  refine ⟨(1 / 4 : ℝ) • (w - v), ⟨?_, ?_⟩, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right, norm_smul]
    have hn : ‖w - v‖ ≤ 2 := (norm_sub_le w v).trans (by rw [hw, hv]; norm_num)
    norm_num
    linarith
  · simp only [Set.mem_ofPred_eq, real_inner_smul_left, inner_sub_left,
      real_inner_self_eq_norm_sq, hv]
    nlinarith
  · simp only [Set.mem_ofPred_eq, real_inner_smul_left, inner_sub_left,
      real_inner_self_eq_norm_sq, hw, real_inner_comm w v]
    nlinarith

theorem eq_of_halfspace_indicator_ae {n : ℕ} {v w : Euc n}
    (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (he : {z | inner ℝ z v < 0}.indicator (fun _ ↦ (1 : ℝ)) =ᵐ[
      volume.restrict (Metric.ball (0 : Euc n) 1)]
      {z | inner ℝ z w < 0}.indicator (fun _ ↦ (1 : ℝ))) : v = w := by
  by_contra hne
  let U : Set (Euc n) := Metric.ball 0 1 ∩ {z | inner ℝ z v < 0} ∩ {z | 0 < inner ℝ z w}
  have hUo : IsOpen U := (Metric.isOpen_ball.inter
    (isOpen_lt (continuous_id.inner continuous_const) continuous_const)).inter
      (isOpen_lt continuous_const (continuous_id.inner continuous_const))
  have hUp : 0 < (volume : Measure (Euc n)) U :=
    hUo.measure_pos _ (halfspace_wedge_nonempty hv hw hne)
  have hUs : U ⊆ Metric.ball 0 1 := fun _ hz ↦ hz.1.1
  have hUr : 0 < volume.restrict (Metric.ball (0 : Euc n) 1) U := by
    rwa [Measure.restrict_apply hUo.measurableSet, inter_eq_left.mpr hUs]
  obtain ⟨z, hz, hze⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hUr.ne' (ae_restrict_of_ae he)
  have hzv : z ∈ {y | inner ℝ y v < 0} := hz.1.2
  have hzwp : 0 < inner ℝ z w := hz.2
  have hzw : z ∉ {y | inner ℝ y w < 0} := not_lt.mpr hzwp.le
  simp only [Set.indicator_of_mem hzv, Set.indicator_of_notMem hzw, one_ne_zero] at hze

theorem integrable_rescaled_indicator {n : ℕ} {E : Set (Euc n)} (hE : MeasurableSet E)
    (x : Euc n) (r : ℝ) :
    Integrable (fun z ↦ E.indicator (fun _ ↦ (1 : ℝ)) (x + r • z))
      (volume.restrict (Metric.ball (0 : Euc n) 1)) := by
  have hAff : Measurable (fun z : Euc n ↦ x + r • z) :=
    measurable_const.add (measurable_id.const_smul r)
  have he : Measurable (E.indicator (fun _ : Euc n ↦ (1 : ℝ))) :=
    measurable_const.indicator hE
  apply (integrableOn_const measure_ball_lt_top.ne (C := (1 : ℝ))).mono'
    (he.comp hAff).aestronglyMeasurable
  filter_upwards [] with z
  by_cases hz : x + r • z ∈ E <;> simp [hz]

theorem HasHalfspaceBlowup.tendstoInMeasure {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) {x v : Euc n} (hv : HasHalfspaceBlowup E x v) :
    TendstoInMeasure (volume.restrict (Metric.ball (0 : Euc n) 1))
      (fun r z ↦ E.indicator (fun _ ↦ (1 : ℝ)) (x + r • z)) (𝓝[>] (0 : ℝ))
      ({z | inner ℝ z v < 0}.indicator (fun _ ↦ (1 : ℝ))) := by
  let μ := (volume : Measure (Euc n)).restrict (Metric.ball 0 1)
  let χ : ℝ → Euc n → ℝ := fun r z ↦ E.indicator (fun _ ↦ (1 : ℝ)) (x + r • z)
  let H : Set (Euc n) := {z | inner ℝ z v < 0}
  let ψ : Euc n → ℝ := H.indicator (fun _ ↦ (1 : ℝ))
  have hH : MeasurableSet H :=
    (isOpen_lt (continuous_id.inner continuous_const) continuous_const).measurableSet
  have hχ : ∀ r, Integrable (χ r) μ := integrable_rescaled_indicator hE x
  have hψ : Integrable ψ μ :=
    (integrableOn_const measure_ball_lt_top.ne (C := (1 : ℝ))).indicator hH
  have hconv : Tendsto (fun r ↦ ∫ z, |χ r z - ψ z| ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply hv.2.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [normalized_ball_integral _ x hr]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [χ, ψ, H, halfspace_indicator_rescale x v z hr]
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
  have heq : (fun r ↦ eLpNorm (χ r - ψ) 1 μ) =
      (fun r ↦ ENNReal.ofReal (∫ z, |χ r z - ψ z| ∂μ)) := by
    funext r
    rw [eLpNorm_one_eq_lintegral_enorm ((hχ r).sub hψ).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hχ r).sub hψ)]
    rfl
  change Tendsto (fun r ↦ eLpNorm (χ r - ψ) 1 μ) _ _
  rw [heq]
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hconv

theorem HasHalfspaceBlowup.unique {n : ℕ} {E : Set (Euc n)} (hE : MeasurableSet E)
    {x v w : Euc n} (hv : HasHalfspaceBlowup E x v) (hw : HasHalfspaceBlowup E x w) :
    v = w := by
  apply eq_of_halfspace_indicator_ae hv.1 hw.1
  exact tendstoInMeasure_ae_unique (hv.tendstoInMeasure hE) (hw.tendstoInMeasure hE)

theorem approximateNormal_eq_of_blowup {n : ℕ} {E : Set (Euc n)} (hE : MeasurableSet E)
    {x v : Euc n} (hv : HasHalfspaceBlowup E x v) : approximateNormal E x = v := by
  have hex : ∃ w, HasHalfspaceBlowup E x w := ⟨v, hv⟩
  rw [approximateNormal, dite_eq_left hex]
  exact (Classical.choose_spec hex).unique hE hv

theorem approximateNormal_eq_gradient {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) {f : Euc n → ℝ} {x : Euc n}
    (hd : DifferentiableAt ℝ f x) (hx : f x = 0) (hdf : fderiv ℝ f x ≠ 0)
    (hlocal : ∀ᶠ y in 𝓝 x, y ∈ E ↔ f y < 0) :
    approximateNormal E x = ‖gradient f x‖⁻¹ • gradient f x :=
  approximateNormal_eq_of_blowup hE (hasHalfspaceBlowup_gradient hE hd hx hdf hlocal)

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
namespace RPI.Boundary

theorem surfaceGradient_eq_tangentialGradient {n : ℕ} {E S : Set (Space n)}
    (hE : MeasurableSet E) {f g : Space n → ℝ} {x : Space n}
    (hf : ContDiffAt ℝ 1 f x) (hfx : f x = 0) (hdf : fderiv ℝ f x ≠ 0)
    (hlevel : ∀ᶠ y in 𝓝 x, y ∈ S ↔ f y = 0)
    (hfilled : ∀ᶠ y in 𝓝 x, y ∈ E ↔ f y < 0) :
    surfaceGradient S g x = RPISingularHarnack.tangentialGradient E g x := by
  have hgrad : gradient f x ≠ 0 := by
    intro he
    apply hdf
    rw [← toDual_gradient, he, map_zero]
  have hn : ‖gradient f x‖ ≠ 0 := norm_ne_zero_iff.mpr hgrad
  rw [surfaceGradient_eq_level_formula hf hdf (by simpa only [hfx] using hlevel),
    RPISingularHarnack.tangentialGradient,
    RPISingularHarnack.approximateNormal_eq_gradient hE
      (hf.differentiableAt (by norm_num)) hfx hdf hfilled,
    real_inner_smul_right, smul_smul, real_inner_comm (gradient f x) (gradient g x)]
  congr 2
  field_simp

end RPI.Boundary

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
namespace RPISingularHarnack

def divergence {n : ℕ} (V : Euc n → Euc n) (x : Euc n) : ℝ :=
  ∑ i : Fin n, inner ℝ ((EuclideanSpace.basisFun (Fin n) ℝ) i)
    (fderiv ℝ V x ((EuclideanSpace.basisFun (Fin n) ℝ) i))

def perimeter {n : ℕ} (E U : Set (Euc n)) : ℝ≥0∞ :=
  ⨆ (V : Euc n → Euc n) (_ : ContDiff ℝ ∞ V) (_ : HasCompactSupport V)
    (_ : tsupport V ⊆ U) (_ : ∀ x, ‖V x‖ ≤ 1),
    ENNReal.ofReal (∫ x in E, divergence V x)

def perimeterSupport {n : ℕ} (E : Set (Euc n)) : Set (Euc n) :=
  {x | ∀ r : ℝ, 0 < r → 0 < perimeter E (Metric.ball x r)}

def IsLocallyPerimeterMinimizing {n : ℕ} (E : Set (Euc n)) : Prop :=
  MeasurableSet E ∧
  (∀ x (r : ℝ), 0 < r → perimeter E (Metric.ball x r) < ⊤) ∧
  ∀ x (r : ℝ), 0 < r → ∀ F : Set (Euc n), MeasurableSet F →
    IsCompact (closure (symmDiff E F)) →
    closure (symmDiff E F) ⊆ Metric.ball x r →
    perimeter E (Metric.ball x r) ≤ perimeter F (Metric.ball x r)

def IsCone {n : ℕ} (E : Set (Euc n)) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ x : Euc n, r • x ∈ E ↔ x ∈ E

end RPISingularHarnack

end

end OAI
