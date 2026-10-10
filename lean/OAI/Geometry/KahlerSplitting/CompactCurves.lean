import OAI.Geometry.KahlerSplitting.SmallArea

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open Set
open Set Topology Filter Metric
open Set MeasureTheory Metric Filter Topology
open scoped Interval
open Set MeasureTheory
open scoped ENNReal
open Set Metric
open Set Metric Filter Topology
open scoped Manifold
open Set Filter Topology
open Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal

namespace UniversalCoverSplitting

variable {T : Type*} [MetricSpace T] [MeasurableSpace T] [BorelSpace T]

theorem finite_large_atoms (μ : Measure T) [IsFiniteMeasure μ]
    {ε : ℝ≥0∞} (hε : 0 < ε) : Set.Finite {p : T | ε ≤ μ {p}} := by
  apply Measure.finite_const_le_meas_of_disjoint_iUnion μ hε
    (fun p ↦ measurableSet_singleton p)
  · intro p q hpq
    exact disjoint_singleton.mpr hpq
  · exact measure_ne_top μ _

theorem eventually_small_ball_of_small_atom {μ : ProbabilityMeasure T}
    {μs : ℕ → ProbabilityMeasure T} (hμ : Tendsto μs atTop (𝓝 μ))
    {p : T} {ε : ℝ≥0∞} (hp : (μ : Measure T) {p} < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ j in atTop,
      (μs j : Measure T) (closedBall p r) < ε := by
  obtain ⟨U,hU,hUo,hUm⟩ := ({p} : Set T).exists_isOpen_lt_of_lt ε hp
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hUo.mem_nhds (hU (mem_singleton p)))
  refine ⟨r/2,by positivity,?_⟩
  apply eventually_lt_of_limsup_lt (hu := ⟨⊤, Filter.Eventually.of_forall (fun _ ↦ le_top)⟩)
  apply (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ isClosed_closedBall).trans_lt
  exact (measure_mono ((closedBall_subset_ball (by linarith)).trans hrU)).trans_lt hUm

theorem bounded_measure_finite_concentration [CompactSpace T] [Nonempty T]
    (μs : ℕ → FiniteMeasure T) (C : ℝ≥0) (hC : ∀ j, (μs j).mass ≤ C)
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ A : Set T, A.Finite ∧
      ∀ p ∉ A, ∃ r : ℝ, 0 < r ∧ ∀ᶠ j in atTop,
        (μs (σ j) : Measure T) (closedBall p r) < (ε : ℝ≥0∞) := by
  obtain ⟨ν,σ,hσ,hν⟩ := CompactSpace.tendsto_subseq (fun j ↦ (μs j).normalize)
  let δ : ℝ≥0 := ε / (C + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  let A : Set T := {p | (δ : ℝ≥0∞) ≤ (ν : Measure T) {p}}
  have hA : A.Finite := finite_large_atoms (ν : Measure T) (by exact_mod_cast hδ)
  refine ⟨σ,hσ,A,hA,?_⟩
  intro p hp
  have hp' : (ν : Measure T) {p} < (δ : ℝ≥0∞) := lt_of_not_ge hp
  obtain ⟨r,hr,he⟩ := eventually_small_ball_of_small_atom hν hp'
  refine ⟨r,hr,?_⟩
  filter_upwards [he] with j hj
  have hj' : (μs (σ j)).normalize (closedBall p r) < δ := by
    change ((μs (σ j)).normalize : Measure T) (closedBall p r) < (δ : ℝ≥0∞) at hj
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hj
    exact ENNReal.coe_lt_coe.mp hj
  have hb : μs (σ j) (closedBall p r) < ε := by
    rw [(μs (σ j)).self_eq_mass_mul_normalize]
    calc
      (μs (σ j)).mass * (μs (σ j)).normalize (closedBall p r)
          ≤ (C + 1) * (μs (σ j)).normalize (closedBall p r) := by
            gcongr
            exact (hC _).trans (le_add_of_nonneg_right zero_le_one)
      _ < (C + 1) * δ := mul_lt_mul_of_pos_left hj' (by positivity)
      _ = ε := by dsimp [δ]; field_simp
  rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
  exact ENNReal.coe_lt_coe.mpr hb

end UniversalCoverSplitting

open Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal
namespace UniversalCoverSplitting

theorem bounded_density_finite_concentration
    {K : Set ℂ} (hK : IsCompact K) (hKn : K.Nonempty)
    (w : ℕ → ℂ → ℝ≥0∞) (C : ℝ≥0)
    (hC : ∀ j, (∫⁻ z in K, w j z) ≤ (C : ℝ≥0∞))
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ A : Set ℂ, A.Finite ∧ A ⊆ K ∧
      ∀ p ∈ interior K \ A, ∃ r : ℝ, 0 < r ∧ closedBall p r ⊆ K ∧
        ∀ᶠ j in atTop, (∫⁻ z in ball p r, w (σ j) z) < (ε : ℝ≥0∞) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have : Nonempty K := hKn.to_subtype
  let ν (j : ℕ) : Measure ℂ := (volume.withDensity (w j)).restrict K
  have hνall (j : ℕ) : ν j univ = ∫⁻ z in K, w j z := by
    simp only [ν,Measure.restrict_apply_univ,withDensity_apply _ hK.measurableSet]
  have hfinite (j : ℕ) : IsFiniteMeasure (ν j) :=
    ⟨by rw [hνall]; exact (hC j).trans_lt (ENNReal.coe_lt_top)⟩
  let μ (j : ℕ) : FiniteMeasure ℂ := ⟨ν j,hfinite j⟩
  let μK (j : ℕ) : FiniteMeasure K := (μ j).comap Subtype.val
  have hmass (j : ℕ) : (μK j).mass ≤ C := by
    apply ((μ j).mass_comap_le Subtype.val).trans
    change (ν j univ).toNNReal ≤ C
    rw [hνall]
    simpa using ENNReal.toNNReal_mono ENNReal.coe_ne_top (hC j)
  obtain ⟨σ,hσ,B,hB,hsmall⟩ := bounded_measure_finite_concentration μK C hmass ε hε
  refine ⟨σ,hσ,Subtype.val '' B,hB.image _,by rintro _ ⟨z,_,rfl⟩; exact z.property,?_⟩
  intro p hp
  have hpK : p ∈ K := interior_subset hp.1
  let pK : K := ⟨p,hpK⟩
  have hpB : pK ∉ B := fun h ↦ hp.2 ⟨pK,h,rfl⟩
  obtain ⟨r,hr,he⟩ := hsmall pK hpB
  obtain ⟨s,hs,hsK⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (mem_interior_iff_mem_nhds.mp hp.1)
  let ρ := min r s
  have hρ : 0 < ρ := lt_min hr hs
  have hρK : closedBall p ρ ⊆ K := (closedBall_subset_closedBall (min_le_right r s)).trans hsK
  refine ⟨ρ,hρ,hρK,?_⟩
  filter_upwards [he] with j hj
  have hcomap : (μK (σ j) : Measure K) (closedBall pK r) =
      ν (σ j) (Subtype.val '' closedBall pK r) := by
    exact Measure.comap_apply Subtype.val Subtype.val_injective
      (fun s hs ↦ (MeasurableEmbedding.subtype_coe hK.measurableSet).measurableSet_image.mpr hs) _ measurableSet_closedBall
  have hball : ball p ρ ⊆ Subtype.val '' closedBall pK r := by
    intro z hz
    have hzK := hρK (ball_subset_closedBall hz)
    refine ⟨⟨z,hzK⟩,?_,rfl⟩
    change dist z p ≤ r
    exact hz.le.trans (min_le_left r s)
  have harea : ν (σ j) (ball p ρ) = ∫⁻ z in ball p ρ, w (σ j) z := by
    change ((volume.withDensity (w (σ j))).restrict K) (ball p ρ) = _
    rw [Measure.restrict_apply measurableSet_ball,
      inter_eq_left.mpr (ball_subset_closedBall.trans hρK),
      withDensity_apply _ measurableSet_ball]
  rw [hcomap] at hj
  exact (harea.symm.trans_le (measure_mono hball)).trans_lt hj

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}
local instance [CompactSpace X.Carrier] : MetricSpace X.Carrier := compactManifoldMetric X

theorem manifold_holomorphic_locally_uniform_limit [CompactSpace X.Carrier]
    {f : ℕ → ℂ → X.Carrier} {F : ℂ → X.Carrier} {Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hf : ∀ j, MDifferentiableOn 𝓘(ℂ, ℂ) (model n) (f j) Ω)
    (hconv : TendstoLocallyUniformlyOn f F atTop Ω) :
    MDifferentiableOn 𝓘(ℂ, ℂ) (model n) F Ω := by
  have hc : ContinuousOn F Ω := hconv.continuousOn
    (Filter.Eventually.of_forall (fun j ↦ (hf j).continuousOn)).frequently
  intro p hp
  let c := F p
  let e := extChartAt (model n) c
  have hes : IsOpen e.source := isOpen_extChartAt_source c
  have hcs : c ∈ e.source := mem_extChartAt_source c
  obtain ⟨δ,hδ,hδsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hes.mem_nhds hcs)
  have hnear : Ω ∩ F ⁻¹' ball c (δ/3) ∈ 𝓝 p := inter_mem (hΩ.mem_nhds hp)
    ((hc.continuousAt (hΩ.mem_nhds hp)) (ball_mem_nhds c (by positivity)))
  obtain ⟨r,hr,hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  have hKΩ : closedBall p r ⊆ Ω := fun z hz ↦ (hrsub hz).1
  have hFsmall (z : ℂ) (hz : z ∈ closedBall p r) : dist (F z) c < δ/3 := (hrsub hz).2
  have hu : TendstoUniformlyOn f F atTop (closedBall p r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).mp hconv _ hKΩ (isCompact_closedBall p r)
  have hlate : ∀ᶠ j in atTop, MapsTo (f j) (ball p r) (closedBall c δ) := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu (δ/3) (by positivity)] with j hj
    intro z hz
    have hzK := ball_subset_closedBall hz
    have hdist : dist (f j z) (F z) < δ/3 := by simpa only [dist_comm] using hj z hzK
    have ht := dist_triangle (f j z) (F z) c
    have hh := hFsmall z hzK
    change dist (f j z) c ≤ δ
    linarith
  have hFmap : MapsTo F (ball p r) (closedBall c δ) := by
    intro z hz
    change dist (F z) c ≤ δ
    exact (hFsmall z (ball_subset_closedBall hz)).le.trans (by linarith)
  have heuc : UniformContinuousOn e (closedBall c δ) :=
    (isCompact_closedBall c δ).uniformContinuousOn_of_continuous ((continuousOn_extChartAt c).mono hδsub)
  have hl : TendstoLocallyUniformlyOn (fun j ↦ e ∘ f j) (e ∘ F) atTop (ball p r) :=
    heuc.comp_tendstoLocallyUniformlyOn (hconv.mono (ball_subset_closedBall.trans hKΩ)) hFmap hlate
  have hhol : ∀ᶠ j in atTop, DifferentiableOn ℂ (e ∘ f j) (ball p r) := by
    filter_upwards [hlate] with j hj
    intro z hz
    have hfj := (hf j).mdifferentiableAt (hΩ.mem_nhds (hKΩ (ball_subset_closedBall hz)))
    have hej : MDifferentiableAt (model n) (model n) e (f j z) :=
      mdifferentiableAt_extChartAt (by simpa only [e,extChartAt_source] using hδsub (hj hz))
    exact (hej.comp z hfj).differentiableAt.differentiableWithinAt
  have hchart := (hl.differentiableOn hhol isOpen_ball).differentiableAt
    (ball_mem_nhds p hr)
  have hfpc : F p ∈ e.source := by exact hcs
  have het : e (F p) ∈ e.target := e.map_source hfpc
  have hei : MDifferentiableAt (model n) (model n) e.symm (e (F p)) :=
    mdifferentiableOn_extChartAt_symm.mdifferentiableAt ((isOpen_extChartAt_target c).mem_nhds het)
  have hd := hei.comp p hchart.mdifferentiableAt
  apply (hd.congr_of_eventuallyEq ?_).mdifferentiableWithinAt
  filter_upwards [ball_mem_nhds p hr] with z hz
  exact (e.left_inv (hδsub (hFmap hz))).symm

end UniversalCoverSplitting

open Set Metric Filter Topology
open scoped Manifold
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}
local instance [CompactSpace X.Carrier] : MetricSpace X.Carrier := compactManifoldMetric X

theorem bounded_curveSpeed_holomorphic_subsequence [CompactSpace X.Carrier]
    (g : KahlerMetric X) (f : ℕ → ℂ → X.Carrier) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hf : ∀ j, MDifferentiableOn 𝓘(ℂ, ℂ) (model n) (f j) Ω)
    (hb : ∀ p ∈ Ω, ∃ R L : ℝ, 0 < R ∧ 0 ≤ L ∧ closedBall p R ⊆ Ω ∧
      ∀ j z, z ∈ closedBall p R → curveSpeed g (f j) z ≤ L) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ F : ℂ → X.Carrier,
      MDifferentiableOn 𝓘(ℂ, ℂ) (model n) F Ω ∧
      TendstoLocallyUniformlyOn (f ∘ σ) F atTop Ω := by
  classical
  have : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  let ff (j : ℕ) : C(Ω,X.Carrier) :=
    ⟨fun z ↦ f j z, continuousOn_iff_continuous_domRestrict.mp (hf j).continuousOn⟩
  have he := bounded_curveSpeed_equicontinuousOn g f hΩ hf hb
  have he' : Equicontinuous (fun j z ↦ ff j z) := by
    intro z
    exact (equicontinuousAt_restrict_iff f z).mpr (he z z.property)
  obtain ⟨σ,hσ,G,hG⟩ := equicontinuous_compact_target_subsequence ff he'
  let F : ℂ → X.Carrier := fun z ↦ if hz : z ∈ Ω then G ⟨z,hz⟩ else f 0 z
  have hconv : TendstoLocallyUniformlyOn (f ∘ σ) F atTop Ω := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    have ht := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hG
    convert ht using 1 <;> first | rfl | simp [F,Function.comp_def]
  exact ⟨σ,hσ,F,manifold_holomorphic_locally_uniform_limit hΩ (fun j ↦ hf (σ j)) hconv,hconv⟩

theorem eventual_curveSpeed_bound_to_bound (g : KahlerMetric X)
    (f : ℕ → ℂ → X.Carrier) {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (hf : ∀ j, MDifferentiableOn 𝓘(ℂ, ℂ) (model n) (f j) Ω)
    {p : ℂ} {R L : ℝ} (hsub : closedBall p R ⊆ Ω) (hL : 0 ≤ L)
    (he : ∀ᶠ j in atTop, ∀ z ∈ closedBall p R, curveSpeed g (f j) z ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j z, z ∈ closedBall p R → curveSpeed g (f j) z ≤ C := by
  classical
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  have hex (j : ℕ) : ∃ C : ℝ, ∀ z ∈ closedBall p R, curveSpeed g (f j) z ≤ C := by
    have h := (isCompact_closedBall p R).bddAbove_image
      ((curveSpeed_continuousOn g hΩ (hf j)).mono hsub)
    obtain ⟨C,hC⟩ := h
    exact ⟨C,fun z hz ↦ hC (mem_image_of_mem _ hz)⟩
  choose C hC using hex
  let B := ∑ j ∈ Finset.range N, max (C j) 0
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ ↦ le_max_right _ _)
  refine ⟨max L B,le_max_of_le_left hL,?_⟩
  intro j z hz
  by_cases hj : N ≤ j
  · exact (hN j hj z hz).trans (le_max_left _ _)
  · have hjN : j ∈ Finset.range N := Finset.mem_range.mpr (lt_of_not_ge hj)
    have hjB : C j ≤ B := (le_max_left _ _).trans
      (Finset.single_le_sum (fun _ _ ↦ le_max_right _ _) hjN)
    exact (hC j z hz).trans (hjB.trans (le_max_right _ _))

end UniversalCoverSplitting

open Set Metric Filter Topology MeasureTheory
open scoped Manifold ENNReal NNReal
namespace UniversalCoverSplitting
variable {n : ℕ} {X : ComplexManifold n}
local instance [CompactSpace X.Carrier] : MetricSpace X.Carrier := compactManifoldMetric X

theorem bounded_curveArea_holomorphic_subsequence [CompactSpace X.Carrier]
    (g : KahlerMetric X) (f : ℕ → ℂ → X.Carrier) {Ω K : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKn : K.Nonempty) (hKΩ : K ⊆ Ω)
    (hf : ∀ j, MDifferentiableOn 𝓘(ℂ,ℂ) (model n) (f j) Ω)
    (C : ℝ≥0) (hC : ∀ j, curveArea g (f j) K ≤ (C : ℝ≥0∞)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ A : Set ℂ, A.Finite ∧ A ⊆ K ∧
      ∃ F : ℂ → X.Carrier,
        MDifferentiableOn 𝓘(ℂ,ℂ) (model n) F (interior K \ A) ∧
        TendstoLocallyUniformlyOn (f ∘ σ) F atTop (interior K \ A) := by
  obtain ⟨η,hη,hsmall⟩ := small_area_weighted_speed g (by norm_num : (0:ℝ) < 1)
  let ε : ℝ≥0 := ⟨η,hη.le⟩
  have hε : 0 < ε := hη
  obtain ⟨τ,hτ,A,hA,hAK,hconc⟩ := bounded_density_finite_concentration hK hKn
    (fun j z ↦ ENNReal.ofReal (curveSpeed g (f j) z ^ 2)) C hC ε hε
  let U := interior K \ A
  have hU : IsOpen U := isOpen_interior.inter hA.isClosed.isOpen_compl
  have hUΩ : U ⊆ Ω := fun _ hz ↦ hKΩ (interior_subset hz.1)
  have hbound : ∀ p ∈ U, ∃ R L : ℝ, 0 < R ∧ 0 ≤ L ∧ closedBall p R ⊆ U ∧
      ∀ j z, z ∈ closedBall p R → curveSpeed g (f (τ j)) z ≤ L := by
    intro p hp
    obtain ⟨r,hr,hrK,he⟩ := hconc p hp
    obtain ⟨s,hs,hsU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hp)
    let R := min (r/2) s
    have hR : 0 < R := lt_min (by positivity) hs
    have hRU : closedBall p R ⊆ U := (closedBall_subset_closedBall (min_le_right _ _)).trans hsU
    have hlate : ∀ᶠ j in atTop, ∀ z ∈ closedBall p R,
        curveSpeed g (f (τ j)) z ≤ 2/r := by
      filter_upwards [he] with j hj
      have ha : curveArea g (f (τ j)) (ball p r) < ENNReal.ofReal η := by
        have heps : (ε : ℝ≥0∞) = ENNReal.ofReal η :=
          (ENNReal.ofReal_eq_coe_nnreal hη.le).symm
        rw [← heps]
        exact hj
      intro z hz
      have hzr : dist z p ≤ r/2 := hz.trans (min_le_left _ _)
      have hzb : z ∈ ball p r := hzr.trans_lt (by linarith)
      have hw := hsmall (f (τ j)) Ω hΩ (hf (τ j)) p r hr (hrK.trans hKΩ) ha z hzb
      have hn := curveSpeed_nonneg g (f (τ j)) z
      apply (le_div_iff₀ hr).mpr
      nlinarith
    obtain ⟨L,hL,hb⟩ := eventual_curveSpeed_bound_to_bound g (f ∘ τ) hU
      (fun j ↦ (hf (τ j)).mono hUΩ) hRU (by positivity : 0 ≤ 2/r) hlate
    exact ⟨R,L,hR,hL,hRU,hb⟩
  obtain ⟨υ,hυ,F,hF,hconv⟩ := bounded_curveSpeed_holomorphic_subsequence g (f ∘ τ) hU
    (fun j ↦ (hf (τ j)).mono hUΩ) hbound
  exact ⟨τ ∘ υ,hτ.comp hυ,A,hA,hAK,F,hF,hconv⟩

end UniversalCoverSplitting

open Set Metric Filter Topology MeasureTheory
open Complex
namespace UniversalCoverSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in

theorem holomorphic_circleAverage_eq {f : ℂ → E} {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R)
    (hc : ContinuousOn f (closedBall 0 R \ ball 0 r))
    (hd : ∀ z ∈ ball 0 R \ closedBall 0 r, DifferentiableAt ℂ f z) :
    Real.circleAverage f 0 R = Real.circleAverage f 0 r := by
  rw [Real.circleAverage_eq_circleIntegral (ne_of_gt (hr.trans_le hrR)),
    Real.circleAverage_eq_circleIntegral hr.ne']
  congr 1
  exact Complex.circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable
    hr hrR (s := ∅) countable_empty hc (fun z hz ↦ hd z hz.1)

omit [CompleteSpace E] in

theorem norm_circleAverage_le {f : ℂ → E} {r B : ℝ}
    (h : ∀ z ∈ sphere (0:ℂ) |r|, ‖f z‖ ≤ B) :
    ‖Real.circleAverage f 0 r‖ ≤ B := by
  rw [Real.circleAverage_def,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr Real.two_pi_pos)]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := 2 * Real.pi) (fun θ _ ↦ h _ (circleMap_mem_sphere' 0 r θ))
  have ht : |2 * Real.pi - 0| = 2 * Real.pi := by rw [sub_zero, abs_of_pos Real.two_pi_pos]
  rw [ht] at hb
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (B * (2 * Real.pi)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = B := by field_simp

theorem norm_sub_circleAverage_le {f : ℂ → E} {r B : ℝ} {v : E}
    (hf : ContinuousOn f (sphere (0:ℂ) |r|))
    (h : ∀ z ∈ sphere (0:ℂ) |r|, ‖f z - v‖ ≤ B) :
    ‖v - Real.circleAverage f 0 r‖ ≤ B := by
  have hb := norm_circleAverage_le h
  rw [Real.circleAverage_fun_sub hf.circleIntegrable' continuousOn_const.circleIntegrable',
    Real.circleAverage_const] at hb
  simpa only [norm_sub_rev] using hb

omit [CompleteSpace E] in

theorem holomorphic_circle_oscillation {f : ℂ → E} {r L : ℝ}
    (hr : 0 < r) (hL : 0 ≤ L)
    (hd : ∀ z ∈ sphere (0:ℂ) r, DifferentiableAt ℂ f z)
    (hb : ∀ z ∈ sphere (0:ℂ) r, ‖deriv f z‖ * r ≤ L) :
    ∀ z ∈ sphere (0:ℂ) r, ‖f z - f (r:ℂ)‖ ≤ 8 * L := by
  have hnorm (θ : ℝ) : ‖circleMap 0 r θ‖ = r := by
    simpa using circleMap_mem_sphere (0:ℂ) hr.le θ
  have hder (θ : ℝ) : HasDerivAt (fun t ↦ f (circleMap 0 r t))
      ((circleMap 0 r θ * Complex.I) • deriv f (circleMap 0 r θ)) θ := by
    exact (hd _ (circleMap_mem_sphere 0 hr.le θ)).hasDerivAt.scomp θ
      (hasDerivAt_circleMap 0 r θ)
  have hbound (θ : ℝ) : ‖(circleMap 0 r θ * Complex.I) • deriv f (circleMap 0 r θ)‖ ≤ L := by
    rw [norm_smul,norm_mul,Complex.norm_I,mul_one,hnorm,mul_comm]
    exact hb _ (circleMap_mem_sphere 0 hr.le θ)
  intro z hz
  have hz' : z ∈ circleMap 0 r '' Ioc 0 (2 * Real.pi) := by
    rw [image_circleMap_Ioc,abs_of_pos hr]
    exact hz
  obtain ⟨θ,hθ,rfl⟩ := hz'
  have hp := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t (_ : t ∈ Icc 0 (2 * Real.pi)) ↦ (hder t).hasDerivWithinAt)
    (fun t _ ↦ hbound t) θ ⟨hθ.1.le,hθ.2⟩
  have ht : L * (θ - 0) ≤ 8 * L := by
    have hh : θ ≤ 8 := hθ.2.trans (by linarith [Real.pi_lt_four])
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hh hL
  simpa [circleMap] using hp.trans ht

theorem holomorphic_annulus_oscillation {f : ℂ → E} {r R L : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hL : 0 ≤ L)
    (hc : ContinuousOn f (closedBall 0 R \ ball 0 r))
    (hd : ∀ z ∈ closedBall 0 R \ ball 0 r, DifferentiableAt ℂ f z)
    (hb : ∀ z ∈ closedBall 0 R \ ball 0 r, ‖deriv f z‖ * ‖z‖ ≤ L) :
    ∀ z ∈ sphere (0:ℂ) r, ‖f z - f (R:ℂ)‖ ≤ 24 * L := by
  have hs (s : ℝ) (hs : s ∈ Icc r R) : sphere (0:ℂ) s ⊆ closedBall 0 R \ ball 0 r := by
    intro z hz
    have hn : ‖z‖ = s := by simpa using hz
    simp only [Set.mem_sdiff,mem_closedBall,mem_ball,dist_zero_right,not_lt]
    exact ⟨hn ▸ hs.2, hn ▸ hs.1⟩
  have ho (s : ℝ) (hs' : s ∈ Icc r R) :
      ∀ z ∈ sphere (0:ℂ) s, ‖f z - f (s:ℂ)‖ ≤ 8 * L := by
    apply holomorphic_circle_oscillation (hr.trans_le hs'.1) hL
    · exact fun z hz ↦ hd z (hs s hs' hz)
    · intro z hz
      have hn : ‖z‖ = s := by simpa using hz
      simpa only [hn] using hb z (hs s hs' hz)
  have hm (s : ℝ) (hs' : s ∈ Icc r R) :
      ‖f (s:ℂ) - Real.circleAverage f 0 s‖ ≤ 8 * L := by
    apply norm_sub_circleAverage_le
    · rw [abs_of_pos (hr.trans_le hs'.1)]
      exact hc.mono (hs s hs')
    · rw [abs_of_pos (hr.trans_le hs'.1)]
      exact ho s hs'
  have havg := holomorphic_circleAverage_eq hr hrR hc
    (fun z hz ↦ hd z ⟨ball_subset_closedBall hz.1, fun hh ↦ hz.2 (ball_subset_closedBall hh)⟩)
  intro z hz
  have h₁ := ho r ⟨le_rfl,hrR⟩ z hz
  have h₂ := hm r ⟨le_rfl,hrR⟩
  have h₃ := hm R ⟨hrR,le_rfl⟩
  rw [havg] at h₃
  have ht₁ := dist_triangle (f z) (f (r:ℂ)) (Real.circleAverage f 0 r)
  have ht₂ := dist_triangle (f z) (Real.circleAverage f 0 r) (f (R:ℂ))
  simp only [dist_eq_norm] at ht₁ ht₂
  rw [norm_sub_rev (Real.circleAverage f 0 r) (f (R:ℂ))] at ht₂
  linarith

end UniversalCoverSplitting

end

end OAI
