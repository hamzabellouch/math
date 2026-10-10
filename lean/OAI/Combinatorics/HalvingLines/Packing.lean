import OAI.Combinatorics.HalvingLines.ActivityRetention

namespace OAI

open Filter Topology

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows Zoom
open scoped Topology unitInterval

noncomputable def commonDirection : Fin 3 → Point := ![(1,0),(1,1),(0,1)]

lemma commonDirection_independent (i j : Fin 3) (h : i≠j) :
    detPair (commonDirection i) (commonDirection j)≠0 := by
  fin_cases i <;> fin_cases j <;> norm_num [commonDirection,detPair] at *

lemma common_frame (F : ℕ → Configuration) {K : Window} (q : CommonChoice K)
    (h12 : ∀ n, (F n).timeSlope (q.time 0)<(F n).timeSlope (q.time 1))
    (h23 : ∀ n, (F n).timeSlope (q.time 1)<(F n).timeSlope (q.time 2)) :
    ∃ E : ℕ → Point ≃L[ℝ] Point,
      (∀ n i, detPair ((E n).symm (1,(F n).timeSlope (q.time i))) (commonDirection i)=0) ∧
      ∀ n, ∃ a b l u : ℝ, 0<a ∧ 0<b ∧ l<u ∧
        E n (1,0)=a • (1,l) ∧ E n (0,1)=b • (1,u) ∧
        ∀ i, ((F n).system.timeWindow q.val.2.2).slope i∈Icc l u := by
  choose E a b ha hb h1 h2 h3 using fun n => slope_frame (h12 n) (h23 n)
  refine ⟨E,?_,?_⟩
  · intro n i
    have h1' : (E n).symm (1,(F n).timeSlope (q.time 0))=(a n)⁻¹ • (1,0) := by
      apply (E n).injective
      rw [(E n).apply_symm_apply,map_smul,h1,smul_smul,inv_mul_cancel₀ (ha n).ne',one_smul]
    have h2' : (E n).symm (1,(F n).timeSlope (q.time 2))=(b n)⁻¹ • (0,1) := by
      apply (E n).injective
      rw [(E n).apply_symm_apply,map_smul,h2,smul_smul,inv_mul_cancel₀ (hb n).ne',one_smul]
    have h3' : (E n).symm (1,(F n).timeSlope (q.time 1))=(1,1) := by
      rw [←h3,(E n).symm_apply_apply]
    fin_cases i
    · change detPair ((E n).symm (1,(F n).timeSlope (q.time 0))) (1,0)=0
      rw [h1']; simp [detPair]
    · change detPair ((E n).symm (1,(F n).timeSlope (q.time 1))) (1,1)=0
      rw [h3']; simp [detPair]
    · change detPair ((E n).symm (1,(F n).timeSlope (q.time 2))) (0,1)=0
      rw [h2']; simp [detPair]
  · intro n
    refine ⟨a n,b n,_,_,ha n,hb n,(h12 n).trans (h23 n),h1 n,h2 n,?_⟩
    intro i
    constructor
    · exact ((F n).timeSlope_before (J:=q.val.2.2) q.property.2.2.2.1.le).trans
        (((F n).system.timeWindow q.val.2.2).increasing.monotone (Fin.zero_le i))
    · apply (((F n).system.timeWindow q.val.2.2).increasing.monotone (Fin.le_last i)).trans
      exact (F n).timeSlope_after (J:=q.val.2.2)
        (q.property.2.2.2.2.trans (q.property.2.1.trans (lower_lt_upper q.val.2.1))).le

noncomputable def commonChart (F : Configuration) {A B : Window} (hAB : Before A B)
    (hA : 0<length F.R A) (hB : 0<length F.R B) (E : Point ≃L[ℝ] Point) :
    OpenPartialHomeomorph Point Point :=
  E.toHomeomorph.transOpenPartialHomeomorph (F.rankChart hAB hA hB)

@[simp] lemma commonChart_symm (F : Configuration) {A B : Window} (hAB : Before A B)
    (hA : 0<length F.R A) (hB : 0<length F.R B) (E : Point ≃L[ℝ] Point) (p : Point) :
    (commonChart F hAB hA hB E).symm p=E.symm ((F.rankChart hAB hA hB).symm p) := rfl

lemma commonChart_source (F : Configuration) {A B : Window} (hAB : Before A B)
    (hA : 0<length F.R A) (hB : 0<length F.R B) (E : Point ≃L[ℝ] Point) :
    (commonChart F hAB hA hB E).source=univ := by
  simp [commonChart,F.rankChart_source]

lemma commonChart_target (F : Configuration) {A B : Window} (hAB : Before A B)
    (hA : 0<length F.R A) (hB : 0<length F.R B) (E : Point ≃L[ℝ] Point) :
    (commonChart F hAB hA hB E).target=Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0 := by
  simp [commonChart,F.rankChart_target]

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows Zoom
open scoped Topology unitInterval

lemma Converges.radial_ae {F : ℕ → Configuration} {L : Data} (h : Converges F L)
    (emb : ∀ n, (F n).SweepEmbedding) (hR : Tendsto (fun n => (F n).R) atTop atTop)
    (hM : Tendsto (fun n => (F n).a*(F n).n) atTop atTop)
    {C : ℝ} (hC : 0≤C)
    (hcoeff : ∀ n, 4608*((F n).a:ℝ)^2*(F n).n^4 / (((F n).R:ℝ)*(F n).a^2)^3≤C)
    (herror : Tendsto (fun n => 13824*((F n).n:ℝ)^3 / (((F n).R:ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (hshort : Tendsto (fun n => ((F n).n:ℝ)/((F n).R*(F n).a)) atTop (𝓝 0))
    {K A B : Window} (hAB : Before A B) (hKA : Before K A) (hKB : Before K B)
    (hA : ∀ n, 0<length (F n).R A) (hB : ∀ n, 0<length (F n).R B)
    (G : Subwindows K → Point → I)
    (hjoint : ∀ i p, ContinuousAt (G i) p → Tendsto
      (fun q : ℕ × Point => (F q.1).extendedRank true A B i.val q.2)
      (atTop ×ˢ 𝓝 p) (𝓝 (G i p)))
    (hGaed : ∀ i, ∀ᵐ p ∂(volume : Measure Point), DifferentiableAt ℝ (fun x => (G i x:ℝ)) p)
    (hid : ∀ i z, z∈(L.points:Measure Labels).support →
      ContinuousAt (G i) (pairCoordinates true A B z) → z i.val=G i (pairCoordinates true A B z))
    (ν : Measure Labels) (he : ν≪(L.edge:Measure Labels)) (hp : ν≪(L.points:Measure Labels))
    (hproj : ν.map (pairCoordinates true A B)≪volume)
    (q : CommonChoice K)
    (hpos : ∀ᵐ z ∂ν, L.conditional z (carrier K)≠0 ∧ z∈commonSet L q)
    (E : ℕ → Point ≃L[ℝ] Point)
    (hE : ∀ n i, detPair ((E n).symm (1,(F n).timeSlope (q.time i))) (commonDirection i)=0) :
    ∀ᵐ z ∂ν, pairCoordinates true A B z∈Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0 ∧
      ∃ C₀ : ℝ, 0<C₀ ∧ ∀ T : ℝ, 1≤T → ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop,
        RadialCompare (commonChart (F n) hAB (hA n) (hB n) (E n)).symm
          (pairCoordinates true A B z) r C₀ T := by
  have hreg := h.rank_regular_ae ν hp hproj G hGaed hid
  have hind := he.ae_le (h.rank_independent_ae (A:=A) (B:=B) emb hR hM hC hcoeff herror hshort G)
  have hna := he.ae_le (h.conditional_nullSingleton emb hR hC hcoeff herror)
  filter_upwards [hreg,hind,hna,hpos,pairCoordinates_interior_ae hproj] with z hz hi hn hpos hzp
  let := hn
  refine ⟨hzp,?_⟩
  have h := pointwise_radial F hR hAB hKA hKB hA hB G hjoint hGaed hzp
    (fun i => (hz i).1) (L.conditional z) hpos.1 (fun J hJ => by
      obtain ⟨i,j,hi,hj,_,hij⟩ := hi hz J hJ
      exact ⟨i,j,hi,hj,hij⟩) q.time q.time_mem
    (q.positive_gaps (L.conditional z) hpos.2.1 hpos.2.2.1)
    (fun n => (E n).symm) commonDirection commonDirection_independent hE
  exact h

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows Zoom Spatial Enhancement Boundary
open scoped Topology unitInterval

lemma normalized_commonChart (F : Configuration) {A B : Window} (hAB : Before A B)
    (hA : 0<length F.R A) (hB : 0<length F.R B) (E : Point ≃L[ℝ] Point)
    (p : Point) {U : ℝ} (hU : U≠0) (x : Point) :
    (normalizeChart (commonChart F hAB hA hB E) p U hU).symm x=
      physical E ((F.rankChart hAB hA hB).symm p) U⁻¹ ((F.rankChart hAB hA hB).symm x) := by
  simp only [normalizeChart_symm,commonChart_symm,physical,map_sub]

lemma enhancement_points_ae (F : Configuration) (ψ : Point → Point) (H : Space → Prop)
    (hH : ∀ p, H (Enhancement.label F ψ p)) :
    ∀ᵐ z ∂(Enhancement.points F ψ : Measure Space), H z := by
  apply Measure.ae_smul_measure
  rw [ae_finsetSum_measure_iff]
  intro i _
  simpa only [ae_dirac_eq,Filter.eventually_pure,Function.comp_apply] using hH (F.point i)

lemma normalized_points_graph (F : Configuration) {A B : Window} (hAB : Before A B)
    (hA : 0<length F.R A) (hB : 0<length F.R B) (E : Point ≃L[ℝ] Point)
    (p₀ : Point) {U : ℝ} (hU : U≠0) :
    let o := (F.rankChart hAB hA hB).symm p₀
    let ψ := physical E o U⁻¹
    ∀ᵐ z ∂(Enhancement.points F ψ : Measure Space), z.2=encode
      ((normalizeChart (commonChart F hAB hA hB E) p₀ U hU).symm
        (pairCoordinates true A B z.1)) := by
  dsimp only
  apply enhancement_points_ae
  intro p
  change encode (physical E _ _ p)=encode ((normalizeChart (commonChart F hAB hA hB E) p₀ U hU).symm
      (pairCoordinates true A B (F.system.labels F.generic p)))
  rw [normalized_commonChart,←F.rankChart_apply hAB hA hB p]
  rw [(F.rankChart hAB hA hB).left_inv (mem_univ p)]

lemma support_graph_subseq {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {μs : ℕ → FiniteMeasure (X × Cube)} {μ : FiniteMeasure (X × Cube)}
    {τ : ℕ → ℕ} (hτ : StrictMono τ) (hμ : Tendsto (μs∘τ) atTop (𝓝 μ))
    (π : X → Point) (hπ : Continuous π) (f : ℕ → Point → Point)
    (hid : ∀ n, ∀ᵐ z ∂(μs n:Measure (X×Cube)), z.2=encode (f n (π z.1)))
    (G : Set X) (l : (π '' G) → Point)
    (hjoint : ∀ p : (π '' G), Tendsto (fun q : ℕ × Point => f q.1 q.2)
      (atTop ×ˢ 𝓝 (p:Point)) (𝓝 (l p))) :
    ∀ z∈(μ:Measure (X×Cube)).support, ∀ hz : z.1∈G,
      z.2=encode (l ⟨π z.1,mem_image_of_mem π hz⟩) := by
  intro z hz hG
  apply support_spatial_graph hμ π hπ (f∘τ)
    (Filter.Eventually.of_forall (fun n => hid (τ n))) G l _ hz hG
  intro p
  exact (hjoint p).comp (hτ.tendsto_atTop.prodMap tendsto_id)

lemma Converges.spatial_impossible {F : ℕ → Configuration} {L : Data} (hF : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop) (emb : ∀ n, (F n).SweepEmbedding)
    {C : ℝ} (hC : 0≤C)
    (hcoeff : ∀ n, 4608*((F n).a:ℝ)^2*(F n).n^4 / (((F n).R:ℝ)*(F n).a^2)^3≤C)
    (herror : Tendsto (fun n => 13824*((F n).n:ℝ)^3 / (((F n).R:ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (J : Window) {A B : Window} (hAB : Before A B)
    (hA : ∀ n, 0<length (F n).R A) (hB : ∀ n, 0<length (F n).R B)
    (E : ℕ → Point ≃L[ℝ] Point)
    (hframe : ∀ n, ∃ a b l u : ℝ, 0<a ∧ 0<b ∧ l<u ∧
      E n (1,0)=a • (1,l) ∧ E n (0,1)=b • (1,u) ∧
      ∀ i, ((F n).system.timeWindow J).slope i∈Icc l u)
    (T : Set Labels) (hT : MeasurableSet T) (hTp : (L.edgeWindow J:Measure Labels) T≠0)
    (hac : ((L.edgeWindow J:Measure Labels).restrict T).map (pairCoordinates true A B)≪volume)
    (hrad : ∀ᵐ z ∂(L.edgeWindow J:Measure Labels).restrict T,
      pairCoordinates true A B z∈Ioo (0:ℝ) 1 ×ˢ Ioo (-1:ℝ) 0 ∧
      ∃ C₀ : ℝ, 0<C₀ ∧ ∀ Q : ℝ, 1≤Q → ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ᶠ n in atTop,
        RadialCompare (commonChart (F n) hAB (hA n) (hB n) (E n)).symm
          (pairCoordinates true A B z) r C₀ Q) : False := by
  let π := pairCoordinates true A B
  let f := fun n => commonChart (F n) hAB (hA n) (hB n) (E n)
  obtain ⟨G,hG,hGT,hGp,m,hdensity,p₀,U,hU,φ,l,c,hc,hφ,hl,hjoint,hsep⟩ :=
    positive_spatial_witness (L.points:Measure Labels) (L.edgeWindow J:Measure Labels)
      T hT hTp π (continuous_pairCoordinates true A B).measurable hac f
      (fun n => commonChart_source _ _ _ _ _) (fun n => commonChart_target _ _ _ _ _) hrad
  let o := fun n => ((F n).rankChart hAB (hA n) (hB n)).symm p₀
  let ψ := fun n => physical (E n) (o n) (U n)⁻¹
  obtain ⟨ρ,M,hρ,hM,hprojection⟩ := Enhancement.subsequence (hF.subseq hφ) (fun n => ψ (φ n))
  have hgraph : ∀ z∈(M .point:Measure Space).support, ∀ hz : z.1∈G,
      z.2=encode (l ⟨π z.1,mem_image_of_mem π hz⟩) :=
    support_graph_subseq (μs:=fun n => Enhancement.points (F (φ n)) (ψ (φ n))) hρ
      (hM .point) π (continuous_pairCoordinates true A B)
      (fun n => (normalizeChart (f (φ n)) p₀ (U (φ n)) (hU (φ n)).ne').symm)
      (fun n => normalized_points_graph (F (φ n)) hAB (hA _) (hB _) (E _) p₀ (hU _).ne')
      G l hjoint
  have hmap : (M .point:Measure Space).map Prod.fst=(L.points:Measure Labels) := by
    rw [← FiniteMeasure.toMeasure_map]
    exact congrArg FiniteMeasure.toMeasure (hprojection .point)
  obtain ⟨hH,hbounded,D,hD,hdisk⟩ := support_lift_disk (M .point:Measure Space) G hG π
    (continuous_pairCoordinates true A B).measurable l hc (by rwa [hmap]) hgraph hl hsep
  have hz := enhanced_boundary_zero ((hF.subseq hφ).subseq hρ)
    ((hR.comp hφ.tendsto_atTop).comp hρ.tendsto_atTop) (fun n => emb (φ (ρ n)))
    hC (fun n => hcoeff (φ (ρ n))) ((herror.comp hφ.tendsto_atTop).comp hρ.tendsto_atTop)
    J (fun n => E (φ (ρ n))) (fun n => o (φ (ρ n))) (fun n => (U (φ (ρ n)))⁻¹)
    (fun n => inv_pos.mpr (hU _)) (fun n => hframe (φ (ρ n))) hM hprojection G hG
    (fun z hz => ⟨hbounded z hz,by rw [hgraph z hz.2 hz.1,decode_encode]⟩) hD hdisk
  have hz' : L.edgeWindow J G=0 := NNReal.coe_injective hz
  apply hGp
  rw [← FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure,hz',ENNReal.coe_zero]

end PlanarHalving.RankLimits
namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows Zoom Spatial Enhancement Boundary
open scoped Topology unitInterval

lemma common_finite_eventually (F : ℕ → Configuration)
    (hR : Tendsto (fun n => (F n).R) atTop atTop)
    (A B : Window) {K : Window} (q : CommonChoice K) :
    ∀ᶠ n in atTop, 0<length (F n).R A ∧ 0<length (F n).R B ∧
      (F n).timeSlope (q.time 0)<(F n).timeSlope (q.time 1) ∧
      (F n).timeSlope (q.time 1)<(F n).timeSlope (q.time 2) := by
  filter_upwards [eventually_length_pos _ hR A,eventually_length_pos _ hR B,
    timeSlope_eventually_lt F hR (q.time_strictMono (by decide : (0:Fin 3)<1)),
    timeSlope_eventually_lt F hR (q.time_strictMono (by decide : (1:Fin 3)<2))]
    with n hA hB h12 h23
  exact ⟨hA,hB,h12,h23⟩

lemma joint_shift {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : ℕ → X → Y) {p : X} {y : Y}
    (h : Tendsto (fun z : ℕ × X => f z.1 z.2) (atTop ×ˢ 𝓝 p) (𝓝 y)) (N : ℕ) :
    Tendsto (fun z : ℕ × X => f (z.1+N) z.2) (atTop ×ˢ 𝓝 p) (𝓝 y) :=
  h.comp ((tendsto_add_atTop_nat N).prodMap tendsto_id)

lemma Converges.analytic_ready {F : ℕ → Configuration} {L : Data} (hF : Converges F L)
    (hR : Tendsto (fun n => (F n).R) atTop atTop)
    {K A B : Window} (hAB : Before A B) (hKA : Before K A) (hKB : Before K B)
    (q : CommonChoice K) :
    ∃ (φ : ℕ → ℕ) (G : Subwindows K → Point → I), StrictMono φ ∧
      (∀ n, 0<length (F (φ n)).R A ∧ 0<length (F (φ n)).R B ∧
        (F (φ n)).timeSlope (q.time 0)<(F (φ n)).timeSlope (q.time 1) ∧
        (F (φ n)).timeSlope (q.time 1)<(F (φ n)).timeSlope (q.time 2)) ∧
      (∀ i, ∀ᵐ p ∂(volume:Measure Point), DifferentiableAt ℝ (fun x => (G i x:ℝ)) p) ∧
      (∀ i z, z∈(L.points:Measure Labels).support →
        ContinuousAt (G i) (pairCoordinates true A B z) → z i.val=G i (pairCoordinates true A B z)) ∧
      ∀ i p, ContinuousAt (G i) p → Tendsto
        (fun z : ℕ × Point => (F (φ z.1)).extendedRank true A B i.val z.2)
        (atTop ×ˢ 𝓝 p) (𝓝 (G i p)) := by
  have hC (i : Subwindows K) : Before i.val A ∧ Before i.val B :=
    ⟨(endpoints_of_subset i.property).2.trans hKA,(endpoints_of_subset i.property).2.trans hKB⟩
  obtain ⟨φ,G,hφ,_,hGaed,hid,hjoint⟩ := hF.rank_analytic hR true hAB
    (fun i : Subwindows K => i.val) (fun i => hC i)
  have hR' : Tendsto (fun n => (F (φ n)).R) atTop atTop := hR.comp hφ.tendsto_atTop
  have he := common_finite_eventually (F∘φ) hR' A B q
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  refine ⟨fun n => φ (n+N),G,(fun _ _ h => hφ (Nat.add_lt_add_right h N)),
    (fun n => hN (n+N) (Nat.le_add_left N n)),hGaed,hid,?_⟩
  intro i p hp
  exact joint_shift (fun n => (F (φ n)).extendedRank true A B i.val) (hjoint i p hp) N

end PlanarHalving.RankLimits

namespace PlanarHalving.RankLimits
open Set Filter MeasureTheory Metric Batches TimeWindows Zoom Spatial Enhancement Boundary
open scoped Topology unitInterval

lemma Converges.impossible {F : ℕ → Configuration} {L : Data} (hF : Converges F L)
    (emb : ∀ n, (F n).SweepEmbedding) (hR : Tendsto (fun n => (F n).R) atTop atTop)
    (hM : Tendsto (fun n => (F n).a*(F n).n) atTop atTop)
    {C : ℝ} (hC : 0≤C)
    (hcoeff : ∀ n, 4608*((F n).a:ℝ)^2*(F n).n^4 / (((F n).R:ℝ)*(F n).a^2)^3≤C)
    (herror : Tendsto (fun n => 13824*((F n).n:ℝ)^3 / (((F n).R:ℝ)*(F n).a^2)^3) atTop (𝓝 0))
    (hshort : Tendsto (fun n => ((F n).n:ℝ)/((F n).R*(F n).a)) atTop (𝓝 0)) : False := by
  obtain ⟨K,H,A,B,T,hKH,hAH,hBH,hAB,hT,hTp,hpos,hcross,hpts⟩ :=
    hF.positive_part emb hR hC hcoeff herror hshort
  obtain ⟨q,V,hV,hVT,hcommon,hVp,hVle⟩ := hF.common_positive hR K
    (hF.conditional_nullSingleton emb hR hC hcoeff herror) hT hTp (fun z hz => (hpos z hz).1)
  let ν := (L.edgeWindow q.val.2.2:Measure Labels).restrict V
  have he : ν≪(L.edge:Measure Labels) :=
    Measure.absolutelyContinuous_of_le (hVle.trans Measure.restrict_le_self)
  have hp : ν≪(L.points:Measure Labels) := (Measure.absolutelyContinuous_of_le hVle).trans hpts
  have hproj : ν.map (pairCoordinates true A B)≪volume :=
    (((Measure.absolutelyContinuous_of_le hVle).trans hcross).map
      (continuous_pairCoordinates true A B).measurable).trans (hF.crossing_signed_projection hR hM true hAB)
  have hgood : ∀ᵐ z ∂ν, L.conditional z (carrier K)≠0 ∧ z∈commonSet L q := by
    filter_upwards [ae_restrict_mem hV] with z hz
    exact ⟨(hpos z (hVT hz)).1,hcommon z hz⟩
  have hKA : Before K A := hKH.2.1.le.trans (endpoints_of_subset hAH).1
  have hKB : Before K B := hKH.2.1.le.trans (endpoints_of_subset hBH).1
  obtain ⟨φ,G,hφ,hfinite,hGaed,hid,hjoint⟩ := hF.analytic_ready hR hAB hKA hKB q
  have hF' : Converges (F∘φ) L := hF.subseq hφ
  have hR' : Tendsto (fun n => (F (φ n)).R) atTop atTop := hR.comp hφ.tendsto_atTop
  obtain ⟨E,hE,hframe⟩ := common_frame (F∘φ) q
    (fun n => (hfinite n).2.2.1) (fun n => (hfinite n).2.2.2)
  exact hF'.spatial_impossible hR' (fun n => emb (φ n)) hC (fun n => hcoeff (φ n))
    (herror.comp hφ.tendsto_atTop) q.val.2.2 hAB (fun n => (hfinite n).1)
    (fun n => (hfinite n).2.1) E hframe V hV hVp hproj
    (hF'.radial_ae (fun n => emb (φ n)) hR' (hM.comp hφ.tendsto_atTop) hC
      (fun n => hcoeff (φ n)) (herror.comp hφ.tendsto_atTop) (hshort.comp hφ.tendsto_atTop)
      hAB hKA hKB (fun n => (hfinite n).1) (fun n => (hfinite n).2.1)
      G hjoint hGaed hid ν he hp hproj q hgood E hE)

end PlanarHalving.RankLimits
namespace PlanarHalving.RankLimits
open Filter
open scoped Topology

lemma normalized_sequence_impossible (F : ℕ → Configuration)
    (emb : ∀ n, (F n).SweepEmbedding) {c : ℝ} (hc : 0<c)
    (hnear : ∀ n, c*((F n).n:ℝ)^4≤((F n).R:ℝ)^3*((F n).a:ℝ)^4)
    (hq : Tendsto (fun n => ((F n).n:ℝ)/(F n).a) atTop atTop) : False := by
  obtain ⟨φ,L,hφ,hF⟩ := subsequence F
  have hnear' : ∀ n, c*((F (φ n)).n:ℝ)^4≤((F (φ n)).R:ℝ)^3*((F (φ n)).a:ℝ)^4 :=
    fun n => hnear (φ n)
  have hq' := hq.comp hφ.tendsto_atTop
  have hs := normalization_sizes_atTop hc hnear' hq'
  exact hF.impossible (fun n => emb (φ n)) hs.2.2 hs.2.1 (by positivity : 0≤4608/c)
    (fun n => (F (φ n)).normalization_coefficient hc (hnear' n))
    (sparse_error_tendsto_zero hc hnear' hq') (short_ratio_tendsto_zero hc hnear' hq')

theorem uniform_batch_saving {c : ℝ} (hc : 0<c) :
    ∃ Q : ℝ, 0<Q ∧ ∀ F : Configuration, F.SweepEmbedding → Q≤(F.n:ℝ)/F.a →
      (F.R:ℝ)^3*(F.a:ℝ)^4≤c*(F.n:ℝ)^4 := by
  by_contra h
  push Not at h
  have hex (m : ℕ) : ∃ F : Configuration, Nonempty F.SweepEmbedding ∧
      (m:ℝ)+1≤(F.n:ℝ)/F.a ∧ c*(F.n:ℝ)^4≤(F.R:ℝ)^3*(F.a:ℝ)^4 := by
    obtain ⟨F,emb,hq,hnear⟩ := h ((m:ℝ)+1) (by positivity)
    exact ⟨F,⟨emb⟩,hq,hnear.le⟩
  choose F he hq hn using hex
  have hlim : Tendsto (fun m => ((F m).n:ℝ)/(F m).a) atTop atTop := by
    apply tendsto_atTop_mono hq
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  exact normalized_sequence_impossible F (fun n => (he n).some) hc hn hlim

end PlanarHalving.RankLimits
namespace PlanarHalving.Sweep
open Set RankLimits

noncomputable def greedyConfiguration {n k : ℕ} {P : Fin n → Point}
    (hP : Generic P) (hk : k≤n) (a : ℕ) (ha : 0<a) (hn : 0<n)
    (hR : 0<((states P hP hk).greedy 0 a ha).count) : Configuration where
  n := n
  R := ((states P hP hk).greedy 0 a ha).count
  k := k
  a := a
  n_pos := hn
  R_pos := hR
  a_pos := ha
  point := P
  generic := hP
  system := (states P hP hk).greedySystem a ha

noncomputable def greedyConfiguration_embedding {n k : ℕ} {P : Fin n → Point}
    (hP : Generic P) (hk : k≤n) (a : ℕ) (ha : 0<a) (hn : 0<n)
    (hR : 0<((states P hP hk).greedy 0 a ha).count) :
    (greedyConfiguration hP hk a ha hn hR).SweepEmbedding where
  rank_le := hk
  index := ((states P hP hk).greedy 0 a ha).index
  increasing := ((states P hP hk).greedy 0 a ha).increasing
  marks := fun _ => rfl

lemma distance_saving {c : ℝ} (hc : 0<c) :
    ∃ Q : ℝ, 0<Q ∧ ∀ {n k : ℕ} (P : Fin n → Point) (hP : Generic P) (hk : k≤n),
      ∀ {d : ℕ}, 0<d → Q≤(n:ℝ)/d →
      ∀ C : Finset (Fin ((traversal (criticalSlopes P)).size+1) × Fin ((traversal (criticalSlopes P)).size+1)),
      StepDisjoint C → (∀ p∈C, p.1≤p.2) →
      (∀ p∈C, d≤(states P hP hk).distance p.1 p.2) →
      (C.card:ℝ)^3*(d:ℝ)^4≤16*c*(n:ℝ)^4 := by
  obtain ⟨Q,hQ,hbatch⟩ := uniform_batch_saving hc
  refine ⟨Q,hQ,?_⟩
  intro n k P hP hk d hd hq C hC hord hdist
  let S := states P hP hk
  let a := (d+1)/2
  have ha : 0<a := by dsimp [a];omega
  have had : a≤d := by dsimp [a];omega
  let R := (S.greedy 0 a ha).count
  have hcount : C.card≤R := S.greedy_packing hd C hC hord hdist
  by_cases hR : 0<R
  · have hn : 0<n := by
      by_contra hn
      have hn0 : n=0 := by omega
      have hq0 : (n:ℝ)/d=0 := by simp [hn0]
      rw [hq0] at hq
      exact (not_le_of_gt hQ) hq
    let F := greedyConfiguration hP hk a ha hn hR
    have hbd : (R:ℝ)^3*(a:ℝ)^4≤c*(n:ℝ)^4 :=
      hbatch F (greedyConfiguration_embedding hP hk a ha hn hR)
        (hq.trans (div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast ha) (by exact_mod_cast had)))
    have hda : (d:ℝ)≤2*(a:ℝ) := by exact_mod_cast (show d≤2*a by dsimp [a];omega)
    calc
      _ ≤ (R:ℝ)^3*(2*(a:ℝ))^4 := by gcongr
      _ = 16*((R:ℝ)^3*(a:ℝ)^4) := by ring
      _ ≤ 16*(c*(n:ℝ)^4) := mul_le_mul_of_nonneg_left hbd (by norm_num)
      _ = _ := by ring
  · have hz : C.card=0 := by omega
    simp only [hz,Nat.cast_zero,zero_pow (by omega : (3:ℕ)≠0),zero_mul]
    positivity

end PlanarHalving.Sweep
namespace PlanarHalving.Sweep
open Set

theorem activity_saving_cubic {δ : ℝ} (hδ : 0<δ) :
    ∃ Q : ℝ, 0<Q ∧ ∀ {n k : ℕ} (P : Fin n → Point) (hP : Generic P) (hk : k≤n),
      ∀ {b : ℕ}, 0<b → Q≤(n:ℝ)/b →
      ∀ C : Finset (Fin ((traversal (criticalSlopes P)).size+1) × Fin ((traversal (criticalSlopes P)).size+1)),
      StepDisjoint C → (horder : ∀ p∈C, p.1≤p.2) →
      (∀ p, ∀ hp : p∈C, b≤((states P hP hk).intervalActivity p.1 p.2 (horder p hp)).card) →
      (C.card:ℝ)^3*(b:ℝ)^4≤524288*δ*(n:ℝ)^4 := by
  obtain ⟨Q,hQ,hdist⟩ := distance_saving hδ
  refine ⟨Q,hQ,?_⟩
  intro n k P hP hk b hb hq C hC horder hactivity
  classical
  let S := states P hP hk
  by_cases hb4 : 4≤b
  · let c := b/4
    have hc : 0<c := by dsimp [c]; omega
    have hbLe : (b : ℝ)≤8*(c : ℝ) := by exact_mod_cast (show b≤8*c by dsimp [c]; omega)
    let A := C.filter (fun p => ∃ hk' : k+c≤n, c≤(states P hP hk').distance p.1 p.2)
    let B := C\A
    have hA : A⊆C := Finset.filter_subset _ _
    have hB : B⊆C := Finset.sdiff_subset
    have hbound (D : Finset _) (hD : D⊆C) (r : ℕ)
        (hd : ∀ p∈D, ∃ hr : r≤n, c≤(states P hP hr).distance p.1 p.2) :
        (D.card : ℝ)^3*(c : ℝ)^4≤16*δ*(n : ℝ)^4 := by
      by_cases hne : D.Nonempty
      · obtain ⟨p,hp⟩ := hne
        obtain ⟨hr,_⟩ := hd p hp
        apply hdist P hP hr hc (hq.trans (div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hc) (by exact_mod_cast (show c≤b by dsimp [c];omega)))) D
        · exact fun p hp q hq hpq => hC p (hD hp) q (hD hq) hpq
        · exact fun p hp => horder p (hD hp)
        · intro p hp
          obtain ⟨hr',hh⟩ := hd p hp
          exact hh
      · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.card_empty,Nat.cast_zero,zero_pow (by omega : (3:ℕ)≠0),zero_mul]
        positivity
    have hAb := hbound A hA (k+c) (fun p hp => (Finset.mem_filter.mp hp).2)
    have hBb := hbound B hB (k-c) (fun p hp => by
      have hpC := hB hp
      have hh := states_intervalActivity_distance P hP hk (horder p hpC)
        ((show 4*c≤b from Nat.mul_div_le b 4).trans (hactivity p hpC))
      rcases hh with hh | ⟨hr,_,hh⟩
      · exact False.elim ((Finset.mem_sdiff.mp hp).2 (Finset.mem_filter.mpr ⟨hpC,hh⟩))
      · exact ⟨hr,hh⟩)
    have hcard : (C.card : ℝ)=(A.card : ℝ)+(B.card : ℝ) := by
      exact_mod_cast (by simpa only [B,Nat.add_comm] using (Finset.card_sdiff_add_card_eq_card hA).symm : C.card=A.card+B.card)
    have hsum := mul_le_mul_of_nonneg_right (cube_add_le (show (0:ℝ)≤A.card by positivity) (show (0:ℝ)≤B.card by positivity)) (show (0:ℝ)≤(c : ℝ)^4 by positivity)
    rw [← hcard] at hsum
    have hcub : (C.card : ℝ)^3*(c : ℝ)^4≤128*δ*(n : ℝ)^4 := by nlinarith [hAb,hBb]
    calc
      _ ≤ (C.card : ℝ)^3*(8*(c : ℝ))^4 := by gcongr
      _ = 4096*((C.card : ℝ)^3*(c : ℝ)^4) := by ring
      _ ≤ 4096*(128*δ*(n : ℝ)^4) := mul_le_mul_of_nonneg_left hcub (by norm_num)
      _ ≤ _ := by nlinarith [mul_nonneg hδ.le (sq_nonneg ((n : ℝ)^2))]
  · have hd := hdist P hP hk (by omega : 0<1) (by simpa using hq.trans (div_le_self (by positivity) (by exact_mod_cast hb))) C hC horder
      (fun p hp => S.intervalActivity_pos_distance (horder p hp) (lt_of_lt_of_le hb (hactivity p hp)))
    norm_num at hd
    have hbLe : (b : ℝ)≤3 := by exact_mod_cast (by omega : b≤3)
    calc
      _ ≤ (C.card : ℝ)^3*3^4 := by gcongr
      _ ≤ 16*δ*(n : ℝ)^4*3^4 := mul_le_mul_of_nonneg_right hd (by norm_num)
      _ ≤ _ := by nlinarith [mul_nonneg hδ.le (sq_nonneg ((n : ℝ)^2))]

end PlanarHalving.Sweep

end OAI
