import OAI.Geometry.PlaneColoring.GraphRealization
import OAI.Geometry.PlaneColoring.Interfaces
import OAI.Geometry.PlaneColoring.Sectors

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
/-- Vanishing exceptional measure is enough: almost every point is outside the
exceptional sets infinitely often. No summability or nesting is required. -/
lemma ae_frequently_notMem_of_measure_tendsto_zero {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {E : ℕ → Set X}
    (hE : Tendsto (fun n => μ (E n)) atTop (𝓝 0)) :
    ∀ᵐ z ∂μ, ∃ᶠ n in atTop, z ∉ E n := by
  let T : ℕ → Set X := fun N => ⋂ n ≥ N, E n
  have hT : ∀ N, μ (T N) = 0 := by
    intro N
    apply le_antisymm _ (by positivity)
    apply ge_of_tendsto hE
    filter_upwards [eventually_ge_atTop N] with n hn
    exact measure_mono (fun z hz => (mem_iInter.mp (mem_iInter.mp hz n)) hn)
  have hn : μ (⋃ N, T N) = 0 := measure_iUnion_null hT
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hn] with z hz
  rw [← not_eventually]
  intro he
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  exact hz (mem_iUnion.mpr ⟨N,mem_iInter.mpr fun n => mem_iInter.mpr (hN n)⟩)

/-- Pointwise differentiation plus vanishing exceptional sets gives the measure
exclusion used for both the mesh bound and the common continuum exclusions. -/
lemma ae_ne_one_of_eventual_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {p : ℕ → X → ℝ} {f : X → ℝ} {E : ℕ → Set X} {U : Set X}
    {α : ℝ} (hα : 0 < α)
    (hp : ∀ᵐ z ∂μ, Tendsto (fun n => p n z) atTop (𝓝 (f z)))
    (hE : Tendsto (fun n => μ (E n)) atTop (𝓝 0))
    (hb : ∀ z ∈ U, ∀ᶠ n in atTop, z ∉ E n → p n z ≤ 1-α) :
    ∀ᵐ z ∂μ, z ∈ U → f z ≠ 1 := by
  filter_upwards [hp,ae_frequently_notMem_of_measure_tendsto_zero hE] with z hz hgood hzU hf
  have hgt : ∀ᶠ n in atTop, 1-α < p n z :=
    hz.eventually (Ioi_mem_nhds (by rw [hf]; linarith))
  obtain ⟨n,hn,hbnd,hlarge⟩ := (hgood.and_eventually ((hb z hzU).and hgt)).exists
  exact (not_lt_of_ge (hbnd hn)) hlarge
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory MeasureTheory.Measure
namespace EuclideanFiveColor
lemma colorFn_locallyIntegrable {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c) (i : Fin k) :
    LocallyIntegrable (colorFn c i) (volume : Measure ℂ) :=
  (continuous_const.locallyIntegrable (f := fun _ : ℂ => (1:ℝ))).mono
    (colorFn_measurable hc i).aestronglyMeasurable (Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (colorFn_nonneg c i z),abs_one] using colorFn_le_one c i z)
lemma diskAverage_eq_average_ball {k : ℕ} (c : ℂ → Fin k) (ε : ℝ) (i : Fin k) (q : ℂ) :
    diskAverage c ε i q = ⨍ z in Metric.ball q ε, colorFn c i z ∂volume := by
  have he : (fun v : ℂ => q+v) ⁻¹' Metric.ball q ε = Metric.ball 0 ε := by
    ext v
    simp [Metric.mem_ball,dist_eq_norm]
  have hi := (measurePreserving_add_left (volume : Measure ℂ) q).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft q).measurableEmbedding (colorFn c i) (Metric.ball q ε)
  rw [he] at hi
  unfold diskAverage diskLaw
  rw [integral_smul_measure,ENNReal.toReal_inv,hi,setAverage_eq]
  simp only [Measure.real,Complex.volume_ball]
lemma complex_ball_ae_closedBall (q : ℂ) (ε : ℝ) :
    Metric.ball q ε =ᵐ[volume] Metric.closedBall q ε :=
  ae_eq_of_subset_of_measure_ge Metric.ball_subset_closedBall
    (by rw [Complex.volume_closedBall,Complex.volume_ball])
    measurableSet_ball.nullMeasurableSet ((isCompact_closedBall q ε).measure_ne_top)
lemma diskAverage_ae_tendsto {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n,0<ε n) (i : Fin k) :
    ∀ᵐ z : ℂ ∂volume, Tendsto (fun n => diskAverage c (ε n) i z) atTop (𝓝 (colorFn c i z)) := by
  have hε' : Tendsto ε atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨hε,Eventually.of_forall hpos⟩
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average volume
    (colorFn_locallyIntegrable hc i) 1] with z hz
  have h := hz (fun _ : ℕ => z) ε hε' (Eventually.of_forall fun n => by
    simp only [one_mul,Metric.mem_closedBall,dist_self]; exact (hpos n).le)
  convert h using 1
  ext n
  rw [diskAverage_eq_average_ball]
  exact setAverage_congr (complex_ball_ae_closedBall z (ε n))

lemma support_disjoint_open_of_ae {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c)
    {U : Set ℂ} (hU : IsOpen U) (i : Fin k)
    (h : ∀ᵐ z ∂(volume : Measure ℂ),z∈U → c z≠i) :
    Disjoint (spatialSupport c i) U := by
  have he : Uᶜ ∈ ae (volume.restrict {z | c z=i}) := by
    change ∀ᵐ z ∂volume.restrict {z | c z=i},z∈Uᶜ
    rw [ae_restrict_iff' (measurableSet_eq_fun hc measurable_const)]
    filter_upwards [h] with z hz hczi hzU
    exact hz hzU hczi
  have hs := Measure.support_subset_of_isClosed hU.isClosed_compl he
  exact Set.disjoint_left.mpr fun z hz hzU => hs hz hzU

lemma diskAverage_support_exclusion {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n,0<ε n)
    {E : ℕ → Set ℂ} (hE : Tendsto (fun n => volume (E n)) atTop (𝓝 0))
    {α : ℝ} (hα : 0<α) {U : Set ℂ} (hU : IsOpen U) (i : Fin k)
    (hb : ∀ z∈U,∀ᶠ n in atTop,z∉E n → diskAverage c (ε n) i z≤1-α) :
    Disjoint (spatialSupport c i) U := by
  apply support_disjoint_open_of_ae hc hU i
  filter_upwards [ae_ne_one_of_eventual_bound hα (diskAverage_ae_tendsto hc hε hpos i) hE hb]
    with z hz hzU hczi
  exact hz hzU (by simp [colorFn,hczi])
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Filter Topology TopologicalSpace
universe u v
namespace EuclideanFiveColor
/-- Connectedness passes to a Vietoris (equivalently compact Hausdorff metric) limit. -/
theorem nonemptyCompacts_preconnected_limit {X : Type u} [TopologicalSpace X]
    [T2Space X] [NormalSpace X] {ι : Type v} {l : Filter ι} [NeBot l]
    {K : ι → NonemptyCompacts X} {L : NonemptyCompacts X}
    (hlim : Tendsto K l (𝓝 L)) (hc : ∀ᶠn in l,IsPreconnected (K n : Set X)) :
    IsPreconnected (L : Set X) := by
  apply (isPreconnected_iff_subset_of_fully_disjoint_closed L.isCompact.isClosed).mpr
  intro A B hA hB hcov hd
  by_contra hh
  push Not at hh
  obtain ⟨x,hx,hxA⟩ := Set.not_subset.mp hh.1
  obtain ⟨y,hy,hyB⟩ := Set.not_subset.mp hh.2
  have hxB := (hcov hx).resolve_left hxA
  have hyA := (hcov hy).resolve_right hyB
  obtain ⟨U,V,hU,hV,hAU,hBV,hUV⟩ := normal_separation hA hB hd
  have hL : (L : Set X)⊆U∪V := hcov.trans (union_subset_union hAU hBV)
  have hs : ∀ᶠn in l,(K n : Set X)⊆U∪V := hlim.eventually
    ((NonemptyCompacts.isOpen_subsets_of_isOpen (hU.union hV)).mem_nhds hL)
  have hu : ∀ᶠn in l,((K n : Set X)∩U).Nonempty := hlim.eventually
    ((NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hU).mem_nhds ⟨y,hy,hAU hyA⟩)
  have hv : ∀ᶠn in l,((K n : Set X)∩V).Nonempty := hlim.eventually
    ((NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hV).mem_nhds ⟨x,hx,hBV hxB⟩)
  obtain ⟨n,hnc,hns,hnu,hnv⟩ := (hc.and (hs.and (hu.and hv))).exists
  obtain ⟨z,_,hzU,hzV⟩ := hnc U V hU hV hns hnu hnv
  exact Set.disjoint_left.mp hUV hzU hzV

lemma nonemptyCompacts_mem_limit {X : Type u} [MetricSpace X]
    {ι : Type v} {l : Filter ι} [NeBot l]
    {K : ι → NonemptyCompacts X} {L : NonemptyCompacts X} {x : ι → X} {y : X}
    (hK : Tendsto K l (𝓝 L)) (hx : Tendsto x l (𝓝 y))
    (hm : ∀ᶠn in l,x n∈K n) : y∈L := by
  have hh := (NonemptyCompacts.lipschitz_infDist.continuous.tendsto (y,L)).comp (hx.prodMk_nhds hK)
  have h0 : (fun n => Metric.infDist (x n) (K n : Set X)) =ᶠ[l] fun _ => 0 :=
    hm.mono fun n hn => Metric.infDist_zero_of_mem hn
  have he : Metric.infDist y (L : Set X)=0 := tendsto_nhds_unique hh
    (tendsto_const_nhds.congr' h0.symm)
  exact (L.isCompact.isClosed.mem_iff_infDist_zero L.nonempty).mpr he

lemma nonemptyCompacts_inter_closed_limit {X : Type u} [TopologicalSpace X]
    {ι : Type v} {l : Filter ι} [NeBot l]
    {K : ι → NonemptyCompacts X} {L : NonemptyCompacts X} {F : Set X}
    (hF : IsClosed F) (hK : Tendsto K l (𝓝 L))
    (hm : ∀ᶠn in l,((K n : Set X)∩F).Nonempty) : ((L : Set X)∩F).Nonempty :=
  (NonemptyCompacts.isClosed_inter_nonempty_of_isClosed hF).mem_of_tendsto hK hm

/-- A finite family of nonempty compact continua in a compact metric space has
one common subsequence of connected compact limits. -/
theorem finite_continuum_subsequence {X : Type u} [MetricSpace X] [CompactSpace X]
    {J : Type v} [Finite J] (K : ℕ → J → NonemptyCompacts X)
    (hc : ∀n j,IsPreconnected (K n j : Set X)) :
    ∃L : J → NonemptyCompacts X, ∃φ : ℕ → ℕ, StrictMono φ ∧
      (∀j,Tendsto (fun n => K (φ n) j) atTop (𝓝 (L j))) ∧
      (∀j,IsPreconnected (L j : Set X)) := by
  obtain ⟨L,_,φ,hφ,hlim⟩ := (isCompact_univ : IsCompact (Set.univ : Set (J → NonemptyCompacts X))).tendsto_subseq (fun n => Set.mem_univ (K n))
  refine ⟨L,φ,hφ,?_,?_⟩
  · intro j
    exact (continuous_apply j).continuousAt.tendsto.comp hlim
  · intro j
    exact nonemptyCompacts_preconnected_limit
      ((continuous_apply j).continuousAt.tendsto.comp hlim)
      (Eventually.of_forall fun n => hc (φ n) j)
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory TopologicalSpace
namespace EuclideanFiveColor
lemma straddle_eventually_of_compact_limit {K : ℕ → NonemptyCompacts ℂ}
    {L : NonemptyCompacts ℂ} (hlim : Tendsto K atTop (𝓝 L)) {z : ℂ}
    (hz : z∈Straddle (L : Set ℂ)) : ∀ᶠ n in atTop,z∈Straddle (K n : Set ℂ) := by
  obtain ⟨p,hp,q,hq,hp1,hq1⟩ := hz
  have ha : ∀ᶠn in atTop,((K n : Set ℂ)∩{p : ℂ | dist z p<1}).Nonempty :=
    hlim.eventually ((NonemptyCompacts.isOpen_inter_nonempty_of_isOpen
      (isOpen_lt (continuous_const.dist continuous_id) continuous_const)).mem_nhds ⟨p,hp,hp1⟩)
  have hb : ∀ᶠn in atTop,((K n : Set ℂ)∩{q : ℂ | 1<dist z q}).Nonempty :=
    hlim.eventually ((NonemptyCompacts.isOpen_inter_nonempty_of_isOpen
      (isOpen_lt continuous_const (continuous_const.dist continuous_id))).mem_nhds ⟨q,hq,hq1⟩)
  filter_upwards [ha,hb] with n hn hm
  obtain ⟨p,hp,hp1⟩ := hn
  obtain ⟨q,hq,hq1⟩ := hm
  exact ⟨p,hp,q,hq,hp1,hq1⟩
/-- The common-exclusion continuum limit argument. The sole exceptional sets are
actual unit neighborhoods of the holes, and their measures tend to zero. -/
theorem continuum_limit_support_exclusion {k : ℕ} {c : ℂ → Fin k}
    (hc : Measurable c) (hw : WeakColoring k c)
    {K : ℕ → NonemptyCompacts ℂ} {L : NonemptyCompacts ℂ}
    (hlim : Tendsto K atTop (𝓝 L)) (hconn : ∀n,IsPreconnected (K n : Set ℂ))
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀n,0<ε n)
    {H E : ℕ → Set ℂ} (hE : Tendsto (fun n => volume (E n)) atTop (𝓝 0))
    (hnear : ∀n z q,q∈H n → dist z q=1 → z∈E n)
    {α : ℝ} (hα : 0<α) (i : Fin k)
    (hprob : ∀n q,q∈K n → q∉H n → α<diskAverage c (ε n) i q) :
    Disjoint (spatialSupport c i) (Straddle (L : Set ℂ)) := by
  apply diskAverage_support_exclusion hc hε hpos hE hα (straddle_isOpen _) i
  intro z hz
  filter_upwards [straddle_eventually_of_compact_limit hlim hz] with n hn hzE
  obtain ⟨q,hq,hunit⟩ := straddle_connected_unit (hconn n) hn
  have hqH : q∉H n := fun hh => hzE (hnear n z q hh hunit)
  have hb := hprob n q hq hqH
  have hu : ‖q-z‖=1 := by simpa only [dist_eq_norm,norm_sub_rev] using hunit
  have hh := diskAverage_unit_pair hc hw (hpos n) hu i
  linarith
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
/-- One interface excludes both labels from the same straddling set and approaches
its center in an actual unit direction. -/
def CommonInterface (c : ℂ → Fin 5) (x : ℂ) (i j : Fin 5) : Prop :=
  ∃K : Set ℂ, ∃v : ℂ, ‖v‖=1 ∧ Nonempty (ApproachingContinuum x K v) ∧
    Disjoint (spatialSupport c i) (Straddle K) ∧ Disjoint (spatialSupport c j) (Straddle K)
lemma CommonInterface.symm {c : ℂ → Fin 5} {x : ℂ} {i j : Fin 5}
    (h : CommonInterface c x i j) : CommonInterface c x j i := by
  obtain ⟨K,v,hv,hK,hi,hj⟩ := h
  exact ⟨K,v,hv,hK,hj,hi⟩
lemma spatialSupport_perm (c : ℂ → Fin 5) (e : Equiv.Perm (Fin 5)) (i : Fin 5) :
    spatialSupport (e.symm ∘ c) i=spatialSupport c (e i) := by
  have he : {z : ℂ | (e.symm ∘ c) z=i}={z : ℂ | c z=e i} := by
    ext z
    exact e.symm_apply_eq
  simp only [spatialSupport,he]
lemma CommonInterface.perm {c : ℂ → Fin 5} {x : ℂ} (e : Equiv.Perm (Fin 5))
    {i j : Fin 5} (h : CommonInterface c x (e i) (e j)) :
    CommonInterface (e.symm ∘ c) x i j := by
  obtain ⟨K,v,hv,hK,hi,hj⟩ := h
  exact ⟨K,v,hv,hK,by rwa [spatialSupport_perm],by rwa [spatialSupport_perm]⟩
lemma commonInterface_of_continuum {c : ℂ → Fin 5} {x y : ℂ} {i j : Fin 5}
    {K : Set ℂ} (hK : IsPreconnected K) (hx : x∈K) (hy : y∈K) (hne : y≠x)
    (hi : Disjoint (spatialSupport c i) (Straddle K))
    (hj : Disjoint (spatialSupport c j) (Straddle K)) : CommonInterface c x i j := by
  obtain ⟨v,hv,ha⟩ := continuum_has_approach hK hx hy hne
  exact ⟨K,v,hv,ha,hi,hj⟩
lemma no_triangle_commonInterface {c : ℂ → Fin 5} (hc : Measurable c)
    (hw : WeakColoring 5 c) {x : ℂ} (h01 : CommonInterface c x 0 1)
    (h12 : CommonInterface c x 1 2) (h20 : CommonInterface c x 2 0) : False := by
  let a : Fin 3 → Fin 5 := ![0,1,2]
  let b : Fin 3 → Fin 5 := ![1,2,0]
  have h (i : Fin 3) : CommonInterface c x (a i) (b i) := by
    fin_cases i
    · exact h01
    · exact h12
    · exact h20
  choose K v hv hK hA hB using h
  apply no_triangle_interfaces hc hw hv (fun i => Classical.choice (hK i))
  intro i j hj
  have he : triangleEdge i={a i,b i} := by fin_cases i <;> decide
  rw [he] at hj
  rcases Finset.mem_insert.mp hj with rfl|hj
  · exact hA i
  · rw [Finset.mem_singleton] at hj; subst j; exact hB i
lemma no_four_commonInterface {c : ℂ → Fin 5} (hc : Measurable c)
    (hw : WeakColoring 5 c) {x : ℂ} (h01 : CommonInterface c x 0 1)
    (h12 : CommonInterface c x 1 2) (h23 : CommonInterface c x 2 3)
    (h30 : CommonInterface c x 3 0) : False := by
  let a : Fin 4 → Fin 5 := ![0,1,2,3]
  let b : Fin 4 → Fin 5 := ![1,2,3,0]
  have h (i : Fin 4) : CommonInterface c x (a i) (b i) := by
    fin_cases i
    · exact h01
    · exact h12
    · exact h23
    · exact h30
  choose K v hv hK hA hB using h
  apply no_four_interfaces hc hw hv (fun i => Classical.choice (hK i))
  intro i j hj
  have he : fourEdge i={a i,b i} := by fin_cases i <;> decide
  rw [he] at hj
  rcases Finset.mem_insert.mp hj with rfl|hj
  · exact hA i
  · rw [Finset.mem_singleton] at hj; subst j; exact hB i
lemma no_five_commonInterface {c : ℂ → Fin 5} (hc : Measurable c)
    (hw : WeakColoring 5 c) {x : ℂ} (h : ∀i,CommonInterface c x i (i+1)) : False := by
  choose K v hv hK hi hj using h
  exact no_five_exclusion_continua c hc hw hv (fun i => Classical.choice (hK i)) (fun i => ⟨hi i,hj i⟩)
/-- All actual common-exclusion interfaces at a point form a forest. This
assembles triangle, four and five cases for arbitrary labels, not just canonical cycles. -/
theorem commonInterface_graph_acyclic {c : ℂ → Fin 5} (hc : Measurable c)
    (hw : WeakColoring 5 c) (x : ℂ) (G : SimpleGraph (Fin 5))
    (hG : ∀i j,G.Adj i j → CommonInterface c x i j) : G.IsAcyclic := by
  intro v p hp
  obtain ⟨e,he⟩ := cycle_standard_permutation hp
  have hm : Measurable (e.symm ∘ c) := (measurable_of_finite e.symm).comp hc
  have hw' := weak_relabel c e.symm hw
  have h (i j : Fin 5) (hij : G.Adj (e i) (e j)) : CommonInterface (e.symm ∘ c) x i j :=
    (hG _ _ hij).perm e
  rcases he with ⟨h01,h02,h12⟩|⟨h01,h12,h23,h30⟩|hfive
  · exact no_triangle_commonInterface hm hw' (h _ _ h01) (h _ _ h12) (h _ _ h02).symm
  · exact no_four_commonInterface hm hw' (h _ _ h01) (h _ _ h12) (h _ _ h23) (h _ _ h30)
  · exact no_five_commonInterface hm hw' (fun i => h _ _ (hfive i))
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Filter Topology TopologicalSpace MeasureTheory
namespace EuclideanFiveColor
/-- End-to-end limit of actual connected midpoint fibers, retaining both endpoint
exclusions on the same limiting continuum. -/
theorem commonInterface_of_compact_sequence {c : ℂ → Fin 5}
    (hc : Measurable c) (hw : WeakColoring 5 c) {x : ℂ} {ρ : ℝ} (hρ : 0<ρ)
    (K : ℕ → NonemptyCompacts ℂ) (hsub : ∀n,(K n : Set ℂ)⊆Metric.closedBall x ρ)
    (hconn : ∀n,IsPreconnected (K n : Set ℂ))
    (a : ℕ → ℂ) (ha : ∀n,a n∈K n) (halim : Tendsto a atTop (𝓝 x))
    (hout : ∀n,((K n : Set ℂ)∩Metric.sphere x ρ).Nonempty)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀n,0<ε n)
    {H E : ℕ → Set ℂ} (hE : Tendsto (fun n => volume (E n)) atTop (𝓝 0))
    (hnear : ∀n z q,q∈H n → dist z q=1 → z∈E n)
    {α : ℝ} (hα : 0<α) (i j : Fin 5)
    (hi : ∀n q,q∈K n → q∉H n → α<diskAverage c (ε n) i q)
    (hj : ∀n q,q∈K n → q∉H n → α<diskAverage c (ε n) j q) :
    CommonInterface c x i j := by
  obtain ⟨L,hL,φ,hφ,hlim⟩ := (NonemptyCompacts.isCompact_subsets_of_isCompact
    (isCompact_closedBall x ρ)).tendsto_subseq hsub
  have hx : x∈L := nonemptyCompacts_mem_limit hlim (halim.comp hφ.tendsto_atTop)
    (Eventually.of_forall fun n => ha (φ n))
  obtain ⟨y,hy,hyρ⟩ := nonemptyCompacts_inter_closed_limit Metric.isClosed_sphere hlim
    (Eventually.of_forall fun n => hout (φ n))
  have hne : y≠x := by
    intro he
    subst y
    have he : (0:ℝ)=ρ := by simpa only [Metric.mem_sphere,dist_self] using hyρ
    linarith
  apply commonInterface_of_continuum
    (nonemptyCompacts_preconnected_limit hlim (Eventually.of_forall fun n => hconn (φ n))) hx hy hne
  · exact continuum_limit_support_exclusion hc hw hlim (fun n => hconn (φ n))
      (hε.comp hφ.tendsto_atTop) (fun n => hpos (φ n)) (hE.comp hφ.tendsto_atTop)
      (fun n => hnear (φ n)) hα i (fun n => hi (φ n))
  · exact continuum_limit_support_exclusion hc hw hlim (fun n => hconn (φ n))
      (hε.comp hφ.tendsto_atTop) (fun n => hpos (φ n)) (hE.comp hφ.tendsto_atTop)
      (fun n => hnear (φ n)) hα j (fun n => hj (φ n))
end EuclideanFiveColor
end

end OAI
