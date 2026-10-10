import Mathlib
import OAI.Geometry.BallPacking.Moser.SmoothManifoldIntegral
import OAI.Geometry.BallPacking.RelativeJets.SymplecticProjectionNaturality

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

theorem embedding_adapted_neighborhood {e : N → M}
    (he : IsSmoothEmbedding 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e) (a : N) :
    let h := he.isImmersion.isImmersionAt a
    ∃ U : Set M, IsOpen U ∧ e a ∈ U ∧ U ⊆ h.codChart.source ∧
      ∀ b : N, e b ∈ U → b ∈ h.domChart.source ∧
        h.equiv.symm ((h.codChart.extend 𝓘(ℝ,E)) (e b)) =
          ((h.domChart.extend 𝓘(ℝ,F)) b,0) := by
  let h := he.isImmersion.isImmersionAt a
  obtain ⟨V,hV,hpre⟩ := he.isEmbedding.isInducing.isOpen_iff.mp h.domChart.open_source
  refine ⟨V ∩ h.codChart.source,hV.inter h.codChart.open_source,?_,inter_subset_right,?_⟩
  · constructor
    · have ha := h.mem_domChart_source
      rw [←hpre] at ha
      exact ha
    · exact h.mem_codChart_source
  · intro b hb
    have hb' : b ∈ h.domChart.source := by rw [←hpre]; exact hb.1
    refine ⟨hb',?_⟩
    have hz : b ∈ (h.domChart.extend 𝓘(ℝ,F)).source := by
      simpa only [OpenPartialHomeomorph.extend_source] using hb'
    have hh := h.writtenInCharts ((h.domChart.extend 𝓘(ℝ,F)).map_source hz)
    simp only [Function.comp_apply,(h.domChart.extend 𝓘(ℝ,F)).left_inv hz] at hh
    rw [hh,h.equiv.symm_apply_apply]


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold IsManifold
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

omit [IsManifold 𝓘(ℝ,F) ∞ N] in

theorem exists_relative_jet_patch
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M} {e : N → M}
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (he : IsSmoothEmbedding 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e) {T : Set ℝ}
    (hi : ∀ t ∈ T, ∀ b, ((Ω t (e b)).bilinearComp (manifoldMapDifferential (E := E) (F := F) e b)
      (manifoldMapDifferential (E := E) (F := F) e b)).IsInvertible) (a : N) :
    ∃ U : Set (ℝ × M), ∃ f : ℝ × M → ℝ,
      IsOpen U ∧ (∀ t ∈ T, (t,e a) ∈ U) ∧
      ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ f U ∧
      ∀ t ∈ T, ∀ b, (t,e b) ∈ U → f (t,e b) = 0 ∧
        HasMFDerivAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) f (t,e b)
          ((symplecticNormalJet (Ω t (e b)) (manifoldMapDifferential (E := E) (F := F) e b) (α t (e b))).comp
            (ContinuousLinearMap.snd ℝ ℝ E)) := by
  let h := he.isImmersion.isImmersionAt a
  obtain ⟨V,hV,ha,hVd,hVb⟩ := embedding_adapted_neighborhood he a
  have hw : EqOn (h.codChart ∘ e ∘ h.domChart.symm)
      (fun y => h.equiv (y,0)) h.domChart.target := by
    simpa only [Function.comp_def, mfld_simps] using h.writtenInCharts
  let U := relativeLocalDomain Ω h.codChart h.equiv ∩ (univ ×ˢ V)
  refine ⟨U,relativeLocalPotential Ω α h.codChart h.equiv,?_,?_,?_,?_⟩
  · exact (relativeLocalDomain_isOpen hΩ h.codChart_mem_maximalAtlas h.equiv).inter
      (isOpen_univ.prod hV)
  · intro t ht
    exact ⟨relativeLocalDomain_mem Ω h.domChart_mem_maximalAtlas h.codChart_mem_maximalAtlas
      h.equiv hw h.mem_domChart_source h.mem_codChart_source
      (he.contMDiff.mdifferentiable (by simp) a) (hi t ht a),mem_univ _,ha⟩
  · exact (relativeLocalPotential_contMDiffOn hΩ hα h.codChart_mem_maximalAtlas h.equiv).mono
      inter_subset_left
  · intro t ht b hb
    have hbb := hVb b hb.2.2
    have hbd := hVd hb.2.2
    constructor
    · apply localSymplecticPotential_zero
      simpa using congrArg Prod.snd hbb.2
    · exact relativeLocalPotential_hasMFDerivAt hΩ hα h.domChart_mem_maximalAtlas
        h.codChart_mem_maximalAtlas h.equiv hw hbb.1 hbd
        (he.contMDiff.mdifferentiable (by simp) b) (hi t ht b)


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {ι : Type}

omit [IsManifold I ∞ M] in

theorem smoothPartition_eventually_finite_sum {S : Set M}
    (ρ : SmoothPartitionOfUnity ι I M S) (g : ι → M → ℝ) (x : M) :
    (fun y => ∑ᶠ i, ρ i y • g i y) =ᶠ[𝓝 x]
      (fun y => ∑ i ∈ ρ.fintsupport x, ρ i y • g i y) := by
  classical
  filter_upwards [ρ.eventually_finsupport_subset x] with y hy
  rw [←ρ.sum_finsupport_smul_eq_finsum y g]
  apply Finset.sum_subset hy
  intro i hi hni
  have hz : ρ i y = 0 := by
    simpa only [ρ.mem_finsupport,mem_support,not_not] using hni
  rw [hz,zero_smul]

omit [IsManifold I ∞ M] in

theorem smoothPartition_glues_zero_first_jet {S : Set M}
    (ρ : SmoothPartitionOfUnity ι I M S) {U : ι → Set M}
    (hρ : ρ.IsSubordinate U)
    {g : ι → M → ℝ} {β : (x : M) → TangentSpace I x →L[ℝ] ℝ}
    (hzero : ∀ i x, x ∈ S → x ∈ U i → g i x = 0)
    (hjet : ∀ i x, x ∈ S → x ∈ U i → HasMFDerivAt I 𝓘(ℝ,ℝ) (g i) x (β x))
    (x : M) (hx : x ∈ S) :
    (∑ᶠ i, ρ i x • g i x) = 0 ∧
    HasMFDerivAt I 𝓘(ℝ,ℝ) (fun y => ∑ᶠ i, ρ i y • g i y) x (β x) := by
  classical
  have hloc := smoothPartition_eventually_finite_sum ρ g x
  have hmem (i : ι) (hi : i ∈ ρ.fintsupport x) : x ∈ U i :=
    hρ i ((ρ.mem_fintsupport_iff x i).1 hi)
  constructor
  · rw [hloc.eq_of_nhds]
    apply Finset.sum_eq_zero
    intro i hi
    rw [hzero i x hx (hmem i hi),smul_zero]
  · have hd (i : ι) (hi : i ∈ ρ.fintsupport x) :
        HasMFDerivAt I 𝓘(ℝ,ℝ) (fun y => ρ i y • g i y) x (ρ i x • β x) := by
      have hp := ((ρ i).contMDiff.mdifferentiable (by simp) x).hasMFDerivAt
      refine (hp.mul (hjet i x hx (hmem i hi))).congr_mfderiv ?_
      let A : TangentSpace I x →L[ℝ] ℝ := mfderiv I 𝓘(ℝ,ℝ) (ρ i) x
      change ρ i x • β x + g i x • A = ρ i x • β x
      rw [hzero i x hx (hmem i hi), zero_smul, add_zero]
    have hsum := HasMFDerivAt.sum (I := I) (t := ρ.fintsupport x)
      (f := fun i y => ρ i y • g i y) (f' := fun i => ρ i x • β x) hd
    have hweights : (∑ i ∈ ρ.fintsupport x, ρ i x • β x) = β x := by
      rw [←Finset.sum_smul,ρ.sum_finsupport' x hx (ρ.finsupport_subset_fintsupport x),one_smul]
    rw [hweights] at hsum
    exact hsum.congr_of_eventuallyEq (by
      filter_upwards [hloc] with y hy
      simpa only [Finset.sum_apply] using hy)

variable [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]

theorem exists_smooth_zero_first_jet {S : Set M} (hS : IsClosed S)
    {U : ι → Set M} (hU : ∀ i, IsOpen (U i)) (hcover : S ⊆ ⋃ i, U i)
    {g : ι → M → ℝ} (hg : ∀ i, ContMDiffOn I 𝓘(ℝ,ℝ) ∞ (g i) (U i))
    {β : (x : M) → TangentSpace I x →L[ℝ] ℝ}
    (hzero : ∀ i x, x ∈ S → x ∈ U i → g i x = 0)
    (hjet : ∀ i x, x ∈ S → x ∈ U i → HasMFDerivAt I 𝓘(ℝ,ℝ) (g i) x (β x)) :
    ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ,ℝ) ∞ f ∧
      ∀ x ∈ S, f x = 0 ∧ HasMFDerivAt I 𝓘(ℝ,ℝ) f x (β x) := by
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I hS U hU hcover
  exact ⟨_,hρ.contMDiff_finsum_smul hU hg,
    fun x hx => smoothPartition_glues_zero_first_jet ρ hρ hzero hjet x hx⟩


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold IsManifold
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} {N : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]

def embeddedNormalJet (Ω : ℝ → ManifoldTwoForm E M) (α : ℝ → ManifoldOneForm E M)
    (e : N → M) (p : ℝ × M) : (ℝ × E) →L[ℝ] ℝ := by
  classical
  exact if h : ∃ b, e b = p.2 then
    (symplecticNormalJet (Ω p.1 p.2) (manifoldMapDifferential (E := E) (F := F) e h.choose) (α p.1 p.2)).comp
      (ContinuousLinearMap.snd ℝ ℝ E)
    else 0

omit [IsManifold 𝓘(ℝ,E) ∞ M] [IsManifold 𝓘(ℝ,F) ∞ N] in
theorem embeddedNormalJet_apply (Ω : ℝ → ManifoldTwoForm E M) (α : ℝ → ManifoldOneForm E M)
    {e : N → M} (he : Injective e) (t : ℝ) (b : N) :
    embeddedNormalJet (F := F) Ω α e (t,e b) =
      (symplecticNormalJet (Ω t (e b)) (manifoldMapDifferential (E := E) (F := F) e b) (α t (e b))).comp
        (ContinuousLinearMap.snd ℝ ℝ E) := by
  classical
  have hx : ∃ a, e a = (t,e b).2 := ⟨b,rfl⟩
  have hy : hx.choose = b := he hx.choose_spec
  simp only [embeddedNormalJet,dite_eq_left hx,hy]

variable [CompleteSpace F] [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]

omit [IsManifold 𝓘(ℝ,F) ∞ N] in

theorem exists_relative_global_potential
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M} {e : N → M}
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ,E) c).target))
    (he : IsSmoothEmbedding 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ e) (hclosed : IsClosed (range e))
    {T : Set ℝ} (hT : IsClosed T)
    (hi : ∀ t ∈ T, ∀ b, ((Ω t (e b)).bilinearComp (manifoldMapDifferential (E := E) (F := F) e b)
      (manifoldMapDifferential (E := E) (F := F) e b)).IsInvertible) :
    ∃ f : ℝ × M → ℝ, ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ f ∧
      ∀ t ∈ T, ∀ b, f (t,e b) = 0 ∧
        HasMFDerivAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) f (t,e b)
          ((symplecticNormalJet (Ω t (e b)) (manifoldMapDifferential (E := E) (F := F) e b) (α t (e b))).comp
            (ContinuousLinearMap.snd ℝ ℝ E)) := by
  classical
  choose U g hU hcover hg hjet using exists_relative_jet_patch hΩ hα he hi
  have hcov : (T ×ˢ range e) ⊆ ⋃ a, U a := by
    rintro ⟨t,x⟩ ⟨ht,b,rfl⟩
    exact mem_iUnion.mpr ⟨b,hcover b t ht⟩
  obtain ⟨f,hf,hfjet⟩ := exists_smooth_zero_first_jet (I := (𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E))
    (β := embeddedNormalJet (F := F) Ω α e) (hT.prod hclosed) hU hcov hg
    (by
      rintro a ⟨t,x⟩ ⟨ht,b,rfl⟩ hp
      exact (hjet a t ht b hp).1)
    (by
      rintro a ⟨t,x⟩ ⟨ht,b,rfl⟩ hp
      rw [embeddedNormalJet_apply Ω α he.isEmbedding.injective]
      exact (hjet a t ht b hp).2)
  refine ⟨f,hf,?_⟩
  intro t ht b
  have h := hfjet (t,e b) ⟨ht,mem_range_self b⟩
  rw [embeddedNormalJet_apply Ω α he.isEmbedding.injective] at h
  exact h


end

section
open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

def correctedOneForm (α : ℝ → ManifoldOneForm E M) (f : ℝ × M → ℝ)
    (t : ℝ) (x : M) : E →L[ℝ] ℝ :=
  α t x + manifoldSpatialDifferential f t x

theorem chartOneForm_corrected {α : ℝ → ManifoldOneForm E M} {f : ℝ × M → ℝ}
    (hf : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ f)
    {c : M} {p : ℝ × E} (hp : p.2 ∈ (extChartAt 𝓘(ℝ,E) c).target) :
    chartOneForm (correctedOneForm α f p.1) c p.2 =
      chartOneForm (α p.1) c p.2 + spatialDifferential (manifoldPotentialChart f c) p := by
  rw [←chartOneForm_manifoldSpatialDifferential hf hp]
  exact ContinuousLinearMap.add_comp _ _ _

theorem ManifoldMoserData.corrected {Ω : ℝ → ManifoldTwoForm E M}
    {α : ℝ → ManifoldOneForm E M} (h : ManifoldMoserData Ω α) {f : ℝ × M → ℝ}
    (hf : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ f) :
    ManifoldMoserData Ω (correctedOneForm α f) := by
  have he (c : M) (p : ℝ × E) (hp : p.2 ∈ (extChartAt 𝓘(ℝ,E) c).target) :
      (fun q : ℝ × E => chartOneForm (correctedOneForm α f q.1) c q.2) =ᶠ[𝓝 p]
        (fun q => chartOneForm (α q.1) c q.2 + spatialDifferential (manifoldPotentialChart f c) q) := by
    have ht := continuousAt_snd.preimage_mem_nhds
      ((isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c).mem_nhds hp)
    filter_upwards [ht] with q hq
    exact chartOneForm_corrected hf hq
  have hs (c : M) (p : ℝ × E) (hp : p.2 ∈ (extChartAt 𝓘(ℝ,E) c).target) :
      ContDiffAt ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2) p :=
    (h.smooth_one c).contDiffAt ((isOpen_univ.prod
      (isOpen_extChartAt_target (I := 𝓘(ℝ,E)) c)).mem_nhds ⟨mem_univ _,hp⟩)
  refine ⟨h.smooth_two,?_,h.nondegenerate,h.skew,h.closed,?_⟩
  · intro c p hp
    exact (((hs c p hp.2).add (spatialDifferential_contDiffAt
      (manifoldPotentialChart_contDiffAt hf hp.2))).congr_of_eventuallyEq
        (he c p hp.2)).contDiffWithinAt
  · intro t ht c y hy v w
    have hd := (he c (t,y) hy).fderiv_eq (𝕜 := ℝ)
    rw [hd]
    have ha := fderiv_add ((hs c (t,y) hy).differentiableAt (by simp))
      ((spatialDifferential_contDiffAt (manifoldPotentialChart_contDiffAt hf hy)).differentiableAt
        (by simp))
    change fderiv ℝ (fun q : ℝ × E => chartOneForm (α q.1) c q.2 +
      spatialDifferential (manifoldPotentialChart f c) q) (t,y) = _ at ha
    rw [ha]
    simp only [add_apply]
    have hz := spatialDifferential_closedAt (manifoldPotentialChart_contDiffAt hf (p := (t,y)) hy) v w
    have ho := h.exact_time t ht c y hy v w
    linarith


end

open scoped ContDiff Manifold Topology
open Set Function Manifold
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N]

omit [IsManifold 𝓘(ℝ,E) ∞ M] in

theorem manifoldSpatialDifferential_of_jet {f : ℝ × M → ℝ} {t : ℝ} {x : M}
    {β : E →L[ℝ] ℝ}
    (hf : HasMFDerivAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) f (t,x)
      (β.comp (ContinuousLinearMap.snd ℝ ℝ E))) :
    manifoldSpatialDifferential f t x = β := by
  have hc : HasMFDerivAt 𝓘(ℝ,E) ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E))
      (fun z : M => (t,z)) x (ContinuousLinearMap.inr ℝ ℝ E) := by
    convert! (hasMFDerivAt_const (I := 𝓘(ℝ,E)) (I' := 𝓘(ℝ,ℝ)) t x).prodMk
      (hasMFDerivAt_id (I := 𝓘(ℝ,E)) x) using 1
  have h := (hf.comp x hc).mfderiv
  change mfderiv 𝓘(ℝ,E) 𝓘(ℝ,ℝ) (f ∘ fun z => (t,z)) x = β
  rw [h]
  ext v
  rfl

theorem ManifoldMoserData.skew_intrinsic {Ω : ℝ → ManifoldTwoForm E M}
    {α : ℝ → ManifoldOneForm E M} (h : ManifoldMoserData Ω α)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (x : M) (u v : E) :
    Ω t x u v = -Ω t x v u := by
  have hx : x ∈ (extChartAt 𝓘(ℝ,E) x).source := mem_extChartAt_source x
  have hs := h.skew t ht x _ (mem_extChartAt_target x)
    (chartDifferential x x u) (chartDifferential x x v)
  have h1 := chartTwoForm_apply_chart (Ω := Ω t) hx u v
  have h2 := chartTwoForm_apply_chart (Ω := Ω t) hx v u
  exact h1.symm.trans (hs.trans (congrArg (fun r : ℝ => -r) h2))

theorem relative_moser_field_related {Ω : ℝ → ManifoldTwoForm E M}
    {α : ℝ → ManifoldOneForm E M} {e : N → M} {f : ℝ × M → ℝ}
    (h : ManifoldMoserData Ω α) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (b : N)
    (hi : (manifoldPullbackTwoForm (F := F) Ω e t b).IsInvertible)
    (hf : HasMFDerivAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) f (t,e b)
      ((symplecticNormalJet (Ω t (e b)) (manifoldMapDifferential (E := E) (F := F) e b)
        (α t (e b))).comp (ContinuousLinearMap.snd ℝ ℝ E))) :
    manifoldMapDifferential (E := E) (F := F) e b
      (manifoldMoserField (manifoldPullbackTwoForm (F := F) Ω e) (manifoldPullbackOneForm (F := F) α e) (t,b)) =
      manifoldMoserField Ω (correctedOneForm α f) (t,e b) := by
  dsimp only [manifoldMoserField,correctedOneForm]
  rw [manifoldSpatialDifferential_of_jet hf]
  exact (corrected_moser_vector_tangent (h.nondegenerate t ht (e b)) hi
    (h.skew_intrinsic ht (e b)) (α t (e b))).symm



end PackingSufficiencySupport.Hamiltonian
end

end OAI
