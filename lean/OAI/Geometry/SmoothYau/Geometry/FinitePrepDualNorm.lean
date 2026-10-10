import Mathlib
import OAI.Geometry.SmoothYau.Estimates.PreparationWaveSecondGtOne
import OAI.Geometry.SmoothYau.Limits.OscDualNorm
import OAI.Geometry.SmoothYau.Smoothness.CompactDisjointSmoothCutoffs

namespace OAI

noncomputable section
open Set Filter Function Metric MeasureTheory
open scoped Topology ENNReal
namespace YauCounterexamples
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem finite_disjoint_profile_cores (μ : Measure E) [SFinite μ]
    {U : Set E} (hU : IsOpen U) (V : E → Set E) (hV : ∀ x ∈ U, V x ∈ 𝓝 x)
    {a : ℝ≥0∞} (ha : a < μ U) :
    ∃ (t : Finset E) (r : E → ℝ),
      (∀ x ∈ t, x ∈ U ∧ 0 < r x ∧ closedBall x (r x) ⊆ U ∩ V x) ∧
      (t : Set E).PairwiseDisjoint (fun x => closedBall x (r x)) ∧
      a < μ (⋃ x ∈ t, closedBall x (r x)) := by
  classical
  let f : E → Set ℝ := fun x => {r | closedBall x r ⊆ U ∩ V x}
  have hf : ∀ x ∈ U, ∀ δ > 0, (f x ∩ Ioo 0 δ).Nonempty := by
    intro x hx δ hδ
    have hn : U ∩ V x ∈ 𝓝 x := inter_mem (hU.mem_nhds hx) (hV x hx)
    obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp hn
    refine ⟨min r δ / 2, ⟨?_, by constructor <;> nlinarith [lt_min hr hδ, min_le_right r δ]⟩⟩
    exact (closedBall_subset_ball (by nlinarith [lt_min hr hδ, min_le_left r δ])).trans hrsub
  obtain ⟨s,r,hs,hsU,hr,hcover,hdisj⟩ :=
    Besicovitch.exists_disjoint_closedBall_covering_ae μ f U hf (fun _ => 1) (by intro x hx; norm_num)
  have hμ : μ (⋃ x ∈ s, closedBall x (r x)) = μ U := by
    apply le_antisymm (measure_mono ?_)
    · exact measure_mono_ae (ae_le_set.mpr hcover)
    · intro y hy
      obtain ⟨x,hx,hy⟩ := mem_iUnion₂.mp hy
      exact (hr x hx).1 hy |>.1
  let : Countable s := hs.to_subtype
  let A : Finset s → Set E := fun t => ⋃ x ∈ t, closedBall (x : E) (r x)
  have hmono : Monotone A := by
    intro t v htv y hy
    obtain ⟨x,hx,hy⟩ := mem_iUnion₂.mp hy
    exact mem_iUnion₂.mpr ⟨x,htv hx,hy⟩
  have hUnion : (⋃ t : Finset s, A t) = ⋃ x ∈ s, closedBall x (r x) := by
    ext y
    simp only [A, mem_iUnion]
    constructor
    · rintro ⟨t,x,hx,hy⟩
      exact ⟨x,x.property,hy⟩
    · rintro ⟨x,hx,hy⟩
      exact ⟨{⟨x,hx⟩},⟨x,hx⟩,Finset.mem_singleton_self _,hy⟩
  have hsup : a < ⨆ t : Finset s, μ (A t) := by
    rw [← hmono.measure_iUnion, hUnion, hμ]
    exact ha
  obtain ⟨t,ht⟩ := lt_iSup_iff.mp hsup
  refine ⟨t.image Subtype.val,r,?_,?_,?_⟩
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact ⟨hsU y.property,(hr y y.property).2.1,(hr y y.property).1⟩
  · intro x hx y hy hxy
    obtain ⟨x',hx',rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y',hy',rfl⟩ := Finset.mem_image.mp hy
    exact hdisj x'.property y'.property hxy
  · simpa [A] using ht
end YauCounterexamples

end

namespace YauCounterexamples
noncomputable section
open Set Filter Function Metric Manifold Bundle MeasureTheory
open scoped Topology ContDiff InnerProductSpace ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
local instance finitePrepDualNorm : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance finitePrepDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance finitePrepFormNorm : NormedAddCommGroup (CoordinateForm E) := inferInstance
local instance finitePrepFormSpace : NormedSpace ℝ (CoordinateForm E) := inferInstance

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma disjoint_supported_sum_eq_patch {ι : Type*} [Fintype ι]
    (u : E → ℝ) (χ f : ι → E → ℝ)
    (hd : Pairwise (Disjoint on fun i => tsupport (χ i)))
    (hf : ∀ i, tsupport (f i) ⊆ tsupport (χ i)) {i : ι} {x : E}
    (hx : x ∈ tsupport (χ i)) :
    (fun y => u y+∑ j, f j y) =ᶠ[𝓝 x] (fun y => u y+f i y) := by
  classical
  have hz : ∀ j, ∀ᶠ y in 𝓝 x, j ≠ i → f j y = 0 := by
    intro j
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall (fun _ hh => (hh hji).elim)
    · exact (notMem_tsupport_iff_eventuallyEq.mp
        (fun hh => (hd hji).notMem_of_mem_right hx (hf j hh))).mono (fun _ hh _ => hh)
  filter_upwards [Filter.eventually_all.mpr hz] with y hy
  rw [Finset.sum_eq_single i (fun j _ hji => hy j hji) (by simp)]

theorem actual_metric_preparation (hdim : Module.finrank ℝ E = 3)
    (g : SmoothMetric E E) {u : E → ℝ} (hu : ContDiff ℝ ∞ u)
    {Ω : Set E} (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (ha : ∀ x ∈ closure Ω, coordinateMetricGradient g u x ≠ 0)
    (hstrict : ∀ x ∈ closure Ω, actualProfileStrict g u x)
    (μ : Measure E) [IsFiniteMeasure μ] {ε εp : ℝ} (hε : 0 < ε) (hεp : 0 < εp) :
    ∃ (v : E → ℝ) (U : Set E), ContDiff ℝ ∞ v ∧
      HasCompactSupport (fun x => v x-u x) ∧ tsupport (fun x => v x-u x) ⊆ Ω ∧
      (∀ x, |v x-u x| < ε ∧ ‖fderiv ℝ v x-fderiv ℝ u x‖ < ε) ∧
      (∀ x ∈ closure Ω, coordinateMetricGradient g v x ≠ 0 ∧ actualProfileStrict g v x ∧
        actualCoordinateNorm g x (coordinateMetricGradient g v x-coordinateMetricGradient g u x) ≤
          εp*actualProfileSpeed g u x) ∧
      IsOpen U ∧ U ⊆ Ω ∧ (∀ x ∈ U, actualProfileFull g v x) ∧ μ Ω/6 ≤ μ U := by
  classical
  by_cases hzero : μ Ω = 0
  · refine ⟨u,∅,hu,?_,?_,?_,?_,isOpen_empty,empty_subset _,?_,?_⟩
    · dsimp [HasCompactSupport]; simp
    · simp
    · intro x; simpa using And.intro hε hε
    · intro x hx
      refine ⟨ha x hx,hstrict x hx,?_⟩
      simp only [sub_self,actualCoordinateNorm,map_zero,Real.sqrt_zero]
      exact mul_nonneg hεp.le (actualCoordinateNorm_nonneg g _ _)
    · simp
    · simp [hzero]
  have hhalf : μ Ω/2 < μ Ω := by
    have hh := ENNReal.mul_lt_mul_left hzero (measure_ne_top μ Ω)
      (by norm_num : (1/2 : ℝ≥0∞) < 1)
    simpa only [one_mul,div_eq_mul_inv,one_mul,mul_comm] using hh
  have hloc : ∀ p : E, ∃ (W : Set E) (s : E → ℝ) (C : ℝ), IsOpen W ∧
      (p ∈ Ω → p ∈ W ∧ ContDiff ℝ ∞ s ∧ 0 < C ∧ ∀ x ∈ W,
        fderiv ℝ s x ≠ 0 ∧ fderiv ℝ s x (coordinateMetricGradient g u x) = 0 ∧
        ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x) ≠ 0) ∧
        (∀ c ∈ Icc (-2*C) (2*C), quadraticPlaneStrict
          (metricProfileTraceForm (selfMetricFlat g x)
            (actualCoordinateHessian g u x+c • profileRankOne (fderiv ℝ s x))
            (coordinateMetricGradient g u x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x))) ∧
        (∀ c ∈ Icc C (2*C), quadraticPlaneFull
          (metricProfileTraceForm (selfMetricFlat g x)
            (actualCoordinateHessian g u x+c • profileRankOne (fderiv ℝ s x))
            (coordinateMetricGradient g u x)) ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)))) := by
    intro p
    by_cases hp : p ∈ Ω
    · obtain ⟨W,s,C,hWo,hWp,hs,hC,hdata⟩ := exists_actual_preparation_neighborhood hdim g hu
        (ha p (subset_closure hp)) (hstrict p (subset_closure hp))
      exact ⟨W,s,C,hWo,fun _ => ⟨hWp,hs,hC,hdata⟩⟩
    · exact ⟨∅,0,1,isOpen_empty,fun h => (hp h).elim⟩
  choose W s C hWo hW using hloc
  obtain ⟨t,r,ht,htd,htm⟩ := finite_disjoint_profile_cores μ hΩ W
    (fun p hp => (hWo p).mem_nhds (hW p hp).1) hhalf
  let ι := {p // p ∈ t}
  let K : ι → Set E := fun i => closedBall i.val (r i.val)
  have hK : ∀ i, IsCompact (K i) := fun _ => isCompact_closedBall _ _
  have hKd : Pairwise (Disjoint on K) := by
    intro i j hij
    exact htd i.property j.property (fun he => hij (Subtype.ext he))
  obtain ⟨χ,hχ,hχd⟩ := compact_disjoint_smooth_cutoffs K (fun i => Ω ∩ W i.val) hK hKd
    (fun i => hΩ.inter (hWo i.val)) (fun i => (ht i.val i.property).2.2)
  have hχ1 : ∀ i, ∀ x ∈ K i, χ i x = 1 := fun i x hx =>
    (eventually_nhdsSet_iff_forall.mp (hχ i).2.2.2.1 x hx).self_of_nhds
  have hKχ : ∀ i, K i ⊆ tsupport (χ i) := by
    intro i x hx
    apply subset_tsupport
    simp only [Function.mem_support,hχ1 i x hx,ne_eq,one_ne_zero,not_false_eq_true]
  obtain ⟨δ,hδ,hrel⟩ := compact_relative_gradient_tolerance g hu hΩc ha hεp
  have hpdata : ∀ i : ι, ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ τ : ℝ,
      ∀ x ∈ tsupport (χ i),
      let v := preparationCorrugation u (χ i) preparationWave (s i.val) (C i.val) N τ
      coordinateMetricGradient g v x ≠ 0 ∧ actualProfileStrict g v x ∧
      (χ i x = 1 → 1 < preparationWaveSecond (N*s i.val x+τ) → actualProfileFull g v x) ∧
      |v x-u x| < min ε δ ∧ ‖fderiv ℝ v x-fderiv ℝ u x‖ < min ε δ := by
    intro i
    have hi := hW i.val (ht i.val i.property).1
    apply actual_preparation_on_compact_patch g hu (hχ i).1 hi.2.1 (hχ i).2.1
      (C i.val) hi.2.2.1 (fun x _ => (hχ i).2.2.2.2 x)
    · exact fun x hx => (hi.2.2.2 x ((hχ i).2.2.1 hx).2).2.2.1
    · exact fun x hx => (hi.2.2.2 x ((hχ i).2.2.1 hx).2).2.2.2.1
    · exact fun x hx => (hi.2.2.2 x ((hχ i).2.2.1 hx).2).2.2.2.2
    · exact lt_min hε hδ
  choose N₀ hN₀ hdata using hpdata
  let N : ℝ := max 1 (∑ i, |N₀ i|)
  have hN : ∀ i, N₀ i ≤ N := by
    intro i
    exact (le_abs_self _).trans ((Finset.single_le_sum (fun j _ => abs_nonneg (N₀ j))
      (Finset.mem_univ i)).trans (le_max_right _ _))
  let S : Set E := ⋃ i, K i
  have hSm : MeasurableSet S := MeasurableSet.iUnion fun i => (hK i).measurableSet
  have hSO : S ⊆ Ω := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    exact ((ht i.val i.property).2.2 hi).1
  have hMS : μ Ω/2 ≤ μ S := by
    apply le_of_lt
    convert htm using 1
    congr 1
    ext x
    simp only [S,K,ι,mem_iUnion,Subtype.exists,exists_prop]
  let sg : E → ℝ := fun x => ∑ i, (K i).indicator (s i.val) x
  have hsg : Measurable sg := Finset.measurable_sum _ (fun i _ =>
    ((hW i.val (ht i.val i.property).1).2.1.continuous.measurable).indicator (hK i).measurableSet)
  have hsgi : ∀ i, ∀ x ∈ K i, sg x = s i.val x := by
    intro i x hx
    dsimp only [sg]
    rw [Finset.sum_eq_single i]
    · exact indicator_of_mem hx _
    · intro j _ hji
      exact indicator_of_notMem ((hKd hji).notMem_of_mem_right hx) _
    · simp
  obtain ⟨τ,hτ⟩ := exists_preparation_phase (μ.restrict S) sg hsg N
  let w : ι → E → ℝ := fun i => preparationCorrugation u (χ i) preparationWave (s i.val) (C i.val) N τ
  let f : ι → E → ℝ := fun i x => w i x-u x
  let v : E → ℝ := fun x => u x+∑ i, f i x
  have hw : ∀ i, ContDiff ℝ ∞ (w i) := fun i => preparationCorrugation_smooth hu (hχ i).1
    preparationWave_smooth (hW i.val (ht i.val i.property).1).2.1 _ _ _
  have hv : ContDiff ℝ ∞ v := hu.add (ContDiff.sum (fun i _ => (hw i).sub hu))
  have hfs : ∀ i, tsupport (f i) ⊆ tsupport (χ i) := fun i => preparationCorrugation_tsupport ..
  have hfd : Pairwise (Disjoint on fun i => tsupport (f i)) := fun i j hij =>
    (hχd hij).mono (hfs i) (hfs j)
  have heq : ∀ i, ∀ x ∈ tsupport (χ i), v =ᶠ[𝓝 x] w i := by
    intro i x hx
    simpa only [f,add_sub_cancel] using disjoint_supported_sum_eq_patch u χ f hχd hfs hx
  have hcases (x : E) : (v =ᶠ[𝓝 x] u) ∨ ∃ i, x ∈ tsupport (χ i) ∧ v =ᶠ[𝓝 x] w i := by
    rcases disjoint_sum_eventuallyEq u f hfd x with h|⟨i,hi,hei⟩
    · exact Or.inl h
    · exact Or.inr ⟨i,hfs i hi,heq i x (hfs i hi)⟩
  have hvs : tsupport (fun x => v x-u x) ⊆ ⋃ i, tsupport (χ i) := by
    apply closure_minimal _ (isClosed_iUnion_of_finite fun i => isClosed_tsupport _)
    intro x hx
    by_contra hh
    have hz : ∀ i, χ i x = 0 := fun i => image_eq_zero_of_notMem_tsupport
      (fun hi => hh (mem_iUnion_of_mem i hi))
    have hvx : v x = u x := by simp [v,f,w,preparationCorrugation,hz]
    exact hx (sub_eq_zero.mpr hvx)
  have hc : HasCompactSupport (fun x => v x-u x) :=
    (isCompact_iUnion fun i => (hχ i).2.1).of_isClosed_subset (isClosed_tsupport _) hvs
  have hsub : tsupport (fun x => v x-u x) ⊆ Ω := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hvs hx)
    exact ((hχ i).2.2.1 hi).1
  have heps : ∀ x, |v x-u x| < ε ∧ ‖fderiv ℝ v x-fderiv ℝ u x‖ < ε := by
    intro x
    rcases hcases x with hh|⟨i,hi,hei⟩
    · simp only [hh.self_of_nhds,hh.fderiv_eq (𝕜:=ℝ),sub_self,abs_zero,norm_zero]
      exact ⟨hε,hε⟩
    · have hp := hdata i N (hN i) τ x hi
      rw [hei.self_of_nhds,hei.fderiv_eq (𝕜:=ℝ)]
      exact ⟨hp.2.2.2.1.trans_le (min_le_left _ _),hp.2.2.2.2.trans_le (min_le_left _ _)⟩
  have hglobal : ∀ x ∈ closure Ω, coordinateMetricGradient g v x ≠ 0 ∧ actualProfileStrict g v x ∧
      actualCoordinateNorm g x (coordinateMetricGradient g v x-coordinateMetricGradient g u x) ≤
        εp*actualProfileSpeed g u x := by
    intro x hx
    rcases hcases x with hh|⟨i,hi,hei⟩
    · obtain ⟨hg,hH,hS,hF⟩ := actualJet_eventuallyEq g hh
      refine ⟨hg ▸ ha x hx,hS.mpr (hstrict x hx),?_⟩
      simp only [hg,sub_self,actualCoordinateNorm,map_zero,Real.sqrt_zero]
      exact mul_nonneg hεp.le (actualCoordinateNorm_nonneg g _ _)
    · have hp := hdata i N (hN i) τ x hi
      obtain ⟨hg,hH,hS,hF⟩ := actualJet_eventuallyEq g hei
      refine ⟨hg ▸ hp.1,hS.mpr hp.2.1,?_⟩
      exact (hrel v x hx (by
        rw [hei.fderiv_eq (𝕜:=ℝ)]
        exact hp.2.2.2.2.trans_le (min_le_right _ _))).le
  let U : Set E := Ω ∩ {x | metricJetFull g (x,actualCoordinateHessian g v x,fderiv ℝ v x)}
  have hU : IsOpen U := hΩ.inter ((isOpen_metricJetFull g).preimage
    (continuous_id.prodMk ((continuous_coordinateCovariantSecond _
      (contDiff_metricChristoffel g).continuous hv).prodMk (hv.continuous_fderiv (by simp)))))
  have hUF : ∀ x ∈ U, actualProfileFull g v x := fun x hx =>
    ((metricJetFull_actual g v x).mp hx.2).2
  have hgood : {x | 1 < preparationWaveSecond (N*sg x+τ)} ∩ S ⊆ U := by
    intro x hx
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx.2
    have hix := hKχ i hi
    have hp := hdata i N (hN i) τ x hix
    have hh := hp.2.2.1 (hχ1 i x hi) (by simpa only [mem_ofPred_eq,hsgi i x hi] using hx.1)
    have he := actualJet_eventuallyEq g (heq i x hix)
    exact ⟨hSO hx.2,(metricJetFull_actual g v x).mpr ⟨(hglobal x (subset_closure (hSO hx.2))).1,
      he.2.2.2.mpr hh⟩⟩
  refine ⟨v,U,hv,hc,hsub,heps,hglobal,hU,inter_subset_left,hUF,?_⟩
  have hmeas : MeasurableSet {x | 1 < preparationWaveSecond (N*sg x+τ)} :=
    measurableSet_lt measurable_const (preparationWaveSecond_smooth.continuous.measurable.comp
      ((measurable_const.mul hsg).add measurable_const))
  rw [Measure.restrict_apply_univ,Measure.restrict_apply hmeas] at hτ
  calc
    μ Ω/6 = μ Ω/2*(1/3 : ℝ≥0∞) := by
      simp only [div_eq_mul_inv,mul_assoc,one_mul]
      congr 1
      rw [← ENNReal.mul_inv (by norm_num : (2 : ℝ≥0∞) ≠ 0 ∨ (3 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞))
        (by norm_num : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) ∨ (3 : ℝ≥0∞) ≠ 0)]
      norm_num
    _ ≤ μ S*(1/3 : ℝ≥0∞) := by gcongr
    _ ≤ μ ({x | 1 < preparationWaveSecond (N*sg x+τ)} ∩ S) := hτ
    _ ≤ μ U := measure_mono hgood
end
end YauCounterexamples

end OAI
