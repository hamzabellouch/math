import OAI.Analysis.StrictMeans.MeasurableGeometry

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology

open Set Filter MeasureTheory Complex
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma countable_scalar_regular_fiber {f : ℝ → ℝ} {s : Set ℝ} {c : ℝ}
    (hs : ∀ x ∈ s, f x = c ∧ ∃ d : ℝ, HasDerivAt f d x ∧ d ≠ 0) : s.Countable := by
  have hd : DiscreteTopology s := discreteTopology_subtype_iff.mpr (by
    intro x hx
    obtain ⟨_,d,hder,hd⟩ := hs x hx
    have he : ∀ᶠ z in 𝓝[≠] x, f z ≠ c := hder.eventually_ne hd
    rw [Filter.inf_principal_eq_bot]
    exact he.mono (fun z hz hzs => hz (hs z hzs).1))
  have : Countable s := countable_of_Lindelof_of_discrete
  exact Set.countable_coe_iff.mp inferInstance

lemma plane_regular_slice_null {f : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (hf : ∀ p ∈ s, f p = 0 ∧
      ∃ d : ℝ, HasDerivAt (fun y => f (p.1,y)) d p.2 ∧ d ≠ 0) :
    volume s = 0 := by
  rw [Measure.volume_eq_prod]
  apply Measure.measure_prod_null_of_ae_null hs
  apply Filter.Eventually.of_forall
  intro x
  apply Set.Countable.measure_zero
  apply countable_scalar_regular_fiber (f := fun y => f (x,y)) (c := 0)
  intro y hy
  exact hf (x,y) hy

lemma plane_regular_slice_fst_null {f : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (hf : ∀ p ∈ s, f p = 0 ∧
      ∃ d : ℝ, HasDerivAt (fun x => f (x,p.2)) d p.1 ∧ d ≠ 0) :
    volume s = 0 := by
  have hh : volume (Prod.swap ⁻¹' s) = 0 := by
    apply plane_regular_slice_null (hs.preimage measurable_swap)
    intro p hp
    exact hf p.swap hp
  have hm := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))).measure_preimage hs.nullMeasurableSet
  rw [← Measure.volume_eq_prod] at hm
  exact hm ▸ hh

lemma measurableSet_zero_in_open {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [BorelSpace E] {f : E → ℝ} {U : Set E} (hU : IsOpen U) (hf : ContinuousOn f U) :
    MeasurableSet {x ∈ U | f x = 0} := by
  have ho := hf.isOpen_inter_preimage hU (isOpen_ne_fun continuous_id (continuous_const (y := (0:ℝ))))
  have he : {x ∈ U | f x = 0} = U \ (U ∩ f ⁻¹' {x : ℝ | x ≠ 0}) := by
    ext x
    simp only [mem_ofPred_eq, Set.mem_sdiff, mem_inter_iff, mem_preimage, not_and, not_not]
    tauto
  rw [he]
  exact hU.measurableSet.diff ho.measurableSet

lemma plane_regular_level_null {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) :
    volume {p ∈ U | f p = 0 ∧ fderiv ℝ f p ≠ 0} = 0 := by
  let S (v : ℝ × ℝ) : Set (ℝ × ℝ) := {p ∈ U | f p = 0 ∧ fderiv ℝ f p v ≠ 0}
  have hS (v : ℝ × ℝ) : MeasurableSet (S v) := by
    have hc := (hf.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply (continuousOn_const (c := v))
    have ho := hc.isOpen_inter_preimage hU (isOpen_ne_fun continuous_id (continuous_const (y := (0:ℝ))))
    exact (measurableSet_zero_in_open hU hf.continuousOn).inter ho.measurableSet |>.congr
      (by ext p; simp only [S, mem_inter_iff, mem_ofPred_eq, mem_preimage]; tauto)
  have hy : volume (S (0,1)) = 0 := by
    apply plane_regular_slice_null (hS (0,1))
    intro p hp
    refine ⟨hp.2.1, fderiv ℝ f p (0,1), ?_, hp.2.2⟩
    exact ((hf.differentiableOn one_ne_zero p hp.1).differentiableAt
      (hU.mem_nhds hp.1)).hasFDerivAt.comp_hasDerivAt p.2
        ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  have hx : volume (S (1,0)) = 0 := by
    apply plane_regular_slice_fst_null (hS (1,0))
    intro p hp
    refine ⟨hp.2.1, fderiv ℝ f p (1,0), ?_, hp.2.2⟩
    exact ((hf.differentiableOn one_ne_zero p hp.1).differentiableAt
      (hU.mem_nhds hp.1)).hasFDerivAt.comp_hasDerivAt p.1
        ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  apply measure_mono_null (t := S (1,0) ∪ S (0,1)) _ (measure_union_null hx hy)
  intro p hp
  by_cases h1 : fderiv ℝ f p (1,0) ≠ 0
  · exact Or.inl ⟨hp.1, hp.2.1, h1⟩
  · refine Or.inr ⟨hp.1, hp.2.1, ?_⟩
    intro h2
    apply hp.2.2
    apply ContinuousLinearMap.ext
    intro v
    have hv : v = v.1 • (1,0) + v.2 • (0,1) := by ext <;> simp
    simp only [ne_eq, not_not] at h1
    rw [hv, map_add, map_smul, map_smul, h1, h2]
    simp

lemma complex_regular_level_null {f : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) :
    volume {z ∈ U | f z = 0 ∧ fderiv ℝ f z ≠ 0} = 0 := by
  let e := Complex.equivRealProdCLM
  let g : ℝ × ℝ → ℝ := f ∘ e.symm
  have hV : IsOpen (e.symm ⁻¹' U) := hU.preimage e.symm.continuous
  have hg : ContDiffOn ℝ 1 g (e.symm ⁻¹' U) :=
    hf.comp e.symm.contDiff.contDiffOn (fun _ h => h)
  have he (p : ℝ × ℝ) (hp : e.symm p ∈ U) :
      fderiv ℝ g p ≠ 0 ↔ fderiv ℝ f (e.symm p) ≠ 0 := by
    have hdf := (hf.differentiableOn one_ne_zero (e.symm p) hp).differentiableAt (hU.mem_nhds hp)
    have hdg : fderiv ℝ g p = (fderiv ℝ f (e.symm p)).comp (e.symm : (ℝ × ℝ) →L[ℝ] ℂ) := by
      rw [show g = f ∘ e.symm from rfl, fderiv_comp p hdf e.symm.differentiableAt,
        e.symm.fderiv]
    rw [hdg]
    constructor
    · intro hn hh
      exact hn (by rw [hh]; apply ContinuousLinearMap.ext; intro v; simp)
    · intro hn hh
      apply hn
      apply ContinuousLinearMap.ext
      intro z
      have h := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (e z)) hh
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.symm_apply_apply, zero_apply] using h
  have hset : {p ∈ e.symm ⁻¹' U | g p = 0 ∧ fderiv ℝ g p ≠ 0} =
      e.symm ⁻¹' {z ∈ U | f z = 0 ∧ fderiv ℝ f z ≠ 0} := by
    ext p
    simp only [mem_ofPred_eq, mem_preimage, g, Function.comp_apply]
    by_cases hp : e.symm p ∈ U
    · rw [and_iff_right hp, and_iff_right hp, he p hp]
    · simp only [hp, false_and]
  have hz := plane_regular_level_null hV hg
  rw [hset] at hz
  have hmeas : MeasurableSet {z ∈ U | f z = 0 ∧ fderiv ℝ f z ≠ 0} := by
    have hd := (hf.continuousOn_fderiv_of_isOpen hU le_rfl).isOpen_inter_preimage hU
      (isOpen_ne_fun continuous_id (continuous_const (y := (0 : ℂ →L[ℝ] ℝ))))
    convert (measurableSet_zero_in_open hU hf.continuousOn).inter hd.measurableSet using 1
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage]
    tauto
  have hmp := Complex.volume_preserving_equiv_real_prod.symm
  exact hmp.measure_preimage hmeas.nullMeasurableSet ▸ hz

end
end StrictInverseFirstPower

open Set Filter MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma isOpen_regular_locus {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hG : ContDiffOn ℝ 1 G U) :
    IsOpen {z ∈ U | (fderiv ℝ G z).det ≠ 0} := by
  exact ((ContinuousLinearMap.continuous_det).comp_continuousOn
    (hG.continuousOn_fderiv_of_isOpen hU le_rfl)).isOpen_inter_preimage hU
      (isOpen_ne_fun continuous_id (continuous_const (y := (0:ℝ))))

lemma regular_inverse_chart {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hG : ContDiffOn ℝ 1 G U) {z : ℂ} (hz : z ∈ U) (hd : (fderiv ℝ G z).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, (e : ℂ → ℂ) = G ∧ z ∈ e.source ∧
      e.source ⊆ {w ∈ U | (fderiv ℝ G w).det ≠ 0} ∧ ContDiffOn ℝ 1 e.symm e.target := by
  let R := {w ∈ U | (fderiv ℝ G w).det ≠ 0}
  have hR : IsOpen R := isOpen_regular_locus hU hG
  have hcz : ContDiffAt ℝ 1 G z := hG.contDiffAt (hU.mem_nhds hz)
  let L := (fderiv ℝ G z).toContinuousLinearEquivOfDetNeZero hd
  have hdz : HasFDerivAt G (L : ℂ →L[ℝ] ℂ) z := by
    simpa only [L, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] using
      (hcz.differentiableAt one_ne_zero).hasFDerivAt
  let e0 := hcz.toOpenPartialHomeomorph G hdz one_ne_zero
  let e := e0.restr R
  have he : (e : ℂ → ℂ) = G := rfl
  have hs : e.source ⊆ R := by
    rw [show e = e0.restr R from rfl, e0.restr_source' R hR]
    exact inter_subset_right
  refine ⟨e, he, ?_, hs, ?_⟩
  · rw [show e = e0.restr R from rfl, e0.restr_source' R hR]
    exact ⟨hcz.mem_toOpenPartialHomeomorph_source hdz one_ne_zero, hz, hd⟩
  · intro ξ hξ
    have hp := hs (e.map_target hξ)
    have hc : ContDiffAt ℝ 1 G (e.symm ξ) := hG.contDiffAt (hU.mem_nhds hp.1)
    let A := (fderiv ℝ G (e.symm ξ)).toContinuousLinearEquivOfDetNeZero hp.2
    have hdf : HasFDerivAt e (A : ℂ →L[ℝ] ℂ) (e.symm ξ) := by
      rw [he]
      simpa only [A, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] using
        (hc.differentiableAt one_ne_zero).hasFDerivAt
    exact (e.contDiffAt_symm hξ hdf (he ▸ hc)).contDiffWithinAt

lemma countable_regular_inverse_charts {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hG : ContDiffOn ℝ 1 G U) :
    ∃ C : Set (OpenPartialHomeomorph ℂ ℂ), C.Countable ∧
      (∀ e ∈ C, (e : ℂ → ℂ) = G ∧
        e.source ⊆ {z ∈ U | (fderiv ℝ G z).det ≠ 0} ∧ ContDiffOn ℝ 1 e.symm e.target) ∧
      {z ∈ U | (fderiv ℝ G z).det ≠ 0} ⊆ ⋃ e ∈ C, e.source := by
  classical
  let R := {z ∈ U | (fderiv ℝ G z).det ≠ 0}
  have hex (z : R) := regular_inverse_chart hU hG z.property.1 z.property.2
  choose E hE hmem hsub hdiff using hex
  have hcover : R ⊆ ⋃ z : R, (E z).source := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z,hz⟩,hmem ⟨z,hz⟩⟩
  obtain ⟨c,hc,hcov⟩ := (HereditarilyLindelofSpace.isLindelof R).elim_countable_subcover
    (fun z : R => (E z).source) (fun z => (E z).open_source) hcover
  refine ⟨E '' c,hc.image E,?_,?_⟩
  · rintro e ⟨z,_,rfl⟩
    exact ⟨hE z,hsub z,hdiff z⟩
  · intro z hz
    obtain ⟨w,hw,hz'⟩ := mem_iUnion₂.mp (hcov hz)
    exact mem_iUnion₂.mpr ⟨E w,⟨w,hw,rfl⟩,hz'⟩

end
end StrictInverseFirstPower

end

end OAI
