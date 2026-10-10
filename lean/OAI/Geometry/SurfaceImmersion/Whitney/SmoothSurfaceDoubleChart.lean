import OAI.Geometry.SurfaceImmersion.Geometry.MatchedZeroLineData
import OAI.Geometry.SurfaceImmersion.Atlas.PairCurveChartDerivative
import OAI.Geometry.SurfaceImmersion.Whitney.SurfacePairLocalRegularization
import OAI.Geometry.SurfaceImmersion.Whitney.CompactDoublePairs

namespace OAI

/-! The real-line charts of the actual double locus have smooth regular inverses. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

theorem smooth_surface_double_pair_chart_data {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (x y : M) (hxy : x ≠ y) (heq : f x = f y)
    (hreg : Function.Surjective (surfacePairDerivative f x y)) :
    ∃ c : OpenPartialHomeomorph (surfaceDoublePairs f) ℝ,
      (⟨(x,y),hxy,heq⟩ : surfaceDoublePairs f) ∈ c.source ∧
      ContMDiffOn 𝓘(ℝ) planeModel ∞ (fun t => (c.symm t).val.1) c.target ∧
      ContMDiffOn 𝓘(ℝ) planeModel ∞ (fun t => (c.symm t).val.2) c.target ∧
      (∀ t ∈ c.target, Function.Injective
        ((mfderiv 𝓘(ℝ) planeModel (fun s => (c.symm s).val.1) t).prod
          (mfderiv 𝓘(ℝ) planeModel (fun s => (c.symm s).val.2) t))) ∧
      ∃ C : Base × Base → ℝ, ContDiff ℝ ∞ C ∧
        ∀ z ∈ c.source, z.val.1 ∈ (chart x).source ∧ z.val.2 ∈ (chart y).source ∧
          c z = C (chart x z.val.1,chart y z.val.2) := by
  obtain ⟨U,F,hU,hxU,hUs,hF,heF⟩ := surface_chart_representative hf x
  obtain ⟨V,G,hV,hyV,hVs,hG,heG⟩ := surface_chart_representative hf y
  let H : Base × Base → ProjectionTarget 3 := fun z => F z.1-G z.2
  have hH : ContDiff ℝ ∞ H := (hF.comp contDiff_fst).sub (hG.comp contDiff_snd)
  have hD : Function.Surjective (fderiv ℝ H (chart x x,chart y y)) :=
    (surface_pair_coordinate_regular_iff x y (hUs hxU) (hVs hyV) hF hG
      (heF.eventuallyEq_of_mem (hU.mem_nhds hxU))
      (heG.eventuallyEq_of_mem (hV.mem_nhds hyV))).mp hreg
  obtain ⟨b,hb,hbf,hbSmooth,hbInv⟩ := double_locus_submersion_chart hH (chart x x,chart y y) hD
  let R : Set (M × M) := (U ×ˢ V) ∩ {z | z.1 ≠ z.2}
  have hR : IsOpen R := (hU.prod hV).inter isClosed_diagonal.isOpen_compl
  let a := ((chart x).prod (chart y)).restrOpen R hR
  let e := a.trans b
  have hp : (x,y) ∈ e.source := by
    exact ⟨⟨⟨hUs hxU,hVs hyV⟩,⟨⟨hxU,hyV⟩,hxy⟩⟩,hb⟩
  have hmatch : ∀ z ∈ e.source, z ∈ surfaceDoublePairs f ↔ (e z).1 = 0 := by
    intro z hz
    have hsrc : z ∈ (U ×ˢ V) ∩ {z | z.1 ≠ z.2} := hz.1.2
    have hfirst : (e z).1 = f z.1-f z.2 := by
      change (b (chart x z.1,chart y z.2)).1 = _
      rw [hbf]
      change F (chart x z.1)-G (chart y z.2) = _
      change (F ∘ chart x) z.1-(G ∘ chart y) z.2 = _
      rw [← heF hsrc.1.1,← heG hsrc.1.2]
    rw [hfirst,sub_eq_zero]
    exact and_iff_right hsrc.2

  obtain ⟨c,hpc,hcs,hct,hcf,hci⟩ :=
    matched_zero_subset_line_chart_data e (surfaceDoublePairs f) (x,y) hp ⟨hxy,heq⟩ hmatch
  let θ : ℝ → Base × Base := fun t => b.symm (0,t)
  let A : ℝ → M := fun t => (chart x).symm (θ t).1
  let B : ℝ → M := fun t => (chart y).symm (θ t).2
  have htE (t : ℝ) (ht : t ∈ c.target) : (0,t) ∈ e.target := by
    rw [hct] at ht
    exact ht
  have htB (t : ℝ) (ht : t ∈ c.target) : (0,t) ∈ b.target := (htE t ht).1
  have htA (t : ℝ) (ht : t ∈ c.target) : θ t ∈ a.target := (htE t ht).2
  have hmapA : MapsTo (fun t => (θ t).1) c.target (chart x).target := by
    intro t ht
    exact (htA t ht).1.1
  have hmapB : MapsTo (fun t => (θ t).2) c.target (chart y).target := by
    intro t ht
    exact (htA t ht).1.2
  have hθ : ContDiffOn ℝ ∞ θ c.target :=
    hbInv.comp (contDiff_const.prodMk contDiff_id).contDiffOn htB
  have hA : ContMDiffOn 𝓘(ℝ) planeModel ∞ A c.target :=
    (chart_symm_smooth x).comp hθ.fst.contMDiffOn hmapA
  have hB : ContMDiffOn 𝓘(ℝ) planeModel ∞ B c.target :=
    (chart_symm_smooth y).comp hθ.snd.contMDiffOn hmapB
  have hAB (t : ℝ) (ht : t ∈ c.target) : (c.symm t).val = (A t,B t) := hci t ht
  have hAeq : EqOn (fun t => (c.symm t).val.1) A c.target :=
    fun t ht => congrArg Prod.fst (hAB t ht)
  have hBeq : EqOn (fun t => (c.symm t).val.2) B c.target :=
    fun t ht => congrArg Prod.snd (hAB t ht)
  refine ⟨c,hpc,hA.congr hAeq,hB.congr hBeq,?_⟩
  constructor
  · intro t ht
    have hEA : (fun s => (c.symm s).val.1) =ᶠ[𝓝 t] A :=
      hAeq.eventuallyEq_of_mem (c.open_target.mem_nhds ht)
    have hEB : (fun s => (c.symm s).val.2) =ᶠ[𝓝 t] B :=
      hBeq.eventuallyEq_of_mem (c.open_target.mem_nhds ht)
    rw [hEA.mfderiv_eq,hEB.mfderiv_eq]
    apply paired_curve_derivative_injective x y t
      (hA.contMDiffAt (c.open_target.mem_nhds ht))
      (hB.contMDiffAt (c.open_target.mem_nhds ht))
      ((chart x).map_target (hmapA ht)) ((chart y).map_target (hmapB ht))
      (hθ.contDiffAt (c.open_target.mem_nhds ht))
    · filter_upwards [c.open_target.mem_nhds ht] with s hs
      apply Prod.ext
      · exact ((chart x).right_inv (hmapA hs)).symm
      · exact ((chart y).right_inv (hmapB hs)).symm
    · let g : Base × Base → ℝ := fun z => (b z).2
      have hg : ContDiff ℝ ∞ g := hbSmooth.snd
      have heqθ : g ∘ θ =ᶠ[𝓝 t] id := by
        filter_upwards [c.open_target.mem_nhds ht] with s hs
        exact congrArg Prod.snd (b.right_inv (htB s hs))
      have hθt := hθ.differentiableOn (by simp) t ht
      have hd : (fderiv ℝ g (θ t)).comp (fderiv ℝ θ t) = ContinuousLinearMap.id ℝ ℝ := by
        rw [← fderiv_comp t (hg.differentiable (by simp) _)
          (hθt.differentiableAt (c.open_target.mem_nhds ht)),heqθ.fderiv_eq,fderiv_id]
      intro u v huv
      have hh := congrArg (fderiv ℝ g (θ t)) huv
      change ((fderiv ℝ g (θ t)).comp (fderiv ℝ θ t)) u =
        ((fderiv ℝ g (θ t)).comp (fderiv ℝ θ t)) v at hh
      simpa only [hd,ContinuousLinearMap.id_apply] using hh
  · refine ⟨(fun z => (b z).2),hbSmooth.snd,?_⟩
    intro z hz
    have hzs : z.val ∈ e.source := by rw [hcs] at hz; exact hz
    exact ⟨hzs.1.1.1,hzs.1.1.2,hcf z hz⟩

theorem smooth_surface_double_pair_chart {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (x y : M) (hxy : x ≠ y) (heq : f x = f y)
    (hreg : Function.Surjective (surfacePairDerivative f x y)) :
    ∃ c : OpenPartialHomeomorph (surfaceDoublePairs f) ℝ,
      (⟨(x,y),hxy,heq⟩ : surfaceDoublePairs f) ∈ c.source ∧
      ContMDiffOn 𝓘(ℝ) planeModel ∞ (fun t => (c.symm t).val.1) c.target ∧
      ContMDiffOn 𝓘(ℝ) planeModel ∞ (fun t => (c.symm t).val.2) c.target ∧
      ∀ t ∈ c.target, Function.Injective
        ((mfderiv 𝓘(ℝ) planeModel (fun s => (c.symm s).val.1) t).prod
          (mfderiv 𝓘(ℝ) planeModel (fun s => (c.symm s).val.2) t)) := by
  obtain ⟨c,hc,hA,hB,hpair,_⟩ := smooth_surface_double_pair_chart_data hf x y hxy heq hreg
  exact ⟨c,hc,hA,hB,hpair⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
