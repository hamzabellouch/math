import OAI.Geometry.SurfaceImmersion.Whitney.SmoothRegularZeroArc
import OAI.Geometry.SurfaceImmersion.Whitney.SurfaceDoublePairChart
import OAI.Geometry.SurfaceImmersion.Atlas.PairCurveChartDerivative

namespace OAI

/-! Actual transverse double points have smooth local paired curves,
with a regular and injective coordinate parametrization. -/
noncomputable section
open Set Filter Manifold Topology
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

theorem smooth_surface_double_arc {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (x y : M) (hxy : x ≠ y) (hval : f x = f y)
    (hreg : Function.Surjective (surfacePairDerivative f x y)) :
    ∃ (t₀ : ℝ) (T : Set ℝ) (A B : ℝ → M) (θ : ℝ → Base × Base),
      IsOpen T ∧ t₀ ∈ T ∧ A t₀ = x ∧ B t₀ = y ∧
      ContMDiffOn 𝓘(ℝ) planeModel ∞ A T ∧ ContMDiffOn 𝓘(ℝ) planeModel ∞ B T ∧
      ContDiff ℝ ∞ θ ∧ T.InjOn θ ∧
      ∀ t ∈ T, f (A t) = f (B t) ∧ A t ≠ B t ∧
        chart x (A t) = (θ t).1 ∧ chart y (B t) = (θ t).2 ∧
        Function.Injective (fderiv ℝ θ t) ∧
        Function.Injective ((mfderiv 𝓘(ℝ) planeModel A t).prod (mfderiv 𝓘(ℝ) planeModel B t)) := by
  obtain ⟨U,F,hU,hxU,hUs,hF,heF⟩ := surface_chart_representative hf x
  obtain ⟨V,G,hV,hyV,hVs,hG,heG⟩ := surface_chart_representative hf y
  let H : Base × Base → ProjectionTarget 3 := fun z => F z.1-G z.2
  have hH : ContDiff ℝ ∞ H := (hF.comp contDiff_fst).sub (hG.comp contDiff_snd)
  have hD : Function.Surjective (fderiv ℝ H (chart x x,chart y y)) :=
    (surface_pair_coordinate_regular_iff x y (hUs hxU) (hVs hyV) hF hG
      (heF.eventuallyEq_of_mem (hU.mem_nhds hxU))
      (heG.eventuallyEq_of_mem (hV.mem_nhds hyV))).mp hreg
  have hzero : H (chart x x,chart y y) = 0 := by
    change (F ∘ chart x) x-(G ∘ chart y) y = 0
    rw [← heF hxU,← heG hyV,hval,sub_self]
  obtain ⟨t₀,T₀,θ,hT₀,ht₀,hθ,hθ₀,hθall,hθinj⟩ :=
    smooth_regular_zero_arc hH (chart x x,chart y y) hzero hD
  let A : ℝ → M := fun t => (chart x).symm (θ t).1
  let B : ℝ → M := fun t => (chart y).symm (θ t).2
  let W : Set (Base × Base) := ((chart x) '' U) ×ˢ ((chart y) '' V)
  have hW : IsOpen W := ((chart x).isOpen_image_of_subset_source hU hUs).prod
    ((chart y).isOpen_image_of_subset_source hV hVs)
  let T := T₀ ∩ θ ⁻¹' W ∩ {t | A t ≠ B t}
  have hmapA : MapsTo (fun t => (θ t).1) (T₀ ∩ θ ⁻¹' W) (chart x).target := by
    rintro t ⟨_,ht⟩
    obtain ⟨z,hz,he⟩ := ht.1
    change (θ t).1 ∈ (chart x).target
    rw [← he]
    exact (chart x).map_source (hUs hz)
  have hmapB : MapsTo (fun t => (θ t).2) (T₀ ∩ θ ⁻¹' W) (chart y).target := by
    rintro t ⟨_,ht⟩
    obtain ⟨z,hz,he⟩ := ht.2
    change (θ t).2 ∈ (chart y).target
    rw [← he]
    exact (chart y).map_source (hVs hz)
  have hA : ContMDiffOn 𝓘(ℝ) planeModel ∞ A (T₀ ∩ θ ⁻¹' W) :=
    (chart_symm_smooth x).comp hθ.fst.contMDiff.contMDiffOn hmapA
  have hB : ContMDiffOn 𝓘(ℝ) planeModel ∞ B (T₀ ∩ θ ⁻¹' W) :=
    (chart_symm_smooth y).comp hθ.snd.contMDiff.contMDiffOn hmapB
  have hAx : A t₀ = x := by simp only [A,hθ₀]; exact (chart x).left_inv (hUs hxU)
  have hBy : B t₀ = y := by simp only [B,hθ₀]; exact (chart y).left_inv (hVs hyV)
  have hbase : IsOpen (T₀ ∩ θ ⁻¹' W) := hT₀.inter (hW.preimage hθ.continuous)
  have hT : IsOpen T :=
    (hA.continuousOn.prodMk hB.continuousOn).isOpen_inter_preimage hbase
      isClosed_diagonal.isOpen_compl
  have htT : t₀ ∈ T := by
    refine ⟨⟨ht₀,?_⟩,?_⟩
    · change θ t₀ ∈ W
      rw [hθ₀]
      exact ⟨⟨x,hxU,rfl⟩,⟨y,hyV,rfl⟩⟩
    · change A t₀ ≠ B t₀
      rw [hAx,hBy]
      exact hxy
  refine ⟨t₀,T,A,B,θ,hT,htT,hAx,hBy,hA.mono inter_subset_left,hB.mono inter_subset_left,
    hθ,hθinj.mono (inter_subset_left.trans inter_subset_left),?_⟩
  intro t ht
  have hcA : chart x (A t) = (θ t).1 := (chart x).right_inv (hmapA ht.1)
  have hcB : chart y (B t) = (θ t).2 := (chart y).right_inv (hmapB ht.1)
  obtain ⟨u,hu,heU⟩ := ht.1.2.1
  obtain ⟨v,hv,heV⟩ := ht.1.2.2
  have hAu : A t = u := by change (chart x).symm _ = _; rw [← heU,(chart x).left_inv (hUs hu)]
  have hBv : B t = v := by change (chart y).symm _ = _; rw [← heV,(chart y).left_inv (hVs hv)]
  refine ⟨?_,ht.2,hcA,hcB,(hθall t ht.1.1).2,?_⟩
  · have hz := (hθall t ht.1.1).1
    change F (θ t).1-G (θ t).2 = 0 at hz
    rw [heF (hAu ▸ hu),heG (hBv ▸ hv)]
    change F (chart x (A t)) = G (chart y (B t))
    rw [hcA,hcB]
    exact sub_eq_zero.mp hz
  · apply paired_curve_derivative_injective x y t
      (hA.contMDiffAt (hbase.mem_nhds ht.1)) (hB.contMDiffAt (hbase.mem_nhds ht.1))
      ((chart x).map_target (hmapA ht.1)) ((chart y).map_target (hmapB ht.1)) hθ.contDiffAt
    · filter_upwards [hT.mem_nhds ht] with s hs
      apply Prod.ext
      · exact ((chart x).right_inv (hmapA hs.1)).symm
      · exact ((chart y).right_inv (hmapB hs.1)).symm
    · exact (hθall t ht.1.1).2

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
