import OAI.Geometry.SurfaceImmersion.Whitney.CenteredCrosscapPreparation
import OAI.Geometry.SurfaceImmersion.Atlas.ChartGermImmersion

namespace OAI

/-! A supported preparation of one actual surface crosscap. The change
creates no singularities and retains the chosen singular point. -/
noncomputable section
open Set Filter Metric Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

theorem prepare_surface_crosscap {f : M → ProjectionTarget 3}
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (p q : M) (hp : p ∈ (chart q).source)
    (hbadp : ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p))
    {φ : Base → ProjectionTarget 3} (hφ : ContDiff ℝ ∞ φ)
    (heq : φ =ᶠ[𝓝 (chart q p)] f ∘ (chart q).symm) (b : Bool) (t : ℝ)
    (hz : surfaceDirection φ b (chart q p,t) = 0)
    (hreg : Function.Bijective (fderiv ℝ (surfaceDirection φ b) (chart q p,t)))
    {U : Set M} (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ g : M → ProjectionTarget 3, ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ g ∧
      tsupport (g-f) ⊆ U ∧
      {x | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g x)} ⊆
        {x | ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f x)} ∧
      (¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) g p)) ∧
      g =ᶠ[𝓝 p] (centeredSurfaceTaylor φ (chart q p)) ∘ chart q := by
  let a := chart q p
  obtain ⟨W,hWeq,hW,haW⟩ := _root_.mem_nhds_iff.mp heq
  let O := ((chart q).target ∩ (chart q).symm ⁻¹' U) ∩ W
  have hO : IsOpen O := ((chart q).isOpen_inter_preimage_symm hU).inter hW
  have haO : a ∈ O := by
    refine ⟨⟨(chart q).map_source hp,?_⟩,haW⟩
    change (chart q).symm (chart q p) ∈ U
    rwa [(chart q).left_inv hp]
  obtain ⟨ρ,hρ,hρO⟩ := nhds_basis_closedBall.mem_iff.mp (hO.mem_nhds haO)
  obtain ⟨r,G,hr,hrρ,hG,hGT,_hout,hGS,hGlocal⟩ :=
    centered_quadratic_crosscap_preparation hφ b a t hz hreg hρ
  have hSO : tsupport (G-φ) ⊆ O := by
    apply hGS.trans
    apply Subset.trans _ hρO
    apply closedBall_subset_closedBall
    linarith
  have hST : tsupport (G-φ) ⊆ (chart q).target := fun x hx => (hSO hx).1.1
  have hcompact : HasCompactSupport (G-φ) :=
    (isCompact_closedBall a (r/2)).of_isClosed_subset (isClosed_tsupport _) hGS
  obtain ⟨g,hg,hmodel,hext⟩ := chart_map_replacement q hf hG hφ hcompact hST hW
    (fun x hx => (hWeq hx).symm)
  let K := (chart q).symm '' tsupport (G-φ)
  have hK : IsCompact K := hcompact.image_of_continuousOn
    ((chart q).symm.continuousOn.mono hST)
  have hKS : tsupport (g-f) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    by_contra hn
    exact hx (sub_eq_zero.mpr ((hext x hn).self_of_nhds))
  have hKU : K ⊆ U := by
    rintro x ⟨y,hy,rfl⟩
    exact (hSO hy).1.2
  have hpmodel : g =ᶠ[𝓝 p] G ∘ chart q := hmodel p hp haW
  refine ⟨g,hg,hKS.trans hKU,?_,?_,?_⟩
  · intro x hbad
    by_cases hx : x ∈ K
    · obtain ⟨y,hy,rfl⟩ := hx
      have hyT := hST hy
      have hs := (chart q).map_target hyT
      have hyW : chart q ((chart q).symm y) ∈ W := by
        rw [(chart q).right_inv hyT]
        exact (hSO hy).2
      have hgm := hmodel _ hs hyW
      have hbadG : ¬ Function.Injective (fderiv ℝ G y) := by
        intro hi
        apply hbad
        apply (chart_germ_immersion_iff q hs hG hgm).mpr
        simpa only [(chart q).right_inv hyT] using hi
      have hyball : y ∈ ball a r := by
        have hyhalf := hGS hy
        have hd : dist y a ≤ r/2 := hyhalf
        rw [mem_ball]
        linarith
      have hya := (hGlocal y hyball).mp hbadG
      have hp' : (chart q).symm y = p := by rw [hya]; exact (chart q).left_inv hp
      change ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f ((chart q).symm y))
      exact (congrArg (fun w : M => ¬ Function.Injective
        (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f w)) hp').mpr hbadp
    · intro hgood
      exact hbad (by rw [(hext x hx).mfderiv_eq]; exact hgood)
  · intro hgood
    have hi := (chart_germ_immersion_iff q hp hG hpmodel).mp hgood
    exact ((hGlocal a (mem_ball_self hr)).mpr rfl) hi
  · exact hpmodel.trans (hGT.comp_tendsto ((chart q).continuousAt hp))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
