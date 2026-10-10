import OAI.Geometry.SurfaceImmersion.Whitney.RegularPairedArcProjection
import OAI.Geometry.SurfaceImmersion.Whitney.OrderedArcEndpointUnique
import OAI.Geometry.SurfaceImmersion.Primitive.RegularCurveLoopRemoval

namespace OAI

/-! An actual ordered crosscap connection gives an embedded source path
made from finitely many regular smooth pieces, inside the original source image. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {f : M → ProjectionTarget 3} {p q : M}

theorem crosscap_source_embedded_path
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (cp : SurfaceCrosscapCoordinates f p) (cq : SurfaceCrosscapCoordinates f q)
    {Γ : I → M × M} (hΓ : Continuous Γ) (hi : Function.Injective Γ)
    (hzero : Γ 0 = (p,p)) (hone : Γ 1 = (q,q))
    (heq : ∀ u, f (Γ u).1 = f (Γ u).2)
    (hgood : ∀ u : I, 0 < (u:ℝ) → (u:ℝ) < 1 → (Γ u).1 ≠ (Γ u).2 ∧
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (Γ u).1) ∧
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (Γ u).2))
    (hsing : ∀ x, f x = f p → x = p) :
    ∃ P : Path p q, FiniteRegularPath planeModel P ∧ Function.Injective P ∧
      range P ⊆ Prod.fst '' range Γ := by
  obtain ⟨S,hSi,hS0,hS1,hr0,hr1⟩ := smooth_crosscap_connecting_arc_endpoint_regular hf hreg
    cp cq hΓ hi hzero hone heq (fun u h0 h1 => (hgood u h0 h1).1)
  let γ : ℝ → M := fun t => (S.curve t).1
  have hγ : ContMDiffOn 𝓘(ℝ) planeModel ∞ γ S.domain := contMDiff_fst.comp_contMDiffOn S.smooth
  let U : Set ℝ := {t | t ∈ S.domain ∧ Function.Injective (mfderiv 𝓘(ℝ) planeModel γ t)}
  have hU : IsOpen U := curve_regular_locus_open S.domain_open hγ
  have hclosed : Icc S.start S.finish ⊆ U := by
    intro t ht
    exact ⟨S.interval_subset ht,regular_paired_arc_projection hf hzero hone heq
      (fun u h0 h1 => (hgood u h0 h1).2) S hSi hS0 hS1 hr0 hr1 t ht⟩
  have hγ0 : γ S.start = p := congrArg Prod.fst hS0
  have hγ1 : γ S.finish = q := congrArg Prod.fst hS1
  have havoid : ∀ t ∈ Ioc S.start S.finish, γ t ≠ γ S.start := by
    intro t ht he
    obtain ⟨u,hu⟩ := hSi.subset ⟨t,⟨ht.1.le,ht.2⟩,rfl⟩
    have hup : (Γ u).1 = p := (congrArg Prod.fst hu).trans (he.trans hγ0)
    have hu0 := ordered_arc_source_start_unique hi hzero hone heq
      (fun u h0 h1 => (hgood u h0 h1).1) hsing u hup
    have heS : S.curve t = S.curve S.start := by rw [← hu,hu0,hzero,hS0]
    exact (ne_of_gt ht.1) (S.injective ⟨ht.1.le,ht.2⟩
      (left_mem_Icc.mpr S.start_lt_finish.le) heS)
  obtain ⟨P,hPp,hPi,hPr⟩ := regular_curve_loop_removal hU (hγ.mono (fun _ ht => ht.1))
    (fun _ ht => ht.2) S.start_lt_finish hclosed havoid
  let Q : Path p q := P.cast hγ0.symm hγ1.symm
  refine ⟨Q,hPp.cast _ _,hPi,hPr.trans ?_⟩
  rintro x ⟨t,ht,rfl⟩
  exact ⟨S.curve t,hSi.subset ⟨t,ht,rfl⟩,rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
