import OAI.Geometry.SurfaceImmersion.Atlas.GenericCoordinateLevels
import OAI.Geometry.SurfaceImmersion.Correction.CompactSmoothCutoffs
import OAI.Geometry.SurfaceImmersion.Correction.SmoothingAtlas

namespace OAI

/-! Generic levels of actual smooth functions on a closed surface. Finite
chart extensions reduce the selection to the proved Euclidean Sard input;
no coordinate extension or transversality premise is assumed. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PublishedInputs
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_generic_surface_levels (A : SmoothingAtlas M)
    (ρ : ι → M → ℝ) (hρ : ∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (ρ i))
    (U : Set (ι → ℝ)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ r ∈ U,
      (∀ i j, i ≠ j → {p : M | ρ i p = r i ∧ ρ j p = r j}.Finite) ∧
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k →
        ∀ p : M, ¬ (ρ i p = r i ∧ ρ j p = r j ∧ ρ k p = r k)) ∧
      (∀ i j, i ≠ j → ∀ p : M, ρ i p = r i → ρ j p = r j →
        ∃ q : M, p ∈ (chartAt Plane q).source ∧
          Function.Surjective (fderiv ℝ (fun y => radiusPairProjection i j
            (fun k => ρ k ((chartAt Plane q).symm y))) (chartAt Plane q p))) := by
  classical
  let K : A.centers → Set Plane := fun a => (chartAt Plane (a : M)) '' tsupport (A.weight a)
  have hsource (a : A.centers) : tsupport (A.weight a) ⊆ (chartAt Plane (a : M)).source := by
    simpa only [chart_source] using A.weight_support a
  have hK (a : A.centers) : IsCompact (K a) :=
    (isClosed_tsupport (A.weight a)).isCompact.image_of_continuousOn
      ((chartAt Plane (a : M)).continuousOn.mono (hsource a))
  have hKt (a : A.centers) : K a ⊆ (chartAt Plane (a : M)).target := by
    rintro x ⟨p,hp,rfl⟩
    exact (chartAt Plane (a : M)).map_source (hsource a hp)
  have hs (a : A.centers) (i : ι) : ContDiffOn ℝ ∞
      (fun y => ρ i ((chartAt Plane (a : M)).symm y)) (chartAt Plane (a : M)).target :=
    ((hρ i).comp_contMDiffOn (contMDiffOn_chart_symm (I := planeModel) (x := (a : M)))).contDiffOn
  choose W hW hKW hWt f hf he using fun a i =>
    CollarVelocity.compact_smooth_extension (hK a) (chartAt Plane (a : M)).open_target
      (hKt a) (hs a i)
  have hgerm (a : A.centers) (i : ι) {x : Plane} (hx : x ∈ K a) :
      f a i =ᶠ[𝓝 x] (fun y => ρ i ((chartAt Plane (a : M)).symm y)) := by
    filter_upwards [(hW a i).mem_nhds (hKW a i hx)] with y hy
    exact he a i hy
  obtain ⟨r,hr,hreg,hfinite,htriple⟩ := exists_generic_coordinate_levels f hf K hK U hU hne
  have hcover (p : M) : ∃ a : A.centers, p ∈ tsupport (A.weight a) := by
    by_contra hn
    push Not at hn
    have hz : ∀ a : A.centers, A.weight a p = 0 :=
      fun a => image_eq_zero_of_notMem_tsupport (hn a)
    have hh := A.partition p
    simp only [hz,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero] at hh
    exact zero_ne_one hh
  have heval (a : A.centers) {p : M} (hp : p ∈ tsupport (A.weight a)) (i : ι) :
      f a i (chartAt Plane (a : M) p) = ρ i p := by
    rw [he a i (hKW a i ⟨p,hp,rfl⟩)]
    change ρ i ((chartAt Plane (a : M)).symm (chartAt Plane (a : M) p)) = ρ i p
    rw [(chartAt Plane (a : M)).left_inv (hsource a hp)]
  refine ⟨r,hr,?_,?_,?_⟩
  · intro i j hij
    have hfin : (⋃ a : A.centers, (chartAt Plane (a : M)).symm ''
        (K a ∩ {x | f a i x = r i ∧ f a j x = r j})).Finite :=
      Set.finite_iUnion (fun a => (hfinite a i j hij).image _)
    apply hfin.subset
    intro p hp
    obtain ⟨a,ha⟩ := hcover p
    exact mem_iUnion.mpr ⟨a,⟨chartAt Plane (a : M) p,
      ⟨⟨p,ha,rfl⟩,by
        change f a i (chartAt Plane (a : M) p) = r i ∧ f a j (chartAt Plane (a : M) p) = r j
        rw [heval a ha i,heval a ha j]
        exact hp⟩,
      (chartAt Plane (a : M)).left_inv (hsource a ha)⟩⟩
  · intro i j k hij hik hjk p hp
    obtain ⟨a,ha⟩ := hcover p
    apply htriple a i j k hij hik hjk (chartAt Plane (a : M) p) ⟨p,ha,rfl⟩
    simpa only [heval a ha i,heval a ha j,heval a ha k] using hp
  · intro i j hij p hi hj
    obtain ⟨a,ha⟩ := hcover p
    let x : Plane := chartAt Plane (a : M) p
    have hx : x ∈ K a := ⟨p,ha,rfl⟩
    have hh := hreg a i j hij x hx
      ((heval a ha i).trans hi) ((heval a ha j).trans hj)
    have heq : (fun y => radiusPairProjection i j (fun k => f a k y)) =ᶠ[𝓝 x]
        (fun y => radiusPairProjection i j (fun k => ρ k ((chartAt Plane (a : M)).symm y))) := by
      have hevery : ∀ᶠ y in 𝓝 x, ∀ k, f a k y = ρ k ((chartAt Plane (a : M)).symm y) :=
        eventually_all.mpr (fun k => hgerm a k hx)
      filter_upwards [hevery] with y hy
      congr 1
      funext k
      exact hy k
    exact ⟨(a : M),hsource a ha,by rw [← heq.fderiv_eq]; exact hh⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
