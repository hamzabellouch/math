import Mathlib
import OAI.Geometry.PrescribedPotential.PathLaplaceJets
import OAI.Geometry.PrescribedPotential.SchwartzFamilyBounds

namespace OAI

/-! Path Laplacian Sobolev. -/

section

noncomputable section
open Set Filter Topology
open scoped ContDiff SchwartzMap
namespace Anticanonical.SourceSmooth
open EllipticKernel GlobalElliptic SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X}

lemma path_laplacian_localized_bound (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A)
    (i : Fin A.count) (ρ : Smooth A)
    (hρ : tsupport (ρ : X → ℂ) ⊆ (A.euclideanChart i).source) (r : ℝ) :
    ∃ C : ℝ, ∀ s : PathSolution g h,
      ‖schwartzCoord r (localize A i ρ hρ (Smooth.ofReal (g.laplacian s.potential)))‖ ≤ C := by
  let K := (A.euclideanChart i) '' tsupport (ρ : X → ℂ)
  have hK : IsCompact K := (isClosed_tsupport (ρ : X → ℂ)).isCompact.image_of_continuousOn
    ((A.euclideanChart i).continuousOn.mono hρ)
  have hKU : K ⊆ (A.euclideanChart i).target := by
    rintro _ ⟨x,hx,rfl⟩
    exact (A.euclideanChart i).mapsTo (hρ hx)
  apply schwartzCoord_family_bound (fun s : PathSolution g h =>
    localize A i ρ hρ (Smooth.ofReal (g.laplacian s.potential))) hK
  · intro s
    exact closure_minimal (localizeFun_support A i ρ _) hK.isClosed
  · intro m
    obtain ⟨C,hC⟩ := path_laplacian_weighted_jets g h i ρ hK hKU m
    refine ⟨C,fun s x hx => ?_⟩
    have he : (localize A i ρ hρ (Smooth.ofReal (g.laplacian s.potential)) : EC d → ℂ)
        =ᶠ[𝓝 x] (fun y => ρ ((A.euclideanChart i).symm y)*
          Smooth.ofReal (g.laplacian s.potential) ((A.euclideanChart i).symm y)) := by
      filter_upwards [(A.euclideanChart i).open_target.mem_nhds (hKU hx)] with y hy
      exact localizeFun_apply A ρ _ hy
    rw [(he.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds]
    exact hC s x hx

lemma path_laplacian_sobolev_bound (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A)
    {ι : Type*} [Fintype ι] (D : Localizers A ι) (r : ℝ) :
    ∃ C : ℝ, ∀ s : PathSolution g h,
      ‖D.embed r (Smooth.ofReal (g.laplacian s.potential))‖ ≤ C := by
  choose C hC using fun i => path_laplacian_localized_bound g h (D.index i) (D.weight i) (D.support_sub i) r
  let B := ∑ i, max 0 (C i)
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => le_max_left _ _
  refine ⟨B,fun s => ?_⟩
  change ‖D.coordinates r (Smooth.ofReal (g.laplacian s.potential))‖ ≤ B
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro i
  exact (hC i s).trans ((le_max_right 0 (C i)).trans
    (Finset.single_le_sum (fun j _ => le_max_left 0 (C j)) (Finset.mem_univ i)))
end Anticanonical.SourceSmooth

end
end

end OAI
