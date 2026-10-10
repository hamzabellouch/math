import OAI.Geometry.SurfaceImmersion.Whitney.SmoothCrosscapConnectingArc
import OAI.Geometry.SurfaceImmersion.Whitney.DoubleCurveVelocities

namespace OAI

/-! Interior regularity of both source sheets, together with the actual
endpoint germs, makes the first projection of the whole arc regular. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {f : M → ProjectionTarget 3} {p q : M}

theorem regular_paired_arc_projection
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    {Γ : I → M × M} (hzero : Γ 0 = (p,p)) (hone : Γ 1 = (q,q))
    (heq : ∀ u, f (Γ u).1 = f (Γ u).2)
    (hgood : ∀ u : I, 0 < (u:ℝ) → (u:ℝ) < 1 →
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (Γ u).1) ∧
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (Γ u).2))
    (S : SmoothCompactArc (planeModel.prod planeModel) (M × M))
    (hSi : S.curve '' Icc S.start S.finish = range Γ)
    (hS0 : S.curve S.start = (p,p)) (hS1 : S.curve S.finish = (q,q))
    (hr0 : Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun t => (S.curve t).1) S.start))
    (hr1 : Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun t => (S.curve t).1) S.finish)) :
    ∀ t ∈ Icc S.start S.finish,
      Function.Injective (mfderiv 𝓘(ℝ) planeModel (fun u => (S.curve u).1) t) := by
  intro t ht
  by_cases hts : t = S.start
  · subst t
    exact hr0
  by_cases htf : t = S.finish
  · subst t
    exact hr1
  have hto : t ∈ Ioo S.start S.finish :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm hts),lt_of_le_of_ne ht.2 htf⟩
  obtain ⟨u,hu⟩ := hSi.subset ⟨t,ht,rfl⟩
  have hu0 : u ≠ 0 := by
    intro he
    have hh : S.curve t = S.curve S.start := by rw [← hu,he,hzero,hS0]
    exact hts (S.injective ht (left_mem_Icc.mpr S.start_lt_finish.le) hh)
  have hu1 : u ≠ 1 := by
    intro he
    have hh : S.curve t = S.curve S.finish := by rw [← hu,he,hone,hS1]
    exact htf (S.injective ht (right_mem_Icc.mpr S.start_lt_finish.le) hh)
  have hureg := hgood u (lt_of_le_of_ne u.property.1 (fun he => hu0 (Subtype.ext he.symm)))
    (lt_of_le_of_ne u.property.2 (fun he => hu1 (Subtype.ext he)))
  have hSt := S.smooth.contMDiffAt (S.domain_open.mem_nhds (S.interval_subset ht))
  have hA := contMDiffAt_fst.comp t hSt
  have hB := contMDiffAt_snd.comp t hSt
  have he : (fun r => f (S.curve r).1) =ᶠ[𝓝 t] (fun r => f (S.curve r).2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hto] with r hr
    obtain ⟨v,hv⟩ := hSi.subset ⟨r,⟨hr.1.le,hr.2.le⟩,rfl⟩
    rw [← hv]
    exact heq v
  exact (regular_double_curve_velocities hf hA hB he (compact_pair_arc_regular S (S.interval_subset ht))
    (by dsimp only [Function.comp_apply]; rw [← hu]; exact hureg.1)
    (by dsimp only [Function.comp_apply]; rw [← hu]; exact hureg.2)).1

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
