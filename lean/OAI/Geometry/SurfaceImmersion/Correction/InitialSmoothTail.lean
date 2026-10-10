import OAI.Geometry.SurfaceImmersion.Whitney.EndpointRegularArcs
import OAI.Geometry.SurfaceImmersion.Geometry.OriginalRegularSegment
import OAI.Geometry.SurfaceImmersion.Whitney.SmoothArcTail

namespace OAI

/-! Start the finite smooth assembly at the original source endpoint,
retaining its actual regular germ and an exact unchanged initial trace. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {p q : M} {γ : Path p q}

theorem initial_smooth_tail (hγ : FiniteRegularPath planeModel γ) (hi : Function.Injective γ)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ (r : ℝ) (P : SmoothArcTail γ.extend r), 0 < r ∧ r < η ∧
      P.arc.curve P.arc.start = p ∧
      P.arc.curve '' Icc P.arc.start P.arc.finish = γ.extend '' Icc 0 r := by
  obtain ⟨A,r,hr,hrη,hAs,hAf,hmatch,hsource,hgerm⟩ := first_regular_arc hγ hi hη hη1
  have hf : 0 < deriv (id : ℝ → ℝ) A.finish := by simp
  let P : SmoothArcTail γ.extend r := ⟨A,id,contDiff_id,hf,hAf,hgerm⟩
  refine ⟨r,P,hr,hrη,hsource,?_⟩
  change A.curve '' Icc A.start A.finish = _
  rw [hAs,hAf]
  exact Set.EqOn.image_eq (fun u hu => hmatch u hu)

theorem initial_smooth_tail_until (hγ : FiniteRegularPath planeModel γ)
    (hi : Function.Injective γ) {d D : ℝ} (hd : 0 < d) (hdD : d < D) (hD : D ≤ 1)
    (hreg : ∀ t ∈ Ioo (0:ℝ) D, ContMDiffAt 𝓘(ℝ) planeModel ∞ γ.extend t ∧
      Function.Injective (mfderiv 𝓘(ℝ) planeModel γ.extend t)) :
    ∃ P : SmoothArcTail γ.extend d, P.arc.curve P.arc.start = p ∧
      P.arc.curve '' Icc P.arc.start P.arc.finish = γ.extend '' Icc 0 d := by
  obtain ⟨r,P,hr,hrd,hPsource,hPimage⟩ := initial_smooth_tail hγ hi hd (hdD.le.trans hD)
  obtain ⟨Q,hQs,hQf,hQc⟩ := original_regular_segment hi isOpen_Ioo
    (fun _ ht => ⟨ht.1,ht.2.trans_le hD⟩) hreg hrd
    (fun u hu => ⟨hr.trans_le hu.1,hu.2.trans_lt hdD⟩)
  have hcross : ∀ s ∈ Icc P.arc.start P.arc.finish, ∀ t ∈ Ioc Q.start Q.finish,
      P.arc.curve s ≠ Q.curve t := by
    intro s hs t ht he
    obtain ⟨u,hu,huP⟩ := hPimage.subset (mem_image_of_mem P.arc.curve hs)
    rw [hQs,hQf] at ht
    rw [hQc] at he
    have hue : u = t := embeddedPath_extend_injOn γ hi
      ⟨hu.1,hu.2.trans (hrd.le.trans (hdD.le.trans hD))⟩
      ⟨hr.le.trans ht.1.le,ht.2.trans (hdD.le.trans hD)⟩ (huP.trans he)
    exact (not_le_of_gt ht.1) (hue ▸ hu.2)
  have hleft : Q.curve =ᶠ[𝓝 Q.start] γ.extend ∘ id := by rw [hQc]; rfl
  have hright : Q.curve =ᶠ[𝓝 Q.finish] γ.extend ∘ id := by rw [hQc]; rfl
  obtain ⟨R,hRimage,hRsource,_⟩ := P.append Q id id contDiff_id contDiff_id
    (by simp) (by simp) hQs hQf hleft hright hcross
  refine ⟨R,hRsource.trans hPsource,?_⟩
  rw [hRimage,hPimage,hQc,hQs,hQf,← image_union,Icc_union_Icc_eq_Icc hr.le hrd.le]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
