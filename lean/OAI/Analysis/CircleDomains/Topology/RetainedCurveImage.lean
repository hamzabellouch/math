import OAI.Analysis.CircleDomains.Topology.RetainedJordanSides
import OAI.Analysis.CircleDomains.Topology.ImageCoreJordan
import OAI.Analysis.CircleDomains.Rigidity.MatchedEndChains

namespace OAI

/-! Schoenflies and open-map side correspondence for one retained
source curve. The curve may surround missing source points. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem exists_retained_curve_image (hsch : PlanarSchoenflies)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsPreconnected G)
    (hinf : OnePoint.infty ∈ G) {f : Sphere → Sphere}
    (hf : ContinuousOn f G) (ho : ∀ U, IsOpen U → U ⊆ G → IsOpen (f '' U))
    (hi : InjOn f G) (hfix : f OnePoint.infty = OnePoint.infty)
    (H : ℂ ≃ₜ ℂ) (γ : Circle → ℂ) (hγ : Continuous γ) (hγi : Injective γ)
    (hfront : range γ = frontier (jordanInterior H))
    (hγG : ∀ t, (γ t : Sphere) ∈ G) :
    ∃ J : ℂ ≃ₜ ℂ,
      Continuous (fun t => finiteCoord (f (γ t : Sphere))) ∧
      range (fun t => finiteCoord (f (γ t : Sphere))) = frontier (jordanInterior J) ∧
      f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) ∧
      f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) =
        f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior J) := by
  have hfinite (t : Circle) : f (γ t : Sphere) ≠ OnePoint.infty :=
    finite_image_of_fixes_infty hi hinf hfix (hγG t)
  let δ := fun t => finiteCoord (f (γ t : Sphere))
  have hδc (t : Circle) : (δ t : Sphere) = f (γ t : Sphere) :=
    CannonMobius.coe_coordinate (hfinite t)
  have hδ : Continuous δ := by
    apply OnePoint.isOpenEmbedding_coe.isInducing.continuous_iff.mpr
    have he : ((↑) : ℂ → Sphere) ∘ δ = f ∘ ((↑) : ℂ → Sphere) ∘ γ := funext hδc
    rw [he]
    exact hf.comp_continuous (OnePoint.continuous_coe.comp hγ) hγG
  have hδi : Injective δ := by
    intro s t hst
    apply hγi
    apply OnePoint.coe_injective
    exact hi (hγG s) (hγG t)
      ((hδc s).symm.trans ((congrArg ((↑) : ℂ → Sphere) hst).trans (hδc t)))
  obtain ⟨J,hJ⟩ := hsch δ hδ hδi
  have hJfront : range δ = frontier (jordanInterior J) :=
    (frontier_jordanInterior_eq_circle_range J δ hJ).symm
  have hb : f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior J) := by
    rw [← hfront,← hJfront,image_image,← range_comp,← range_comp]
    congr 1
    funext t
    exact (hδc t).symm
  refine ⟨J,hδ,hJfront,hb,?_⟩
  apply open_image_retained_jordan_side_eq hG hconn hinf H J ?_ hf ho hi hfix hb
  rintro _ ⟨z,hz,rfl⟩
  obtain ⟨t,rfl⟩ := hfront.symm ▸ hz
  exact hγG t

 theorem matched_end_subset_retained_side
    {G : Set Sphere} {f : Sphere → Sphere} (hi : InjOn f G)
    (H J : ℂ ≃ₜ ℂ) (Hn Jn : ℕ → ℂ ≃ₜ ℂ)
    (hnest : Antitone (fun n => closedTerminalCap (Hn n)))
    (hfrontG : ∀ n, ((↑) : ℂ → Sphere) '' frontier (jordanInterior (Hn n)) ⊆ G)
    (hboundary : ∀ n, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (Hn n))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (Jn n)))
    (hside : f '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) =
      f '' G ∩ (((↑) : ℂ → Sphere) '' jordanInterior J))
    {q : Sphere} (hend : (⋂ n, closedTerminalCap (Hn n)) = {q})
    (hq : q ∈ ((↑) : ℂ → Sphere) '' jordanInterior H) :
    (⋂ n, closedTerminalCap (Jn n)) ⊆ ((↑) : ℂ → Sphere) '' jordanInterior J := by
  obtain ⟨n,hn⟩ := nested_sphere_sets_eventually_subset
    (fun n => (isCompact_closedTerminalCap (Hn n)).isClosed) hnest
    (OnePoint.isOpen_image_coe.mpr (jordanInterior_isOpen H))
    (by rw [hend]; exact singleton_subset_iff.mpr hq)
  exact (iInter_subset _ n).trans
    ((matched_jordan_disk_subset_iff hi H (Hn n) J (Jn n) (hfrontG n) (hboundary n) hside).mp hn)

end CircleDomainRigidity

end

end OAI
