import OAI.Analysis.CircleDomains.Topology.CompactObstaclePartition
import OAI.Analysis.CircleDomains.Selection.SaturatedNonseparation
import OAI.Analysis.CircleDomains.Topology.ConnectedExteriorNeighborhood
import OAI.Analysis.CircleDomains.Selection.DisjointDustContours

namespace OAI

/-! A componentwise prescribed open cover of a compact nonseparating
plane obstacle gives a finite disjoint Jordan cover subordinate to it.
The contours avoid the entire obstacle. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity

lemma exists_componentwise_jordan_cover
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    {F : Set ℂ} (hF : IsCompact F) (hFc : IsConnected Fᶜ)
    (O : F → Set ℂ) (hO : ∀ x, IsOpen (O x))
    (hcomp : ∀ x : F, connectedComponentIn F x.val ⊆ O x) :
    ∃ (n : ℕ) (H : Fin n → ℂ ≃ₜ ℂ),
      (F ⊆ ⋃ i, jordanInterior (H i)) ∧
      Pairwise (fun i j => Disjoint (closure (jordanInterior (H i)))
        (closure (jordanInterior (H j)))) ∧
      ∀ i, Disjoint (frontier (jordanInterior (H i))) F ∧
        ∃ x : F, closure (jordanInterior (H i)) ⊆ O x := by
  classical
  obtain ⟨s,A,hA,hd,hcover,hAO,hAF,hFA⟩ := compact_obstacle_partition hF O hO hcomp
  have hAc (i : s) : IsConnected (A i)ᶜ := by
    apply nonseparating_closed_relative_complement_piece
      hF.isClosed.isOpen_compl hFc (hA i).isClosed
    · simpa only [compl_compl] using hFA i
    · simpa only [compl_compl] using hAF i
  choose V hVo hAV hVO hVc hVu using fun i : s =>
    exists_open_connected_exterior_neighborhood (hA i) (hAc i) (hO i.val) (hAO i)
  obtain ⟨f,t,γ,H,S,hS,hcov,hpair,hcurves⟩ := exists_disjoint_dust_contours hsard hsch
    A V F hA hd hAF hFA hVo hAV (fun i => (hVc i).isPreconnected) hVu
  let : Fintype S := hS.fintype
  let e : S ≃ Fin (Fintype.card S) := Fintype.equivFin S
  refine ⟨Fintype.card S,fun i => H (e.symm i),?_,?_,?_⟩
  · intro z hz
    have hzA : z ∈ ⋃ i, A i := hcover.symm ▸ hz
    obtain ⟨p,hp,hzp⟩ := mem_iUnion₂.mp (hcov hzA)
    refine mem_iUnion.mpr ⟨e ⟨p,hp⟩,?_⟩
    simpa only [e.symm_apply_apply] using hzp
  · intro i j hij
    exact hpair (e.symm i).property (e.symm j).property
      (fun he => hij (e.symm.injective (Subtype.ext he)))
  · intro i
    let p := e.symm i
    obtain ⟨hinside,_,_,_,havoid⟩ := hcurves p p.property
    exact ⟨havoid,p.val.1.val,hinside.trans (hVO p.val.1)⟩

end CircleDomainRigidity

end

end OAI
