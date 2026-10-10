import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ActivityResidue
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.FreeResidues
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.PrivateMono

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.SourceCylinder
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h L ℓ t : ℕ}

theorem residual_rank_private_family (w : ClosedLine h ℓ)
    (a : S.FixedResidues w) (c : Cylinder (fun p : S.FreeIndex w => ZMod (p.val:ℕ)))
    (ht : 0 < t) (hrank : t ≤ Cylinder.rank (residualEvents w D L a) c)
    (z : S.FreeResidues w) (hz : c.Holds z) :
    ∃ F : PrivateFamily w D L t,
      ∀ j p, (F.witness j).spec.ResidueTest p (F.witness j).vertex (mergeResidues w a z p) := by
  obtain ⟨A,hA,hcard,hle,hprivate⟩ := Cylinder.exists_private_family (residualEvents w D L a)
    c t ht hrank
  let e : Fin t ≃ A := (Fintype.equivFinOfCardEq (by simpa using hcard)).symm
  have hex (j : Fin t) : ∃ s : AttachedSpec w D L, s.Compatible a ∧ s.residualCylinder=(e j).val := by
    obtain ⟨s,hs,he⟩ := mem_image.mp (hA (e j).property)
    exact ⟨s,(mem_filter.mp hs).2,he⟩
  let s : Fin t → AttachedSpec w D L := fun j => Classical.choose (hex j)
  have hs (j : Fin t) : (s j).Compatible a ∧ (s j).residualCylinder=(e j).val :=
    Classical.choose_spec (hex j)
  have hq (j : Fin t) := hprivate (e j).val (e j).property
  let q : Fin t → S.FreeIndex w := fun j => Classical.choose (hq j)
  have hqs (j : Fin t) : q j ∈ (s j).residualCylinder.support := by
    rw [(hs j).2]
    exact (Classical.choose_spec (hq j)).1
  have hqs' (j : Fin t) : ((q j).val:ℕ) ∈ (s j).spec.primeSupport :=
    ((s j).residual_support_iff (q j)).mp (hqs j)
  have hpriv (i j : Fin t) (hij : i≠j) : ((q i).val:ℕ) ∉ (s j).spec.primeSupport := by
    intro hm
    have hmem : q i ∈ (e j).val.support := by
      rw [←(hs j).2]
      exact ((s j).residual_support_iff (q i)).mpr hm
    have heq := (Classical.choose_spec (hq i)).2 (e j).val (e j).property hmem
    exact hij (e.injective (Subtype.ext heq.symm))
  let F := sortPrivateFamily w s (fun j => (q j).val) hqs' (fun j => (q j).property) hpriv
  refine ⟨F,?_⟩
  apply sortPrivateFamily_witness w s (fun j => (q j).val) hqs'
    (fun j => (q j).property) hpriv
      (fun v => ∀ p, v.spec.ResidueTest p v.vertex (mergeResidues w a z p))
  intro j
  apply ((s j).fullCylinder_holds _).mp
  apply ((s j).fullCylinder_merge a z).mpr
  refine ⟨(hs j).1,?_⟩
  rw [(hs j).2]
  exact Cylinder.holds_mono (hle (e j).val (e j).property) hz

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
