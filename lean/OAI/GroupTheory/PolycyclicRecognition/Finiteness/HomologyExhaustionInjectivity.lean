import OAI.GroupTheory.PolycyclicRecognition.Finiteness.HomologyClassExhaustion
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.HomologyBoundary

namespace OAI

/-! # Detection of zero classes in a subgroup exhaustion -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory HomologicalComplex
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem subgroupBarInclusion_factor {H K : Subgroup G} (hHK : H ≤ K)
    (A : Rep ℤ G) :
    groupHomology.chainsMap (Subgroup.inclusion hHK) (subgroupRestrictionMap hHK A) ≫
      subgroupBarInclusion K A = subgroupBarInclusion H A := by
  change groupHomology.chainsMap _ _ ≫ groupHomology.chainsMap _ _ =
    groupHomology.chainsMap _ _
  rw [← groupHomology.chainsMap_comp]
  exact groupHomology.chainsMap_congr (by ext; rfl)
    (by apply DFunLike.ext; intro x; rfl)

theorem homology_zero_in_stage (S : ℕ → Subgroup G) (hS : Monotone S)
    (hcover : ∀ g, ∃ n, g ∈ S n) (A : Rep ℤ G) (i n : ℕ)
    (x : groupHomology (Rep.res (S n).subtype A) i)
    (hx : subgroupHomologyInclusion (S n) A i x = 0) :
    ∃ m, ∃ hnm : n ≤ m,
      groupHomology.map (Subgroup.inclusion (hS hnm))
        (subgroupRestrictionMap (hS hnm) A) i x = 0 := by
  induction x using groupHomology_induction_on with
  | h z =>
    let C := groupHomology.inhomogeneousChains A
    let F := subgroupBarInclusion (S n) A
    have hn := congrArg (fun f => f z) (homologyπ_naturality F i)
    change subgroupHomologyInclusion (S n) A i (groupHomology.π _ i z) =
      C.homologyπ i (cyclesMap F i z) at hn
    obtain ⟨w, hw⟩ := exists_boundary_of_homologyπ_eq_zero C i (cyclesMap F i z)
      (hn.symm.trans hx)
    let T (k : ℕ) := S (n + k)
    have hT : Monotone T := fun a b hab => hS (Nat.add_le_add_left hab n)
    have hcoverT : ∀ g, ∃ k, g ∈ T k := by
      intro g
      obtain ⟨k, hk⟩ := hcover g
      exact ⟨k, hS (Nat.le_add_left k n) hk⟩
    obtain ⟨k, v, hv⟩ := exists_barChain_in_subgroup T hT hcoverT A (i + 1) w
    let m := n + k
    have hnm : n ≤ m := Nat.le_add_right n k
    let J := groupHomology.chainsMap (Subgroup.inclusion (hS hnm))
      (subgroupRestrictionMap (hS hnm) A)
    let Cm := groupHomology.inhomogeneousChains (Rep.res (S m).subtype A)
    let Fm := subgroupBarInclusion (S m) A
    have hj : Fm.f i (Cm.iCycles i (cyclesMap J i z)) = C.iCycles i (cyclesMap F i z) := by
      have hc := congrArg (fun f => f z) (cyclesMap_i J i)
      change Cm.iCycles i (cyclesMap J i z) = J.f i (groupHomology.iCycles _ i z) at hc
      rw [hc]
      have hcomp := congrArg (fun f => f.f i (groupHomology.iCycles _ i z))
        (subgroupBarInclusion_factor (hS hnm) A)
      have hcy := congrArg (fun f => f z) (cyclesMap_i F i)
      exact hcomp.trans hcy.symm
    have hb : Cm.d (i + 1) i v = Cm.iCycles i (cyclesMap J i z) := by
      apply subgroupBarInclusion_injective (S m) A i
      have hc := congrArg (fun f => f v) (Fm.comm (i + 1) i)
      change C.d (i + 1) i (Fm.f (i + 1) v) = Fm.f i (Cm.d (i + 1) i v) at hc
      rw [← hc, hv, hw, hj]
    have hz := homologyπ_eq_zero_of_boundary Cm i (cyclesMap J i z) v hb
    refine ⟨m, hnm, ?_⟩
    have hc := congrArg (fun f => f z) (homologyπ_naturality J i)
    exact hc.trans hz

theorem subgroupHomologyInclusion_injective_of_stages
    (S : ℕ → Subgroup G) (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n)
    (A : Rep ℤ G) (i : ℕ)
    (hinj : ∀ n m (hnm : n ≤ m), Function.Injective
      (groupHomology.map (Subgroup.inclusion (hS hnm))
        (subgroupRestrictionMap (hS hnm) A) i)) (n : ℕ) :
    Function.Injective (subgroupHomologyInclusion (S n) A i) := by
  apply (injective_iff_map_eq_zero (subgroupHomologyInclusion (S n) A i).hom).mpr
  intro x hx
  obtain ⟨m, hnm, hm⟩ := homology_zero_in_stage S hS hcover A i n x hx
  apply hinj n m hnm
  simpa using hm

end PolycyclicRecognition

end

end OAI
