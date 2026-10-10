import OAI.GroupTheory.PolycyclicRecognition.Analysis.BarChainExhaustion
import Mathlib.RingTheory.Noetherian.Basic

namespace OAI

/-! # Homology classes and finite generation along subgroup exhaustions -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2
variable {G : Type} [Group G]

def subgroupHomologyInclusion (H : Subgroup G) (A : Rep ℤ G) (i : ℕ) :
    groupHomology (Rep.res H.subtype A) i ⟶ groupHomology A i :=
  HomologicalComplex.homologyMap (subgroupBarInclusion H A) i

theorem exists_homologyClass_in_subgroup (S : ℕ → Subgroup G)
    (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n)
    (A : Rep ℤ G) (i : ℕ) (x : groupHomology A i) :
    ∃ n, ∃ y : groupHomology (Rep.res (S n).subtype A) i,
      subgroupHomologyInclusion (S n) A i y = x := by
  refine groupHomology_induction_on x ?_
  intro z
  obtain ⟨n, w, hw⟩ := exists_barChain_in_subgroup S hS hcover A i
    (groupHomology.iCycles A i z)
  let F := subgroupBarInclusion (S n) A
  let C := groupHomology.inhomogeneousChains (Rep.res (S n).subtype A)
  let j := (ComplexShape.down ℕ).next i
  have hwcycle : C.d i j w = 0 := by
    apply subgroupBarInclusion_injective (S n) A j
    have hc := congrArg (fun f => f.hom w) (F.comm i j)
    change F.f j (C.d i j w) = F.f j 0
    rw [map_zero]
    change (groupHomology.inhomogeneousChains A).d i j (F.f i w) =
      F.f j (C.d i j w) at hc
    rw [← hc, hw]
    exact congrArg (fun f => f.hom z)
      ((groupHomology.inhomogeneousChains A).iCycles_d i j)
  let wz := groupHomology.cyclesMk i j rfl w hwcycle
  have hwz : HomologicalComplex.cyclesMap F i wz = z := by
    apply (ModuleCat.mono_iff_injective (groupHomology.iCycles A i)).mp inferInstance
    have hc := congrArg (fun f => f.hom wz) (HomologicalComplex.cyclesMap_i F i)
    change groupHomology.iCycles A i (HomologicalComplex.cyclesMap F i wz) =
      F.f i (groupHomology.iCycles (Rep.res (S n).subtype A) i wz) at hc
    rw [groupHomology.iCycles_mk] at hc
    exact hc.trans hw
  refine ⟨n, groupHomology.π (Rep.res (S n).subtype A) i wz, ?_⟩
  have hn := congrArg (fun f => f.hom wz) (HomologicalComplex.homologyπ_naturality F i)
  change subgroupHomologyInclusion (S n) A i
      (groupHomology.π (Rep.res (S n).subtype A) i wz) =
    groupHomology.π A i (HomologicalComplex.cyclesMap F i wz) at hn
  exact hn.trans (congrArg (groupHomology.π A i) hwz)

def subgroupRestrictionMap {H K : Subgroup G} (hHK : H ≤ K) (A : Rep ℤ G) :
    Rep.res H.subtype A ⟶ Rep.res (Subgroup.inclusion hHK) (Rep.res K.subtype A) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

theorem subgroupHomologyInclusion_factor {H K : Subgroup G} (hHK : H ≤ K)
    (A : Rep ℤ G) (i : ℕ) :
    groupHomology.map (Subgroup.inclusion hHK) (subgroupRestrictionMap hHK A) i ≫
        subgroupHomologyInclusion K A i = subgroupHomologyInclusion H A i := by
  change groupHomology.map _ _ i ≫ groupHomology.map _ _ i = groupHomology.map _ _ i
  rw [← groupHomology.map_comp]
  exact groupHomology.map_congr (by ext; rfl) (by ext; rfl) i

theorem subgroupHomologyInclusion_range_mono {H K : Subgroup G} (hHK : H ≤ K)
    (A : Rep ℤ G) (i : ℕ) :
    LinearMap.range (subgroupHomologyInclusion H A i).hom ≤
      LinearMap.range (subgroupHomologyInclusion K A i).hom := by
  rintro x ⟨y, rfl⟩
  refine ⟨groupHomology.map (Subgroup.inclusion hHK) (subgroupRestrictionMap hHK A) i y, ?_⟩
  exact congrArg (fun f => f.hom y) (subgroupHomologyInclusion_factor hHK A i)

theorem exists_surjective_homology_stage (S : ℕ → Subgroup G)
    (hS : Monotone S) (hcover : ∀ g, ∃ n, g ∈ S n)
    (A : Rep ℤ G) (i : ℕ) [Module.Finite ℤ (groupHomology A i)] :
    ∃ n, Epi (subgroupHomologyInclusion (S n) A i) := by
  classical
  have hstage (T : Finset (groupHomology A i)) :
      ∃ n, ∀ x ∈ T, x ∈ LinearMap.range (subgroupHomologyInclusion (S n) A i).hom := by
    induction T using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | @insert x T _ ih =>
      obtain ⟨n, y, hy⟩ := exists_homologyClass_in_subgroup S hS hcover A i x
      obtain ⟨m, hm⟩ := ih
      refine ⟨max n m, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact subgroupHomologyInclusion_range_mono (hS (le_max_left _ _)) A i ⟨y, hy⟩
      · exact subgroupHomologyInclusion_range_mono (hS (le_max_right _ _)) A i (hm z hz)
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := ℤ) (M := groupHomology A i)
  obtain ⟨n, hn⟩ := hstage T
  refine ⟨n, (ModuleCat.epi_iff_surjective _).mpr (LinearMap.range_eq_top.mp ?_)⟩
  apply top_unique
  rw [← hT]
  exact Submodule.span_le.mpr hn

end PolycyclicRecognition

end

end OAI
