import OAI.GroupTheory.PolycyclicRecognition.Analysis.AscendingBaseTransport
import OAI.GroupTheory.PolycyclicRecognition.Algebra.Nilpotent

namespace OAI

/-! # Combining commuting ascending actions

In a nilpotent group, two commuting automorphisms with finitely generated
ascending bases have a common finitely generated invariant base. The positive
orbit of one base is contained in a single stage of the other exhaustion.
This avoids imposing freeness or torsion-freeness on the abelianization.
-/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem fg_subgroup_le_automorphismStage (α : MulAut G) (B C : Subgroup G)
    (hB : B.map α.toMonoidHom ≤ B)
    (hcover : ∀ g, ∃ n, g ∈ automorphismStage α B n) (hC : C.FG) :
    ∃ n, C ≤ automorphismStage α B n := by
  obtain ⟨s, hs⟩ := hC
  obtain ⟨n, hn⟩ := finite_subset_subgroup_exhaustion (automorphismStage α B)
    (automorphismStage_monotone α B hB) hcover s
  refine ⟨n, ?_⟩
  rw [← hs, Subgroup.closure_le]
  exact hn

def positiveOrbitSubgroup (α : MulAut G) (C : Subgroup G) : Subgroup G :=
  ⨆ n : ℕ, C.map (α ^ n).toMonoidHom

theorem le_positiveOrbitSubgroup (α : MulAut G) (C : Subgroup G) :
    C ≤ positiveOrbitSubgroup α C := by
  have h := le_iSup (fun n : ℕ => C.map (α ^ n).toMonoidHom) 0
  change C.map (MonoidHom.id G) ≤ positiveOrbitSubgroup α C at h
  simpa only [Subgroup.map_id] using h

theorem positiveOrbitSubgroup_stable (α : MulAut G) (C : Subgroup G) :
    (positiveOrbitSubgroup α C).map α.toMonoidHom ≤ positiveOrbitSubgroup α C := by
  rw [positiveOrbitSubgroup, Subgroup.map_iSup]
  apply iSup_le
  intro n
  rw [Subgroup.map_map]
  have he : α.toMonoidHom.comp (α ^ n).toMonoidHom = (α ^ (n + 1)).toMonoidHom := by
    ext g
    change α ((α ^ n) g) = (α ^ (n + 1)) g
    rw [pow_succ', MulAut.mul_apply]
  rw [he]
  exact le_iSup (fun n : ℕ => C.map (α ^ n).toMonoidHom) (n + 1)

theorem positiveOrbitSubgroup_stable_of_commute (α β : MulAut G)
    (hcomm : Commute α β) (C : Subgroup G) (hC : C.map β.toMonoidHom ≤ C) :
    (positiveOrbitSubgroup α C).map β.toMonoidHom ≤ positiveOrbitSubgroup α C := by
  rw [positiveOrbitSubgroup, Subgroup.map_iSup]
  apply iSup_le
  intro n
  rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
  apply (le_iSup (fun n : ℕ => C.map (α ^ n).toMonoidHom) n)
  refine ⟨β c, hC ⟨c, hc, rfl⟩, ?_⟩
  exact congrArg (fun f : MulAut G => f c) (hcomm.pow_left n).eq

theorem positiveOrbitSubgroup_le (α : MulAut G) (C D : Subgroup G)
    (hCD : C ≤ D) (hD : D.map α.toMonoidHom ≤ D) :
    positiveOrbitSubgroup α C ≤ D := by
  apply iSup_le
  intro n
  rintro _ ⟨c, hc, rfl⟩
  exact automorphism_pow_mem_of_stable α D hD n (hCD hc)

theorem HasFinitelyGeneratedAscendingBase.common_base [Group.IsNilpotent G]
    {α β : MulAut G} (hα : HasFinitelyGeneratedAscendingBase α)
    (hβ : HasFinitelyGeneratedAscendingBase β) (hcomm : Commute α β) :
    ∃ D : Subgroup G, D.FG ∧ D.map α.toMonoidHom ≤ D ∧ D.map β.toMonoidHom ≤ D ∧
      (∀ g, ∃ n, g ∈ automorphismStage α D n) ∧
      (∀ g, ∃ n, g ∈ automorphismStage β D n) := by
  obtain ⟨B, hBfg, hBstable, hBcover⟩ := hα
  obtain ⟨C, hCfg, hCstable, hCcover⟩ := hβ
  let E := B ⊔ C
  have hEfg : E.FG := hBfg.sup hCfg
  obtain ⟨n, hn⟩ := fg_subgroup_le_automorphismStage α B E hBstable hBcover hEfg
  let D := positiveOrbitSubgroup α E
  have hDle : D ≤ automorphismStage α B n := positiveOrbitSubgroup_le α E _ hn
    (automorphismStage_stable α B hBstable n)
  have hDfg : D.FG := by
    let S := automorphismStage α B n
    let : Group.FG S := (Group.fg_iff_subgroup_fg S).mpr
      (fg_subgroup_map hBfg ((α⁻¹) ^ n).toMonoidHom)
    let : Group.FG (D.subgroupOf S) := CriticalPercolation.nilpotent_subgroup_fg S _
    let e := Subgroup.subgroupOfEquivOfLe hDle
    let : Group.FG D := Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
    exact (Group.fg_iff_subgroup_fg D).mp inferInstance
  -- Enlarge first by the positive beta orbit. Both invariances are then retained.
  let F := positiveOrbitSubgroup β D
  have hDβbound : ∃ m, D ≤ automorphismStage β C m :=
    fg_subgroup_le_automorphismStage β C D hCstable hCcover hDfg
  obtain ⟨m, hm⟩ := hDβbound
  have hFle : F ≤ automorphismStage β C m := positiveOrbitSubgroup_le β D _ hm
    (automorphismStage_stable β C hCstable m)
  have hFfg : F.FG := by
    let S := automorphismStage β C m
    let : Group.FG S := (Group.fg_iff_subgroup_fg S).mpr
      (fg_subgroup_map hCfg ((β⁻¹) ^ m).toMonoidHom)
    let : Group.FG (F.subgroupOf S) := CriticalPercolation.nilpotent_subgroup_fg S _
    let e := Subgroup.subgroupOfEquivOfLe hFle
    let : Group.FG F := Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
    exact (Group.fg_iff_subgroup_fg F).mp inferInstance
  have hBF : B ≤ F := le_sup_left.trans
    ((le_positiveOrbitSubgroup α E).trans (le_positiveOrbitSubgroup β D))
  have hCF : C ≤ F := le_sup_right.trans
    ((le_positiveOrbitSubgroup α E).trans (le_positiveOrbitSubgroup β D))
  refine ⟨F, hFfg, positiveOrbitSubgroup_stable_of_commute β α hcomm.symm D
    (positiveOrbitSubgroup_stable α E), positiveOrbitSubgroup_stable β D, ?_, ?_⟩
  · intro g
    obtain ⟨k, hk⟩ := hBcover g
    exact ⟨k, Subgroup.map_mono hBF hk⟩
  · intro g
    obtain ⟨k, hk⟩ := hCcover g
    exact ⟨k, Subgroup.map_mono hCF hk⟩

theorem HasFinitelyGeneratedAscendingBase.mul [Group.IsNilpotent G]
    {α β : MulAut G} (hα : HasFinitelyGeneratedAscendingBase α)
    (hβ : HasFinitelyGeneratedAscendingBase β) (hcomm : Commute α β) :
    HasFinitelyGeneratedAscendingBase (α * β) := by
  obtain ⟨D, hDfg, hDα, hDβ, _, hcover⟩ := hα.common_base hβ hcomm
  refine ⟨D, hDfg, ?_, ?_⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact hDα ⟨β g, hDβ ⟨g, hg, rfl⟩, rfl⟩
  · intro g
    obtain ⟨n, hn⟩ := hcover g
    apply Exists.intro n
    apply (mem_automorphismStage_iff _ _ _ _).mpr
    rw [hcomm.mul_pow n, MulAut.mul_apply]
    exact automorphism_pow_mem_of_stable α D hDα n
      ((mem_automorphismStage_iff _ _ _ _).mp hn)

end PolycyclicRecognition

end

end OAI
