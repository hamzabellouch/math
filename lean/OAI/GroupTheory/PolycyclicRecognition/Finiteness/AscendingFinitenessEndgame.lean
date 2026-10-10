import OAI.GroupTheory.PolycyclicRecognition.Algebra.AscendingExtensionDimension
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolycyclicExtensionDimension

namespace OAI

/-! # The algebraic conclusion of the ascending structural alternative

These are concrete data for the ascending virtually nilpotent groups in
Kropholler--Martínez-Pérez--Nucinkis, J. reine angew. Math. 637 (2009),
Theorem 1.1(x). The ascending structure is an explicit hypothesis.
-/

noncomputable section
namespace PolycyclicRecognition
variable (G : Type) [Group G]

structure AscendingVirtuallyNilpotentData where
  height : G →* Multiplicative ℤ
  letter : G
  height_letter : height letter = Multiplicative.ofAdd 1
  base : Subgroup height.ker
  base_fg : Group.FG base
  base_nilpotent : Group.IsVirtuallyNilpotent base
  stable : base.map (MulAut.conjNormal (H := height.ker) letter).toMonoidHom ≤ base
  exhaustive : ∀ g : height.ker, ∃ n,
    g ∈ automorphismStage (MulAut.conjNormal (H := height.ker) letter) base n

variable {G}

theorem AscendingVirtuallyNilpotentData.finitelyGenerated
    (D : AscendingVirtuallyNilpotentData G) : Group.FG G := by
  let := D.base_fg
  let α : MulAut D.height.ker := MulAut.conjNormal D.letter
  let A : Subgroup G := D.base.map D.height.ker.subtype
  let C : Subgroup G := A ⊔ Subgroup.zpowers D.letter
  have htC : D.letter ∈ C :=
    (show Subgroup.zpowers D.letter ≤ C from le_sup_right) (Subgroup.mem_zpowers _)
  have hbC (b : D.height.ker) (hb : b ∈ D.base) : (b : G) ∈ C :=
    (show A ≤ C from le_sup_left) ⟨b, hb, rfl⟩
  have hinv (b : D.height.ker) (hb : (b : G) ∈ C) : ((α⁻¹) b : G) ∈ C := by
    change ((MulAut.conjNormal (H := D.height.ker) D.letter).symm b : G) ∈ C
    rw [MulAut.conjNormal_symm_apply]
    exact C.mul_mem (C.mul_mem (C.inv_mem htC) hb) htC
  have hstage (n : ℕ) (b : D.height.ker) (hb : b ∈ D.base) :
      (((α⁻¹) ^ n) b : G) ∈ C := by
    induction n with
    | zero => simpa using hbC b hb
    | succ n ih => simpa only [pow_succ', MulAut.mul_apply] using hinv _ ih
  have hker (g : D.height.ker) : (g : G) ∈ C := by
    obtain ⟨n, b, hb, he⟩ := D.exhaustive g
    exact he ▸ hstage n b hb
  have hC : C = ⊤ := by
    apply top_unique
    intro g _
    rw [← integerQuotientPart_decompose D.height D.letter D.height_letter g]
    exact C.mul_mem (hker _) (C.zpow_mem htC _)
  let e : D.base ≃* A := D.base.equivMapOfInjective D.height.ker.subtype
    D.height.ker.subtype_injective
  let : Group.FG A := Group.fg_of_surjective (f := e.toMonoidHom) e.surjective
  have hAfg : A.FG := (Group.fg_iff_subgroup_fg A).mp inferInstance
  have hTfg : (Subgroup.zpowers D.letter).FG :=
    (Group.fg_iff_subgroup_fg _).mp (finitelyGenerated_of_isCyclic)
  have htop : (⊤ : Subgroup G).FG := hC ▸ hAfg.sup hTfg
  let : Group.FG (⊤ : Subgroup G) := (Group.fg_iff_subgroup_fg _).mpr htop
  exact Group.fg_of_surjective (f := (⊤ : Subgroup G).subtype)
    (by intro g; exact ⟨⟨g, trivial⟩, rfl⟩)

theorem AscendingVirtuallyNilpotentData.virtualSolvableFiniteDimension
    (D : AscendingVirtuallyNilpotentData G) :
    ∃ V : Subgroup G, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V := by
  let := D.base_fg
  exact exists_finiteIndex_solvable_finiteDimension_of_ascending
    D.height D.letter D.height_letter D.base D.stable D.exhaustive D.base_nilpotent

theorem virtualSolvableFiniteDimension_of_ascending_normal_subgroup
    (N : Subgroup G) [N.Normal] (D : AscendingVirtuallyNilpotentData N)
    (hQ : IsVirtuallyPolycyclic (G ⧸ N)) :
    ∃ V : Subgroup G, V.FiniteIndex ∧ Group.IsSolvable V ∧
      HasFiniteIntegralCohomologicalDimension V := by
  let := D.finitelyGenerated
  exact exists_solvable_finiteDimension_of_virtuallyPolycyclic_quotient N
    D.virtualSolvableFiniteDimension hQ

end PolycyclicRecognition

end

end OAI
