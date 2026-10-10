import OAI.GroupTheory.PolycyclicRecognition.Lattices.FreeAbelianCyclicLattice
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CyclicKernelSplitting
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolycyclicTorsionFree

namespace OAI

/-! # Lattice realization for torsion-free nilpotent groups with abelian cyclic kernel

The nilpotency class is unrestricted. An abstract abelian kernel is identified
with its integral basis before applying the constructed real flow.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped IsMulCommutative

theorem abelian_cyclic_nilpotent_lattice {H : Type} [CommGroup H] [Group.FG H]
    (htf : HasNoNontrivialTorsion H) (a : MulAut H)
    [Group.IsNilpotent (H ⋊[integerPowerAction a] Multiplicative ℤ)] :
    ∃ (S : SimplyConnectedSolvableLieModel) (Γ : Subgroup S.carrier),
      IsUniformLattice Γ ∧ Nonempty ((H ⋊[integerPowerAction a] Multiplicative ℤ) ≃* Γ) := by
  obtain ⟨d, ⟨e⟩⟩ := exists_integralLattice_equiv htf
  let aZ : MulAut (IntegralLatticeGroup d) := e.trans (a.trans e.symm)
  have he (x : IntegralLatticeGroup d) : e (aZ x) = a (e x) := by
    change e (e.symm (a (e x))) = _
    exact e.apply_symm_apply _
  let E : (IntegralLatticeGroup d ⋊[integerPowerAction aZ] Multiplicative ℤ) ≃*
      (H ⋊[integerPowerAction a] Multiplicative ℤ) :=
    SemidirectProduct.congr e (MulEquiv.refl _) (by
      intro n
      ext x
      exact mulAut_zpow_semiconj aZ a e he n.toAdd x)
  let : Group.IsNilpotent
      (IntegralLatticeGroup d ⋊[integerPowerAction aZ] Multiplicative ℤ) :=
    Group.nilpotent_of_mulEquiv E.symm
  obtain ⟨S, Γ, hΓ, ⟨f⟩⟩ := freeAbelian_cyclic_nilpotent_lattice aZ
  exact ⟨S, Γ, hΓ, ⟨E.symm.trans f⟩⟩

theorem nilpotent_abelian_kernel_cyclic_lattice {G : Type} [Group G]
    [Group.FG G] [Group.IsNilpotent G] (htf : HasNoNontrivialTorsion G)
    (q : G →* Multiplicative ℤ) (hq : Function.Surjective q)
    [IsMulCommutative q.ker] :
    ∃ (S : SimplyConnectedSolvableLieModel) (Γ : Subgroup S.carrier),
      IsUniformLattice Γ ∧ Nonempty (G ≃* Γ) := by
  obtain ⟨t, ht⟩ := hq (Multiplicative.ofAdd 1)
  let E := cyclicKernelEquiv q t ht
  let : Group.FG q.ker := CriticalPercolation.nilpotent_subgroup_fg G q.ker
  let : Group.IsNilpotent
      (q.ker ⋊[integerPowerAction (MulAut.conjNormal t)] Multiplicative ℤ) :=
    Group.nilpotent_of_mulEquiv E.symm
  obtain ⟨S, Γ, hΓ, ⟨f⟩⟩ := abelian_cyclic_nilpotent_lattice
    (htf.of_injective q.ker.subtype Subtype.val_injective) (MulAut.conjNormal t)
  exact ⟨S, Γ, hΓ, ⟨E.symm.trans f⟩⟩

end PolycyclicRecognition

end

end OAI
