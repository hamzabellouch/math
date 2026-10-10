import OAI.GroupTheory.PolycyclicRecognition.Algebra.FreeAbelianLogarithm
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolycyclicTorsionFree

namespace OAI

/-! # Logarithms of powers of finitely generated abelian characters

A finite-index free subgroup supplies a compatible choice on a basis.
The index-power map pulls that choice back to the whole group.
-/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type} [CommGroup G]

def finiteIndexPowerHom (K : Subgroup G) : G →* K where
  toFun g := ⟨g ^ K.index, K.pow_index_mem g⟩
  map_one' := by apply Subtype.ext; exact one_pow _
  map_mul' g h := by apply Subtype.ext; exact mul_pow g h _

theorem finitelyGenerated_character_power_log [Group.FG G] (ρ : G →* ℂˣ) :
    ∃ m : ℕ, 0 < m ∧ ∃ L : G →* Multiplicative ℂ,
      ∀ g, complexUnitExp (L g) = ρ g ^ m := by
  have hpoly := isPolycyclic_of_finitelyGenerated_commGroup G
  obtain ⟨K, hK, htf⟩ := hpoly.exists_torsionFree_finiteIndex
  let := hK
  obtain ⟨n, ⟨e⟩⟩ := exists_integralLattice_equiv htf
  let r := ρ.comp (K.subtype.comp e.toMonoidHom)
  let p := e.symm.toMonoidHom.comp (finiteIndexPowerHom K)
  refine ⟨K.index, Nat.pos_of_ne_zero hK.index_ne_zero,
    (freeAbelianLogarithm r).comp p, ?_⟩
  intro g
  have h := DFunLike.congr_fun (freeAbelianLogarithm_exp r) (p g)
  change complexUnitExp (freeAbelianLogarithm r (p g)) = _
  rw [MonoidHom.comp_apply] at h
  rw [h]
  change ρ (e (e.symm (finiteIndexPowerHom K g))) = ρ g ^ K.index
  rw [e.apply_symm_apply]
  exact map_pow ρ g K.index

end PolycyclicRecognition

end

end OAI
