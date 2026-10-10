import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Transport.FiniteModules
import OAI.Algebra.FinitisticAsymmetry.Kasch.FiniteDimension

namespace OAI

section
section
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]
section ZeroDimensions
variable {R k : Type u} [Ring R] [Nontrivial R] [Field k] [Algebra k R]

lemma littleFinitisticDimension_nonneg : 0 ≤ littleFinitisticDimension R := by
  have hpd : projectiveDimension (ModuleCat.of R R) = 0 :=
    (projectiveDimension_eq_zero_iff _).mpr ⟨inferInstance, fun h => by
      let := ModuleCat.isZero_iff_subsingleton.mp h
      exact (one_ne_zero : (1 : R) ≠ 0) (Subsingleton.elim _ _)⟩
  exact le_iSup_of_le (ModuleCat.of R R) (le_iSup_of_le (inferInstance : Module.Finite R R)
    (le_iSup_of_le (by rw [hpd]; norm_cast) hpd.ge))

lemma dimensions_zero_of_splitBasic_rightSocle {ι : Type u} [Finite ι]
    (χ : R →ₐ[k] (ι → k)) (hχ : Function.Surjective χ)
    (hJ : ∃ n : ℕ, (RingHom.ker χ.toRingHom) ^ n = ⊥)
    (a : ι → R) (ha : ∀ i, a i ≠ 0)
    (hmul : ∀ i r, a i * r = χ r i • a i) :
    littleFinitisticDimension R = 0 ∧ bigFinitisticDimension R = 0 := by
  have hb : bigFinitisticDimension R ≤ 0 := by
    refine iSup_le fun M => iSup_le fun hpd => ?_
    let : Projective M := Kasch.projective_of_finiteDimension χ a ha hmul hχ hJ M hpd
    exact (projectiveDimension_le_iff M 0).mpr inferInstance
  have hl : 0 ≤ littleFinitisticDimension R := littleFinitisticDimension_nonneg
  have hlb := littleFinitisticDimension_le_big R
  exact ⟨le_antisymm (hlb.trans hb) hl, le_antisymm hb (hl.trans hlb)⟩

end ZeroDimensions

end LittleFinitistic
end
end
end

end OAI
