import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Model

namespace OAI

section
section
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]
namespace Kasch

universe v w
variable {R : Type u} [Ring R]

abbrev radicalPart (J : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] :
    Submodule R M := J • (⊤ : Submodule R M)

lemma map_radical_le (J : Ideal R) {P : Type v} {Q : Type w}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (f : P →ₗ[R] Q) : (radicalPart J P).map f ≤ radicalPart J Q := by
  rw [radicalPart, Submodule.map_smul'']
  exact Submodule.smul_mono le_rfl le_top

lemma isNilpotent_of_range_le_radical {P : Type v} [AddCommGroup P] [Module R P]
    (J : Ideal R) [J.IsTwoSided] (hJ : ∃ n : ℕ, J ^ n = ⊥)
    (f : P →ₗ[R] P) (hf : LinearMap.range f ≤ radicalPart J P) : IsNilpotent f := by
  have hn (n : ℕ) : LinearMap.range (f ^ n) ≤ J ^ n • (⊤ : Submodule R P) := by
    induction n with
    | zero => simp [Submodule.pow_zero, Ideal.one_eq_top]
    | succ n ih =>
      rw [pow_succ, Module.End.mul_eq_comp, LinearMap.range_comp]
      apply le_trans (Submodule.map_mono hf)
      rw [radicalPart, Submodule.map_smul'', Submodule.map_top]
      apply le_trans (Submodule.smul_mono le_rfl ih)
      rw [← Submodule.mul_smul, Ideal.IsTwoSided.pow_succ]
  obtain ⟨n, hnil⟩ := hJ
  refine ⟨n, ?_⟩
  apply LinearMap.range_eq_bot.mp
  apply le_bot_iff.mp
  simpa [hnil] using hn n

lemma top_semisimple {S : Type v} [Ring S] [IsSemisimpleRing S]
    (χ : R →+* S) (hχ : Function.Surjective χ)
    (M : Type w) [AddCommGroup M] [Module R M] :
    IsSemisimpleModule R (M ⧸ radicalPart (RingHom.ker χ) M) := by
  let : IsSemisimpleRing (R ⧸ (RingHom.ker χ)) :=
    (χ.quotientKerEquivOfSurjective hχ).symm.isSemisimpleRing
  exact (Module.isTorsionBySet_quotient_ideal_smul M (RingHom.ker χ)).isSemisimpleModule_iff.mp
    inferInstance

end Kasch
end LittleFinitistic
end
end
end

end OAI
