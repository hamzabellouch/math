import Mathlib

namespace OAI

section

open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra

namespace PartialPermutation

section SchurAverage
variable {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]

noncomputable def conjugateAverage (A : Module.End ℂ V) : Module.End ℂ V :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g : G, ρ g * A * ρ g⁻¹

omit [FiniteDimensional ℂ V] [Representation.IsIrreducible ρ] in
lemma conjugateAverage_eq_averageMap (A : Module.End ℂ V) :
    conjugateAverage ρ A =
      letI := invertibleOfNonzero (show (Fintype.card G : ℂ) ≠ 0 by exact_mod_cast Fintype.card_ne_zero)
      (ρ.linHom ρ).averageMap A := by
  let := invertibleOfNonzero (show (Fintype.card G : ℂ) ≠ 0 by exact_mod_cast Fintype.card_ne_zero)
  simp [conjugateAverage, Representation.averageMap, GroupAlgebra.average,
    Representation.linHom_apply, ← Module.End.mul_eq_comp, mul_assoc]

lemma conjugateAverage_scalar (A : Module.End ℂ V) :
    ∃ c : ℂ, conjugateAverage ρ A = c • (1 : Module.End ℂ V) := by
  let := invertibleOfNonzero (show (Fintype.card G : ℂ) ≠ 0 by exact_mod_cast Fintype.card_ne_zero)
  let F : (ρ.linHom ρ).invariants :=
    ⟨(ρ.linHom ρ).averageMap A, (ρ.linHom ρ).averageMap_invariant A⟩
  let T := Representation.invariantsEquivIntertwiningMap ρ ρ F
  obtain ⟨c, hc⟩ := Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ) |>.surjective T
  refine ⟨c, ?_⟩
  rw [Representation.IntertwiningMap.algebraMap_apply] at hc
  have h := congrArg Representation.IntertwiningMap.toLinearMap hc
  change c • (1 : Module.End ℂ V) = (ρ.linHom ρ).averageMap A at h
  rw [conjugateAverage_eq_averageMap]
  exact h.symm

omit [FiniteDimensional ℂ V] [Representation.IsIrreducible ρ] in
lemma trace_conjugateAverage (A : Module.End ℂ V) :
    LinearMap.trace ℂ V (conjugateAverage ρ A) = LinearMap.trace ℂ V A := by
  have hc : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have ht (g : G) : LinearMap.trace ℂ V (ρ g * A * ρ g⁻¹) = LinearMap.trace ℂ V A := by
    rw [LinearMap.trace_mul_cycle, ← map_mul, inv_mul_cancel, map_one, one_mul]
  simp [conjugateAverage, ht, hc]

lemma conjugateAverage_eq_trace (A : Module.End ℂ V) :
    conjugateAverage ρ A =
      (LinearMap.trace ℂ V A / (Module.finrank ℂ V : ℂ)) • (1 : Module.End ℂ V) := by
  obtain ⟨c, hc⟩ := conjugateAverage_scalar ρ A
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    have : Nontrivial V := by
      have : Nontrivial ρ.asModule := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
      exact ρ.asModuleEquiv.symm.toEquiv.nontrivial
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := V)).ne'
  have ht := trace_conjugateAverage ρ A
  rw [hc, map_smul, LinearMap.trace_one, smul_eq_mul] at ht
  rw [hc, ← ht, mul_div_cancel_right₀ _ hd]

end SchurAverage
end PartialPermutation

end

end OAI
