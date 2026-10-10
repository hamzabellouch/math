import Mathlib
import OAI.RepresentationTheory.PartialPermutation.ProjectionEnergy

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

attribute [local instance] Classical.propDecidable
namespace PartialPermutation
noncomputable section
variable {G : Type*} [Group G] [Fintype G]

def smallTypeKernel (G : Type*) [Group G] [Fintype G] (R : ℝ) : G → ℂ :=
  fun g => ∑ c : IrreducibleIndex G,
    if (irreducibleDegree c : ℝ) ≤ R then centralCharacterKernel (irreducibleRep c) g else 0

lemma smallTypeKernel_inv (R : ℝ) (g : G) :
    smallTypeKernel G R g⁻¹ = conj (smallTypeKernel G R g) := by
  simp only [smallTypeKernel, map_sum]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp [centralCharacterKernel_inv _ (irreducibleRep_unitary c)]

lemma complexFourier_smallTypeKernel {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (R : ℝ) : complexFourier ρ (smallTypeKernel G R) =
      if (Module.finrank ℂ V : ℝ) ≤ R then 1 else 0 := by
  classical
  obtain ⟨c, ⟨e⟩, hc⟩ := irreducibleRep_complete ρ
  have hdeg : irreducibleDegree c = Module.finrank ℂ V := e.toLinearEquiv.finrank_eq
  have he (d : IrreducibleIndex G) :
      Nonempty (Representation.Equiv (irreducibleRep d) ρ) ↔ d = c := by
    exact ⟨hc d, fun h => h ▸ ⟨e⟩⟩
  unfold smallTypeKernel
  rw [complexFourier_sum]
  calc
    _ = ∑ d : IrreducibleIndex G, if d = c then
        (if (Module.finrank ℂ V : ℝ) ≤ R then (1 : Module.End ℂ V) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      by_cases hd : (irreducibleDegree d : ℝ) ≤ R
      · simp only [hd, ite_true, centralCharacterKernel_fourier]
        by_cases hdc : d = c
        · subst d
          rw [hdeg] at hd
          simp [he, hd]
        · simp [he, hdc]
      · simp only [hd, ite_false, complexFourier]
        by_cases hdc : d = c
        · subst d
          simp [hdeg] at hd
          simp [hd]
        · simp [hdc]
    _ = _ := by simp

@[simp] lemma hsNormSq_one {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] : hsNormSq (1 : Module.End ℂ V) = Module.finrank ℂ V := by
  simp [hsNormSq, LinearMap.trace_one]

lemma degree_le_of_kernel_identity {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ] (hρ : IsUnitary ρ)
    (k : G → ℂ) (d : ℕ) (hk : ∑ g, ‖k g‖^2 = (d : ℝ)^2 / Fintype.card G)
    (hact : complexFourier ρ k = 1) : Module.finrank ℂ V ≤ d := by
  have h := fourier_bessel ρ hρ k
  have hN : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [hact, hsNormSq_one, hk] at h
  have hd : (Module.finrank ℂ V : ℝ)^2 ≤ (d : ℝ)^2 := by
    convert h using 1 <;> field_simp
  exact_mod_cast (sq_le_sq₀ (by positivity) (by positivity)).mp hd

lemma smallTypeKernel_identity_of_kernel {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (k : G → ℂ) (d : ℕ) (R : ℝ) (hd : (d : ℝ) ≤ R)
    (hk : ∑ g, ‖k g‖^2 = (d : ℝ)^2 / Fintype.card G)
    (hact : complexFourier ρ k = 1) : complexFourier ρ (smallTypeKernel G R) = 1 := by
  apply linearMap_eq_on_simples ρ
  intro σ hσ x
  have := hσ
  have hu : IsUnitary σ.toRepresentation := fun g x y => hρ g x y
  have hs : complexFourier σ.toRepresentation k = 1 := by
    ext y
    rw [complexFourier_subrep, hact]
    rfl
  have hdeg := degree_le_of_kernel_identity σ.toRepresentation hu k d hk hs
  have hdegR : (Module.finrank ℂ σ.toSubmodule : ℝ) ≤ R := (Nat.cast_le.mpr hdeg).trans hd
  rw [← complexFourier_subrep, complexFourier_smallTypeKernel, ite_eq_left hdegR]
  rfl

end
end PartialPermutation

end

end OAI
