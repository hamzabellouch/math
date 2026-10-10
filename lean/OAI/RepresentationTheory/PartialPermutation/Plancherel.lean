import Mathlib
import OAI.RepresentationTheory.PartialPermutation.Characters
import OAI.RepresentationTheory.PartialPermutation.CompleteKernels
import OAI.RepresentationTheory.PartialPermutation.RegularRepresentation

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators
open scoped BigOperators MonoidAlgebra Classical

namespace PartialPermutation
noncomputable section
open scoped BigOperators MonoidAlgebra Classical

variable {G : Type*} [Group G] [Fintype G]

omit [Fintype G] in
lemma componentRep_unitary {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : IsUnitary ρ)
    (c : isotypicComponents ℂ[G] ρ.asModule) : IsUnitary (componentRep ρ c) := by
  intro g x y
  exact hρ g x.val y.val

lemma complexFourier_regular_delta (a : G → ℂ) (g : G) :
    complexFourier (regularRep G) a (deltaOne G) g = a g := by
  simp [complexFourier, deltaOne, inv_mul_eq_one, eq_comm]

abbrev irreducibleRep (c : IrreducibleIndex G) := componentRep (regularRep G) c

lemma irreducibleRep_unitary (c : IrreducibleIndex G) :
    IsUnitary (G := G) (V := irreducibleSpace c) (irreducibleRep c) :=
  componentRep_unitary (regularRep G) (regularRep_unitary G) c

lemma regular_character_identity (g : G) :
    ∑ c : IrreducibleIndex G, (irreducibleDegree c : ℂ) * (irreducibleRep c).character g =
      if g = 1 then (Fintype.card G : ℂ) else 0 := by
  have ht := congrArg (fun A : Module.End ℂ (EuclideanSpace ℂ G) => A (deltaOne G) g⁻¹)
    (sum_character_kernels_identity (regularRep G))
  rw [complexFourier_regular_delta] at ht
  change (∑ c : IrreducibleIndex G, centralCharacterKernel (irreducibleRep c) g⁻¹) =
    (deltaOne G) g⁻¹ at ht
  simp only [centralCharacterKernel, inv_inv] at ht
  have hN : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have ht' := congrArg (fun z : ℂ => (Fintype.card G : ℂ) * z) ht
  simp only [Finset.mul_sum] at ht'
  convert ht' using 1
  · apply Finset.sum_congr rfl
    intro c _
    change _ = (Fintype.card G : ℂ) *
      ((irreducibleDegree c : ℂ) / Fintype.card G * (irreducibleRep c).character g)
    field_simp
  · change (if g = 1 then (Fintype.card G : ℂ) else 0) =
      (Fintype.card G : ℂ) * (if g⁻¹ = 1 then 1 else 0)
    simp only [inv_eq_one]
    split_ifs <;> simp

lemma sum_regular_character_kernels (g : G) :
    ∑ c : IrreducibleIndex G, centralCharacterKernel (irreducibleRep c) g =
      if g = 1 then 1 else 0 := by
  have ht := congrArg (fun A : Module.End ℂ (EuclideanSpace ℂ G) => A (deltaOne G) g)
    (sum_character_kernels_identity (regularRep G))
  rw [complexFourier_regular_delta] at ht
  exact ht

lemma irreducibleRep_complete {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ] :
    ∃! c : IrreducibleIndex G, Nonempty (Representation.Equiv (irreducibleRep c) ρ) := by
  have : Nontrivial V := IsSimpleModule.nontrivial ℂ[G] ρ.asModule
  have hex : ∃ c : IrreducibleIndex G, Nonempty (Representation.Equiv (irreducibleRep c) ρ) := by
    by_contra hn
    push Not at hn
    have hs : complexFourier ρ (fun g => ∑ c : IrreducibleIndex G,
        centralCharacterKernel (irreducibleRep c) g) = 1 := by
      simp only [sum_regular_character_kernels]
      simp [complexFourier]
    rw [complexFourier_sum] at hs
    have hz : (∑ c : IrreducibleIndex G, complexFourier ρ
        (centralCharacterKernel (irreducibleRep c))) = 0 := by
      apply Finset.sum_eq_zero
      intro c _
      rw [centralCharacterKernel_fourier, ite_eq_right (fun ⟨e⟩ => (hn c).false e)]
    rw [hz] at hs
    exact zero_ne_one hs
  obtain ⟨c, hc⟩ := hex
  refine ⟨c, hc, ?_⟩
  intro d hd
  obtain ⟨e⟩ := hc
  obtain ⟨f⟩ := hd
  exact (componentRep_equiv_iff (regularRep G) d c).mp ⟨f.trans e.symm⟩

lemma trace_fourier_energy {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (hρ : IsUnitary ρ) (a : G → ℂ) :
    LinearMap.trace ℂ V (LinearMap.adjoint (complexFourier ρ a) * complexFourier ρ a) =
      ∑ h, ∑ g, conj (a h) * a g * ρ.character (h⁻¹ * g) := by
  have hadj : LinearMap.adjoint (complexFourier ρ a) =
      ∑ h, conj (a h) • ρ h⁻¹ := by
    simp only [complexFourier, map_sum, map_smulₛₗ, unitary_adjoint ρ hρ]
  rw [hadj, complexFourier, Finset.sum_mul]
  simp only [map_sum, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, map_smul,
    smul_eq_mul, ← map_mul, Representation.character]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro g _
  ring

theorem finite_group_plancherel (a : G → ℂ) :
    (Fintype.card G : ℝ) * ∑ g, ‖a g‖^2 =
      ∑ c : IrreducibleIndex G, (irreducibleDegree c : ℝ) *
        hsNormSq (V := irreducibleSpace c) (complexFourier (V := irreducibleSpace c) (irreducibleRep c) a) := by
  have he : ∑ c : IrreducibleIndex G, (irreducibleDegree c : ℂ) *
      LinearMap.trace ℂ (irreducibleSpace c)
        (LinearMap.adjoint (𝕜 := ℂ) (E := irreducibleSpace c) (F := irreducibleSpace c) (complexFourier (V := irreducibleSpace c) (irreducibleRep c) a) *
          complexFourier (V := irreducibleSpace c) (irreducibleRep c) a) =
        (Fintype.card G : ℂ) * ∑ g, conj (a g) * a g := by
    have htrace (c : IrreducibleIndex G) := trace_fourier_energy
      (V := irreducibleSpace c) (irreducibleRep c) (irreducibleRep_unitary c) a
    simp only [htrace, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ h, ∑ g, conj (a h) * a g *
          (∑ c : IrreducibleIndex G, (irreducibleDegree c : ℂ) *
            (irreducibleRep c).character (h⁻¹ * g)) := by
        apply Finset.sum_congr rfl
        intro h _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro g _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        ring
      _ = _ := by
        simp only [regular_character_identity, inv_mul_eq_one]
        simp [mul_comm, mul_left_comm]
  have hre := congrArg Complex.re he
  have hnorm (g : G) : (conj (a g) * a g).re = ‖a g‖^2 := by
    rw [mul_comm, Complex.mul_conj]
    exact Complex.normSq_eq_norm_sq _
  simpa only [Complex.re_sum, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero, hnorm, hsNormSq] using hre.symm

end
end PartialPermutation
end

end OAI
