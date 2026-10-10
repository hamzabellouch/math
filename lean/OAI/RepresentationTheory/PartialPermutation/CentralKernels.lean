import Mathlib
import OAI.RepresentationTheory.PartialPermutation.Model

namespace OAI

section
open scoped Classical
open scoped BigOperators ComplexConjugate MonoidAlgebra
open scoped BigOperators ComplexConjugate
open scoped MonoidAlgebra BigOperators

namespace PartialPermutation
noncomputable section
open scoped MonoidAlgebra BigOperators

section CentralFourier
variable {G V : Type*} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)

omit [FiniteDimensional ℂ V] in
lemma centralFourier_commute (a : G → ℂ)
    (ha : ∀ g h, a (g * h) = a (h * g)) (g : G) :
    complexFourier ρ a * ρ g = ρ g * complexFourier ρ a := by
  classical
  simp only [complexFourier, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, ← map_mul]
  calc
    _ = ∑ h : G, a (g * h * g⁻¹) • ρ (g * h * g⁻¹ * g) := by
      exact (Fintype.sum_equiv (Equiv.mulLeft g |>.trans (Equiv.mulRight g⁻¹)) _ _
        (fun h => rfl)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h _
      rw [ha (g * h) g⁻¹]
      simp [mul_assoc]

lemma centralFourier_scalar [Representation.IsIrreducible ρ] (a : G → ℂ)
    (ha : ∀ g h, a (g * h) = a (h * g)) :
    ∃ c : ℂ, complexFourier ρ a = c • (1 : Module.End ℂ V) := by
  let T : Representation.IntertwiningMap ρ ρ :=
    { toLinearMap := complexFourier ρ a
      isIntertwining' := fun g => by
        simpa only [Module.End.mul_eq_comp] using centralFourier_commute ρ a ha g }
  obtain ⟨c, hc⟩ := Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ) |>.surjective T
  refine ⟨c, ?_⟩
  rw [Representation.IntertwiningMap.algebraMap_apply] at hc
  exact (congrArg Representation.IntertwiningMap.toLinearMap hc).symm

end CentralFourier

def centralCharacterKernel {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) : ℂ :=
  (Module.finrank ℂ V : ℂ) / Fintype.card G * ρ.character g⁻¹

lemma centralCharacterKernel_comm {G V : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g h : G) :
    centralCharacterKernel ρ (g * h) = centralCharacterKernel ρ (h * g) := by
  simp only [centralCharacterKernel, mul_inv_rev]
  rw [Representation.char_mul_comm]

lemma centralCharacterKernel_fourier {G V W : Type*} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ] :
    complexFourier σ (centralCharacterKernel ρ) =
      if Nonempty (Representation.Equiv ρ σ) then 1 else 0 := by
  classical
  obtain ⟨c, hc⟩ := centralFourier_scalar σ (centralCharacterKernel ρ)
    (centralCharacterKernel_comm ρ)
  have : Nontrivial W := IsSimpleModule.nontrivial ℂ[G] σ.asModule
  have hD : (Module.finrank ℂ W : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℂ) (M := W)).ne'
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    exact_mod_cast (Nat.card_pos (α := G)).ne')
  have ht := congrArg (LinearMap.trace ℂ W) hc
  have ho := Representation.char_orthonormal σ ρ
  have htrace : LinearMap.trace ℂ W (complexFourier σ (centralCharacterKernel ρ)) =
      (Module.finrank ℂ V : ℂ) *
        (if Nonempty (Representation.Equiv ρ σ) then 1 else 0) := by
    simp only [complexFourier, map_sum, map_smul, smul_eq_mul, centralCharacterKernel]
    change (∑ g, (Module.finrank ℂ V : ℂ) / Fintype.card G *
      ρ.character g⁻¹ * σ.character g) = _
    calc
      _ = (Module.finrank ℂ V : ℂ) * ((Fintype.card G : ℂ)⁻¹ *
          ∑ g, σ.character g * ρ.character g⁻¹) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g _
        ring
      _ = _ := by rw [Fintype.card_eq_nat_card, ho]
  rw [htrace, map_smul, LinearMap.trace_one, smul_eq_mul] at ht
  split_ifs with he
  · obtain ⟨e⟩ := he
    have hd := e.toLinearEquiv.finrank_eq
    have hcd : c = 1 := by
      rw [ite_eq_left ⟨e⟩, mul_one, hd] at ht
      apply (mul_right_cancel₀ hD)
      simpa using ht.symm
    simpa [hcd] using hc
  · have hcd : c = 0 := by
      rw [ite_eq_right he, mul_zero] at ht
      exact (mul_eq_zero.mp ht.symm).resolve_right hD
    simpa [hcd] using hc

end
end PartialPermutation
end

end OAI
