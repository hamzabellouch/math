import OAI.GroupTheory.PolycyclicRecognition.Algebra.AlternatingBarCycles

namespace OAI

/-! # Evaluation of explicit alternating cycles

An alternating multilinear map evaluates the signed bar cycle to its value
multiplied by the factorial of the degree.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {A V : Type} [CommGroup A] [AddCommGroup V]

theorem abelianMultilinearChains_alternating {n : ℕ}
    (F : Additive A [⋀^Fin n]→ₗ[ℤ] V) (v : Fin n → A) :
    abelianMultilinearChains F.toMultilinearMap (alternatingBarChain v) =
      (n.factorial : ℤ) • F (Additive.ofMul ∘ v) := by
  classical
  rw [alternatingBarChain, map_sum]
  simp only [map_smul, abelianMultilinearChains_single, one_smul]
  change (∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) •
    F (Additive.ofMul ∘ (v ∘ σ))) = _
  have he (σ : Equiv.Perm (Fin n)) :
      (Equiv.Perm.sign σ : ℤ) • F (Additive.ofMul ∘ (v ∘ σ)) =
        F (Additive.ofMul ∘ v) := by
    rw [← Function.comp_assoc, F.map_perm]
    change (Equiv.Perm.sign σ : ℤ) •
      ((Equiv.Perm.sign σ : ℤ) • F (Additive.ofMul ∘ v)) = _
    rw [smul_smul]
    rw [Int.units_coe_mul_self, one_smul]
  simp_rw [he]
  simp [Fintype.card_perm, Fintype.card_fin, natCast_zsmul]

def alternatingBarCycle {n : ℕ} (v : Fin (n + 1) → A) :
    groupHomology.cycles (integralTrivialCoefficient A) (n + 1) :=
  groupHomology.cyclesMk (n + 1) n (ChainComplex.next_nat_succ n)
    (alternatingBarChain v) (by
      rw [groupHomology.inhomogeneousChains.d_def]
      exact alternatingBarChain_boundary v)

@[simp] theorem alternatingBarCycle_val {n : ℕ} (v : Fin (n + 1) → A) :
    groupHomology.iCycles (integralTrivialCoefficient A) (n + 1)
      (alternatingBarCycle v) = alternatingBarChain v :=
  groupHomology.iCycles_mk (ChainComplex.next_nat_succ n) _ (by
    rw [groupHomology.inhomogeneousChains.d_def]
    exact alternatingBarChain_boundary v)

def alternatingBarClass {n : ℕ} (v : Fin (n + 1) → A) :
    groupHomology (integralTrivialCoefficient A) (n + 1) :=
  groupHomology.π (integralTrivialCoefficient A) (n + 1) (alternatingBarCycle v)

theorem abelianMultilinearHomology_alternating {n : ℕ}
    (F : Additive A [⋀^Fin (n + 1)]→ₗ[ℤ] V) (v : Fin (n + 1) → A) :
    abelianMultilinearHomology F.toMultilinearMap (alternatingBarClass v) =
      ((n + 1).factorial : ℤ) • F (Additive.ofMul ∘ v) := by
  rw [alternatingBarClass, abelianMultilinearHomology_π]
  change abelianMultilinearChains F.toMultilinearMap
    (groupHomology.iCycles (integralTrivialCoefficient A) (n + 1)
      (alternatingBarCycle v)) = _
  rw [alternatingBarCycle_val]
  exact abelianMultilinearChains_alternating F v

end PolycyclicRecognition

end

end OAI
