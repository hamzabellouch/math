import OAI.GroupTheory.PolycyclicRecognition.Analysis.AlternatingBarEndpoints
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.AbelianMultilinearHomology

namespace OAI

/-! # Explicit signed-permutation cycles in the abelian bar complex -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {A : Type} [CommGroup A]

def alternatingBarChain {n : ℕ} (v : Fin n → A) : (Fin n → A) →₀ ℤ :=
  ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) • Finsupp.single (v ∘ σ) 1

theorem alternatingBarChain_d_formula {n : ℕ} (v : Fin (n + 1) → A) :
    groupHomology.inhomogeneousChains.d (integralTrivialCoefficient A) n
      (alternatingBarChain v) =
    ∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) •
      (Finsupp.single (fun i => v (σ i.succ)) (1 : ℤ) +
        ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) •
          Finsupp.single (Fin.contractNth j (· * ·) (v ∘ σ)) 1) := by
  rw [alternatingBarChain, map_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [map_smul]
  congr 1
  rw [groupHomology.inhomogeneousChains.d_single]
  rfl

theorem alternatingBarChain_boundary {n : ℕ} (v : Fin (n + 1) → A) :
    groupHomology.inhomogeneousChains.d (integralTrivialCoefficient A) n
      (alternatingBarChain v) = 0 := by
  rw [alternatingBarChain_d_formula]
  simp only [smul_add, Finset.smul_sum, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  simp_rw [smul_comm (↑(Equiv.Perm.sign _) : ℤ), ← Finset.smul_sum]
  rw [Fin.sum_univ_castSucc]
  have hint : (∑ j : Fin n, (-1 : ℤ) ^ (j.castSucc.val + 1) •
      (∑ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.sign σ : ℤ) •
        Finsupp.single (Fin.contractNth j.castSucc (· * ·) (v ∘ σ)) (1 : ℤ))) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [alternatingBar_interior_cancel v j, smul_zero]
  rw [hint, zero_add]
  simpa only [Fin.val_last, contractNth_last_eq, Function.comp_def] using
    alternatingBar_endpoints_cancel v

end PolycyclicRecognition

end

end OAI
