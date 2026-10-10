import Mathlib
import OAI.Probability.BinarySweep.Processes.IndependentHistory

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
variable {I X : Type*} [Fintype I] [Fintype X] [DecidableEq X]

lemma realSign_swap {u v : X} (huv : u≠v) : realSign (Equiv.swap u v) = -1 := by
  simp [realSign,Equiv.Perm.sign_swap huv]

omit [Fintype I] [Fintype X] in
lemma assigns_swap_left (A B : I ↪ X) {u v : X}
    (hu : u∉Set.range B) (hv : v∉Set.range B) (σ : Equiv.Perm X) :
    Assigns A B (Equiv.swap u v*σ) ↔ Assigns A B σ := by
  have hf (i : I) : Equiv.swap u v (B i)=B i := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro he; exact hu ⟨i,he⟩
    · intro he; exact hv ⟨i,he⟩
  constructor
  · intro hh i
    apply (Equiv.swap u v).injective
    exact (hh i).trans (hf i).symm
  · intro hh i
    change Equiv.swap u v (σ (A i))=B i
    rw [hh i,hf]

omit [Fintype I] in
theorem sum_sign_assigns_zero (A B : I ↪ X) {u v : X}
    (huv : u≠v) (hu : u∉Set.range B) (hv : v∉Set.range B) :
    (∑σ : Equiv.Perm X, if Assigns A B σ then realSign σ else 0) = 0 := by
  classical
  let f (σ : Equiv.Perm X) := if Assigns A B σ then realSign σ else 0
  have ht (σ : Equiv.Perm X) : f (Equiv.swap u v*σ) = -f σ := by
    dsimp [f]
    rw [assigns_swap_left A B hu hv,map_mul,realSign_swap huv]
    split_ifs <;> ring
  have he := Equiv.sum_comp (Equiv.mulLeft (Equiv.swap u v)) f
  change (∑σ, f (Equiv.swap u v*σ))=∑σ,f σ at he
  simp_rw [ht] at he
  rw [Finset.sum_neg_distrib] at he
  dsimp [f] at he
  linarith

omit [Fintype I] in
lemma uniform_sign_assigns_zero (A B : I ↪ X) {u v : X}
    (huv : u≠v) (hu : u∉Set.range B) (hv : v∉Set.range B) :
    (∑σ : Equiv.Perm X, if Assigns A B σ then
      uniformLaw (Equiv.Perm X) σ * realSign σ else 0) = 0 := by
  have ht (σ : Equiv.Perm X) :
      (if Assigns A B σ then uniformLaw (Equiv.Perm X) σ*realSign σ else 0) =
      (Fintype.card (Equiv.Perm X):ℝ)⁻¹*(if Assigns A B σ then realSign σ else 0) := by
    split_ifs <;> simp [uniformLaw]
  simp_rw [ht]
  rw [←Finset.mul_sum,sum_sign_assigns_zero A B huv hu hv,mul_zero]

lemma uniform_sign_zero [Nontrivial X] :
    (∑σ : Equiv.Perm X, uniformLaw (Equiv.Perm X) σ*realSign σ)=0 := by
  obtain ⟨u,v,huv⟩ := exists_pair_ne X
  let E : Fin 0 ↪ X := ⟨Fin.elim0,by intro i; exact Fin.elim0 i⟩
  have hs := uniform_sign_assigns_zero E E huv
    (by rintro ⟨i,_⟩; exact Fin.elim0 i) (by rintro ⟨i,_⟩; exact Fin.elim0 i)
  simpa [Assigns] using hs

lemma lineLaw_sign_zero {d : ℕ} (hd : 0<d) (z : ℝ) :
    (∑σ : Equiv.Perm (Slot d), lineLaw d z σ*realSign σ)=0 := by
  have : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  have : Nontrivial (Slot d) := inferInstance
  simp_rw [lineLaw,add_mul,mul_assoc]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,
    uniform_sign_zero,binary_sign_annihilated d hd,mul_zero,mul_zero,add_zero]

end BinaryCoordinateSweeps

end

end OAI
