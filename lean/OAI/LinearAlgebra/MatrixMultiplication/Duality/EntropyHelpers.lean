import OAI.LinearAlgebra.MatrixMultiplication.Completion.Laws
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexHierarchyEntropy

namespace OAI

/-! Dual matrix multiplication exponents and finite rectangular constructions. -/

noncomputable section

namespace MatrixMultiplication.DualEntropyHelpers

open MatrixMultiplication.Foundation
open scoped BigOperators

variable {A B C X : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype X]

theorem map_comp_mass (p : FiniteLaw A) (f : A → B) (g : B → C) :
    ((p.map f).map g).mass = (p.map (fun a => g (f a))).mass := by
  classical
  funext c
  simp only [FiniteLaw.map_mass]
  calc
    (∑ b, if g b = c then ∑ a, if f a = b then p.mass a else 0 else 0) =
        ∑ b, ∑ a, if f a = b then (if g b = c then p.mass a else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : g b = c <;> simp [h]
    _ = ∑ a, ∑ b, if f a = b then (if g b = c then p.mass a else 0) else 0 :=
      Finset.sum_comm
    _ = ∑ a, if g (f a) = c then p.mass a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      simp

theorem deterministic_pair_entropy (p : FiniteLaw A) (f : A → B) (g : B → C) :
    finiteEntropy (p.map (fun a => (f a, g (f a)))).mass =
      finiteEntropy (p.map f).mass := by
  rw [← map_comp_mass p f (fun b => (b, g b))]
  exact (p.map f).map_entropy_of_injective _ (fun _ _ h => congrArg Prod.fst h)

theorem pair_entropy (p : FiniteLaw A) (f : A → B) (g : A → C) :
    finiteEntropy (p.map (fun a => (f a, g a))).mass =
      finiteEntropy (p.map f).mass +
        ∑ b, (p.map f).mass b * finiteEntropy ((p.conditional f b).map g).mass := by
  have hm : ((p.map f).joint (fun b => (p.conditional f b).map g)).mass =
      (p.map (fun a => (f a, g a))).mass := by
    funext bc
    exact p.map_mass_mul_conditional_map f g bc.1 bc.2
  rw [← hm, FiniteLaw.joint_entropy]

theorem conditional_independence_entropy (p : FiniteLaw A)
    (f : A → B) (g : A → C) (x : A → X)
    (independent : ∀ b, 0 < (p.map f).mass b → ∀ c xx,
      ((p.conditional f b).map (fun a => (g a, x a))).mass (c, xx) =
        ((p.conditional f b).map g).mass c *
          ((p.conditional f b).map x).mass xx) :
    finiteEntropy (p.map (fun a => ((f a, g a), x a))).mass -
        finiteEntropy (p.map (fun a => (f a, g a))).mass =
      finiteEntropy (p.map (fun a => (f a, x a))).mass -
        finiteEntropy (p.map f).mass := by
  classical
  have hassoc : finiteEntropy (p.map (fun a => ((f a, g a), x a))).mass =
      finiteEntropy (p.map (fun a => (f a, (g a, x a)))).mass := by
    have h := (p.map (fun a => ((f a, g a), x a))).map_entropy_of_injective
      (Equiv.prodAssoc B C X) (Equiv.prodAssoc B C X).injective
    rw [map_comp_mass] at h
    exact h.symm
  have hcond (b : B) :
      (p.map f).mass b *
          finiteEntropy ((p.conditional f b).map (fun a => (g a, x a))).mass =
        (p.map f).mass b *
          (finiteEntropy ((p.conditional f b).map g).mass +
            finiteEntropy ((p.conditional f b).map x).mass) := by
    by_cases hb : (p.map f).mass b = 0
    · simp only [hb, zero_mul]
    · have hpos : 0 < (p.map f).mass b :=
        lt_of_le_of_ne ((p.map f).nonneg b) (Ne.symm hb)
      have hm : ((p.conditional f b).map (fun a => (g a, x a))).mass =
          (((p.conditional f b).map g).joint
            (fun _ => (p.conditional f b).map x)).mass := by
        funext cx
        exact independent b hpos cx.1 cx.2
      rw [hm, CompletionLaws.independent_entropy]
  rw [hassoc, pair_entropy p f (fun a => (g a, x a)),
    pair_entropy p f g, pair_entropy p f x]
  simp_rw [hcond]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

end MatrixMultiplication.DualEntropyHelpers

end

end OAI
