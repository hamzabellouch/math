import OAI.NumberTheory.Ostmann.Tree.IndependentMajorants

namespace OAI

namespace Ostmann.Tree
noncomputable section
open scoped BigOperators
open Density
variable {I C : Type*} [Fintype I] [DecidableEq I] [CommGroup C] [Fintype C] [DecidableEq C]
variable {A : I → Type*} [∀ i,Fintype (A i)]

theorem constrainedMajorant_average_uniform (e : I → C ≃ C) (B : ∀ i,C → A i → ℝ)
    (hB : ∀ i χ x,0≤B i χ x) (j : I) (δ M : ℝ) (hδ0 : 0≤δ) (hM : 1≤M)
    (hδ : ∀ χ,average (B j χ)≤δ)
    (hmass : ∀ i,(∑ χ : C,average (B i χ))≤M) :
    average (constrainedMajorant e B)≤δ*M^(Fintype.card I) := by
  apply (constrainedMajorant_average_bound e B hB j δ hδ).trans
  apply mul_le_mul_of_nonneg_left _ hδ0
  calc
    _ ≤ ∏ _i : {i : I // i≠j},M := by
      apply Finset.prod_le_prod₀
      · intro i _
        apply Finset.sum_nonneg
        intro χ _
        exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun x _ => hB i χ x))
      · intro i _
        exact hmass i
    _ = M^(Fintype.card {i : I // i≠j}) := by simp
    _ ≤ M^(Fintype.card I) := pow_le_pow_right₀ hM (Fintype.card_subtype_le _)

end
end Ostmann.Tree

end OAI
