import OAI.NumberTheory.Ostmann.Arithmetic.TreePermutationHaar

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PermutationDiagramComparison
open scoped BigOperators

variable {r m depth : ℕ} {G : Type*} [CommGroup G]

private theorem row_filter_product (samples : Fin r × Fin m → G) (a : Fin r) :
    (∏ x : Fin r, ∏ i : Fin m, if x=a then samples (x,i) else 1)=∏i,samples (a,i) := by
  classical
  calc
    _ = ∏ x : Fin r, if x=a then ∏i : Fin m,samples (x,i) else 1 := by
      apply Finset.prod_congr rfl
      intro x hx
      by_cases h : x=a <;> simp only [h,ite_true,ite_false,Finset.prod_const_one]
    _ = _ := by simp

theorem products_left (σ : Equiv.Perm (Fin r × Fin m))
    (samples : Fin r × Fin m → G) (a : Fin r) :
    (PermutationHaar.products σ samples).1 a = ∏ i,samples (a,i) := by
  classical
  simp only [PermutationHaar.products,BipartiteHaar.slotProducts,IncidenceHaar.fiberProduct,
    MonoidHom.coe_mk,OneHom.coe_mk,Finset.prod_filter,Fintype.prod_prod_type]
  exact row_filter_product samples a

theorem products_right (σ : Equiv.Perm (Fin r × Fin m))
    (samples : Fin r × Fin m → G) (a : Fin r) :
    (PermutationHaar.products σ samples).2 a = ∏ i,samples (σ.symm (a,i)) := by
  classical
  change (∏ e ∈ Finset.univ.filter (fun e => (σ e).1=a),samples e)=_
  rw [Finset.prod_filter]
  have hh := Equiv.prod_comp σ (fun e => if e.1=a then samples (σ.symm e) else 1)
  simp only [Equiv.symm_apply_apply] at hh
  rw [hh]
  rw [Fintype.prod_prod_type]
  exact row_filter_product (samples ∘ σ.symm) a

variable {F : Type*} [Field F]

def slotLeaves (σ : Equiv.Perm (Fin (2^depth) × Fin m))
    (samples : Fin (2^depth) × Fin m → Fˣ) :
    (Tree.Leaves depth → Fˣ) × (Tree.Leaves depth → Fˣ) :=
  (fun path => ∏i,samples (TreePermutationHaar.leafIndex depth path,i),
   fun path => ∏i,samples (σ.symm (TreePermutationHaar.leafIndex depth path,i)))

theorem slotLeaves_eq_leafPairEquiv (σ : Equiv.Perm (Fin (2^depth) × Fin m))
    (samples : Fin (2^depth) × Fin m → Fˣ) :
    slotLeaves σ samples = TreePermutationHaar.leafPairEquiv
      (PermutationHaar.products σ samples) := by
  apply Prod.ext <;> funext path
  · exact (products_left σ samples _).symm
  · exact (products_right σ samples _).symm

end Ostmann.Arithmetic.PermutationDiagramComparison

end

end OAI
