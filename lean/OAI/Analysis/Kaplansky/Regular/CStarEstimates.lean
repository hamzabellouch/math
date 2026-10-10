import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.StableFiniteness.Definitions

namespace OAI

noncomputable section

namespace KaplanskyConsequences

universe u v w
open scoped ComplexOrder InnerProductSpace BigOperators WithCStarModule
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type u} [CStarAlgebra A] {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]

lemma norm_sum_mul_le (a b : ι → A) :
    ‖∑ i, a i * b i‖ ≤ Real.sqrt ‖∑ i, a i * star (a i)‖ *
      Real.sqrt ‖∑ i, star (b i) * b i‖ := by
  let x : C⋆ᵐᵒᵈ(A, ι → A) := WithCStarModule.equiv A _ |>.symm (fun i => star (b i))
  let y : C⋆ᵐᵒᵈ(A, ι → A) := WithCStarModule.equiv A _ |>.symm a
  have h := CStarModule.norm_inner_le (A:=A) (E:=C⋆ᵐᵒᵈ(A, ι → A)) (x:=x) (y:=y)
  simpa only [x,y,WithCStarModule.pi_inner,WithCStarModule.inner_def,
    WithCStarModule.pi_norm,WithCStarModule.equiv_symm_pi_apply,star_star,mul_comm] using h

lemma tuple_product_column (a : ι → A) (b : κ → A)
    (ha : ∑ i, star (a i)*a i = 1) (hb : ∑ j, star (b j)*b j = 1) :
    ∑ p : ι × κ, star (a p.1*b p.2)*(a p.1*b p.2) = 1 := by
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  calc
    _ = ∑ j, star (b j) * (∑ i, star (a i)*a i) * b j := by
      simp only [star_mul,Finset.mul_sum,Finset.sum_mul,mul_assoc]
    _ = 1 := by simpa [ha] using hb

lemma tuple_product_row (a : ι → A) (b : κ → A) (c d : ℝ)
    (_hc : 0 ≤ c) (hd : 0 ≤ d)
    (ha : ∑ i, a i*star (a i) ≤ c • (1:A))
    (hb : ∑ j, b j*star (b j) ≤ d • (1:A)) :
    ∑ p : ι × κ, (a p.1*b p.2)*star (a p.1*b p.2) ≤ (c*d) • (1:A) := by
  rw [Fintype.sum_prod_type]
  calc
    ∑ i, ∑ j, (a i*b j)*star (a i*b j) = ∑ i, a i*(∑ j, b j*star (b j))*star (a i) := by
      simp only [star_mul,Finset.mul_sum,Finset.sum_mul,mul_assoc]
    _ ≤ ∑ i, a i*(d • (1:A))*star (a i) :=
      Finset.sum_le_sum fun i _ => star_right_conjugate_le_conjugate hb _
    _ = d • ∑ i, a i*star (a i) := by simp [Finset.smul_sum]
    _ ≤ d • (c • (1:A)) := smul_le_smul_of_nonneg_left ha hd
    _ = (c*d) • (1:A) := by rw [smul_smul,mul_comm]

lemma exists_small_row_tuple (a : ι → A) (c : ℝ) (hc : 0 ≤ c)
    (hcol : ∑ i, star (a i)*a i = 1) (hrow : ∑ i, a i*star (a i) ≤ c • (1:A))
    (k : ℕ) : ∃ (J : Type v) (_ : Fintype J) (b : J → A),
      (∑ j, star (b j)*b j = 1) ∧ (∑ j, b j*star (b j) ≤ c^k • (1:A)) := by
  induction k with
  | zero =>
    exact ⟨PUnit,inferInstance,fun _ => 1,by simp,by simp⟩
  | succ k ih =>
    rcases ih with ⟨J,hJ,b,hb1,hb2⟩
    let := hJ
    refine ⟨ι × J,inferInstance,fun p => a p.1*b p.2,tuple_product_column a b hcol hb1,?_⟩
    simpa only [pow_succ,mul_comm] using tuple_product_row a b c (c^k) hc (pow_nonneg hc _) hrow hb2


end KaplanskyConsequences

end

end OAI
