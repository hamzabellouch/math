import OAI.NumberTheory.TotientAsymptotic.SquarefreeBandTail

namespace OAI

/-! Exact finite factorization turns independent interval masses into a product. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

lemma finite_factor_reciprocal_mass {k : ℕ} (Q : Finset ℕ) (f : ℕ → Fin k → ℕ)
    (hf : ∀ n ∈ Q,∏ j,f n j=n) :
    (∑ n ∈ Q,(n:ℝ)⁻¹) ≤ ∏ j,∑ d ∈ Q.image (fun n => f n j),(d:ℝ)⁻¹ := by
  classical
  let T : Fin k → Finset ℕ := fun j => Q.image (fun n => f n j)
  have hi : Set.InjOn f (↑Q : Set ℕ) := by
    intro n hn m hm he
    rw [← hf n hn,← hf m hm,he]
  have hs : Q.image f ⊆ Fintype.piFinset T := by
    intro t ht
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp ht
    exact Fintype.mem_piFinset.mpr (fun j => Finset.mem_image.mpr ⟨n,hn,rfl⟩)
  calc
    _ = ∑ n ∈ Q,∏ j,(f n j:ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro n hn
      conv_lhs => rw [← hf n hn]
      rw [Nat.cast_prod,Finset.prod_inv_distrib]
    _ = ∑ t ∈ Q.image f,∏ j,(t j:ℝ)⁻¹ := by
      symm
      rw [Finset.sum_image hi]
    _ ≤ ∑ t ∈ Fintype.piFinset T,∏ j,(t j:ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun t _ _ =>
        Finset.prod_nonneg (fun j _ => inv_nonneg.mpr (Nat.cast_nonneg _)))
    _ = _ := (Finset.prod_univ_sum T (fun (_ : Fin k) (d : ℕ) => (d:ℝ)⁻¹)).symm

theorem finite_squarefree_band_mass : ∃ D : ℝ,0 < D ∧
    ∀ (k : ℕ) (U V c R : Fin k → ℝ),
    (∀ j,2 ≤ U j) → (∀ j,U j ≤ V j) → (∀ j,1 ≤ c j) →
    ∀ (Q : Finset ℕ) (f : ℕ → Fin k → ℕ),
    (∀ n ∈ Q,∏ j,f n j=n) →
    (∀ n ∈ Q,∀ j,Squarefree (f n j) ∧
      (∀ p ∈ (f n j).primeFactorsList,U j < (p:ℝ) ∧ (p:ℝ) ≤ V j) ∧
      R j ≤ ((f n j).primeFactorsList.length:ℝ)) →
    (∑ n ∈ Q,(n:ℝ)⁻¹) ≤
      Real.exp (∑ j : Fin k,(c j*(B (V j)-B (U j)+D)-R j*Real.log (c j))) := by
  obtain ⟨D,hD,hbound⟩ := squarefree_band_lower_mass
  refine ⟨D,hD,?_⟩
  intro k U V c R hU hUV hc Q f hf hQ
  apply (finite_factor_reciprocal_mass Q f hf).trans
  rw [Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro j _
    exact Finset.sum_nonneg (fun d _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  · intro j _
    apply hbound (U j) (V j) (c j) (R j) (hU j) (hUV j) (hc j)
    intro d hd
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hd
    exact hQ n hn j

end TotientAsymptotic

end

end OAI
