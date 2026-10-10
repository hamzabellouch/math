import OAI.NumberTheory.TotientAsymptotic.CanceledPrimeMass
import OAI.NumberTheory.TotientAsymptotic.SmoothResidualMass

namespace OAI

/-! Finite summation over the residual integer, canceled primes, and grid. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma finite_class_card_bound {α β : Type*} [DecidableEq β]
    (Q : Finset α) (T : Finset β) (key : α → β) (w : β → ℝ)
    (hkey : ∀ q ∈ Q, key q ∈ T)
    (hfiber : ∀ b ∈ T, ((Q.filter (fun q => key q=b)).card : ℝ) ≤ w b) :
    (Q.card : ℝ) ≤ ∑ b ∈ T, w b := by
  classical
  have he := Finset.card_eq_sum_card_fiberwise hkey
  rw [he, Nat.cast_sum]
  exact Finset.sum_le_sum hfiber

lemma canceled_tuple_mass (c : ℕ) (P : Finset ℕ) :
    (∑ p ∈ Fintype.piFinset (fun _ : Fin c => P),
      ∏ j : Fin c, (((p j-1 : ℕ) : ℝ)⁻¹)) =
      (∑ p ∈ P, (((p-1 : ℕ) : ℝ)⁻¹))^c := by
  have he := Finset.prod_univ_sum (fun _ : Fin c => P)
    (fun (_ : Fin c) (p : ℕ) => (((p-1 : ℕ) : ℝ)⁻¹))
  simpa using he.symm

/-- The actual finite class partition has no independence requirement: its
image is only enlarged to the product of the available choices. -/
theorem comparison_class_sum {α γ : Type*} [DecidableEq γ]
    (Q : Finset α) (D P : Finset ℕ) (G : Finset γ) (c : ℕ)
    (d : α → ℕ) (p : α → Fin c → ℕ) (g : α → γ) (A : ℝ)
    (hD : ∀ q ∈ Q, d q ∈ D)
    (hP : ∀ q ∈ Q, ∀ j, p q j ∈ P)
    (hG : ∀ q ∈ Q, g q ∈ G)
    (hclass : ∀ a ∈ D, ∀ v ∈ Fintype.piFinset (fun _ : Fin c => P), ∀ z ∈ G,
      ((Q.filter (fun q => (d q,p q,g q)=(a,v,z))).card : ℝ) ≤
        A*(a : ℝ)⁻¹*∏ j : Fin c, (((v j-1 : ℕ) : ℝ)⁻¹)) :
    (Q.card : ℝ) ≤ A*(G.card : ℝ)*(∑ a ∈ D, (a : ℝ)⁻¹)*
      (∑ p ∈ P, (((p-1 : ℕ) : ℝ)⁻¹))^c := by
  classical
  let T := D ×ˢ ((Fintype.piFinset (fun _ : Fin c => P)) ×ˢ G)
  have hkey : ∀ q ∈ Q, (d q,p q,g q) ∈ T := by
    intro q hq
    exact Finset.mem_product.mpr ⟨hD q hq,Finset.mem_product.mpr
      ⟨Fintype.mem_piFinset.mpr (hP q hq),hG q hq⟩⟩
  have hc := finite_class_card_bound Q T (fun q => (d q,p q,g q))
    (fun z => A*(z.1 : ℝ)⁻¹*∏ j : Fin c, (((z.2.1 j-1 : ℕ) : ℝ)⁻¹)) hkey (by
      intro z hz
      obtain ⟨hd,hpg⟩ := Finset.mem_product.mp hz
      obtain ⟨hp,hg⟩ := Finset.mem_product.mp hpg
      exact hclass z.1 hd z.2.1 hp z.2.2 hg)
  apply hc.trans_eq
  dsimp only [T]
  rw [Finset.sum_product]
  simp_rw [Finset.sum_product,Finset.sum_const, nsmul_eq_mul]
  rw [← canceled_tuple_mass c P]
  simp_rw [← Finset.mul_sum,← Finset.sum_mul]
  rw [← Finset.mul_sum D (fun x => (x : ℝ)⁻¹) A]
  ring

/-- Enlarge residuals to all smooth integers only after applying the class
estimate. Mertens bounds both the smooth sum and each canceled prime sum. -/
theorem comparison_class_sum_mertens (hmertens : MertensProductInput) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α γ : Type*} [DecidableEq γ]
      (Q : Finset α) (D : Finset ℕ) (G : Finset γ) (c Nz Np : ℕ)
      (d : α → ℕ) (p : α → Fin c → ℕ) (g : α → γ) (A : ℝ),
      2 ≤ Nz → 2 ≤ Np → 0 ≤ A →
      (∀ a ∈ D, 0 < a ∧ largestPrimeFactor a ≤ Nz) →
      (∀ q ∈ Q, d q ∈ D) →
      (∀ q ∈ Q, ∀ j, (p q j).Prime ∧ p q j ≤ Np) →
      (∀ q ∈ Q, g q ∈ G) →
      (∀ a ∈ D, ∀ v ∈ Fintype.piFinset (fun _ : Fin c => (Finset.Icc 2 Np).filter Nat.Prime),
        ∀ z ∈ G, ((Q.filter (fun q => (d q,p q,g q)=(a,v,z))).card : ℝ) ≤
          A*(a : ℝ)⁻¹*∏ j : Fin c, (((v j-1 : ℕ) : ℝ)⁻¹)) →
      (Q.card : ℝ) ≤ A*(G.card : ℝ)*(C*Real.log Nz)*
        (2*(Real.log C+B Np))^c := by
  obtain ⟨C,hC,hprod⟩ := hmertens
  refine ⟨C,hC,?_⟩
  intro α γ _ Q D G c Nz Np d p g A hNz hNp hA hsmooth hd hp hg hc
  let P := (Finset.Icc 2 Np).filter Nat.Prime
  have hp' : ∀ q ∈ Q, ∀ j, p q j ∈ P := by
    intro q hq j
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(hp q hq j).1.two_le,
      (hp q hq j).2⟩,(hp q hq j).1⟩
  have hdm := (smooth_residual_reciprocal_mass Nz D hsmooth).trans (hprod Nz hNz)
  have hlN : 0 < Real.log (Np : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < Np by omega))
  have hpm : (∑ p ∈ P, (((p-1 : ℕ) : ℝ)⁻¹)) ≤ 2*(Real.log C+B Np) := by
    have hl := Real.log_le_log (primeEulerProduct_pos Np) (hprod Np hNp)
    rw [Real.log_mul hC.ne' hlN.ne'] at hl
    exact (canceled_prime_mass_le_log_product Np).trans (by
      change _ ≤ 2*(Real.log C+Real.log (Real.log (Np : ℝ)))
      linarith)
  apply (comparison_class_sum Q D P G c d p g A hd hp' hg hc).trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left hdm (by positivity)
  · exact pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => by positivity)) hpm c
  · positivity
  · positivity

end TotientAsymptotic

end

end OAI
