import OAI.NumberTheory.Ostmann.Arithmetic.PolynomialFlagMass
import OAI.NumberTheory.Ostmann.Arithmetic.PolynomialFlagReplacementFiniteReindex

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.PolynomialFlagReplacementUnnormalized
open scoped BigOperators
open MvPolynomial PolynomialFlagReplacementFinite

theorem weighted_restricted_flag_error_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : MvPolynomial ι ℤ) (hP : P≠0)
    (S : ι → Finset ℤ) (μ : ι → ℤ → ℝ) (B : Finset ℕ) (ν : ℕ → ℝ)
    (α β H A C Cnu : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hH : 0 ≤ H) (hA : 0 ≤ A)
    (hC : 0 ≤ C) (hCnu : 0 ≤ Cnu)
    (hμ : ∀i a,a∈S i → 0 ≤ μ i a) (hmass : ∀i,∑a∈S i,μ i a ≤ C)
    (hatom : ∀i a,a∈S i → μ i a ≤ α)
    (hprime : ∀b∈B,b.Prime) (hν : ∀b∈B,0 ≤ ν b) (hνmass : ∑b∈B,ν b ≤ Cnu)
    (hνatom : ∀b∈B,ν b ≤ β)
    (hsize : ∀x,(∀i,x i∈S i) → eval x P≠0 → Real.log |((eval x P:ℤ):ℝ)| ≤ H)
    (r : (ι → ℤ) → ℕ → Bool) (w : (ι → ℤ) → ℕ → ℝ)
    (hw : ∀x,(∀i,x i∈S i) → ∀b∈B,0 ≤ w x b ∧ w x b ≤ A) :
    (∑x∈Fintype.piFinset S,(∏i,μ i (x i))*
      (∑b∈B,ν b*(if r x b then w x b*flagError P x b else 0))) ≤
      A*((P.totalDegree:ℝ)*α*C^(Fintype.card ι-1)*Cnu+β*(H/Real.log 2)*C^Fintype.card ι) := by
  classical
  let e := Fintype.equivFin ι
  have hsupport (x : Fin (Fintype.card ι) → ℤ)
      (hx : ∀j,x j∈S (e.symm j)) : ∀i,(x ∘ e) i∈S i := by
    intro i
    simpa only [Function.comp_apply,e.symm_apply_apply] using hx (e i)
  have hsize' (x : Fin (Fintype.card ι) → ℤ) (hx : ∀j,x j∈S (e.symm j))
      (hne : eval x (rename e P)≠0) : Real.log |((eval x (rename e P):ℤ):ℝ)| ≤ H := by
    simpa only [eval_rename_equiv] using hsize (x ∘ e) (hsupport x hx)
      (by simpa only [eval_rename_equiv] using hne)
  have hh := PolynomialFlagMass.weighted_restricted_flag_error_le
    (rename e P) (rename_ne_zero e hP) (fun j => S (e.symm j)) (fun j => μ (e.symm j))
    B ν α β H A C Cnu hα hβ hH hA hC hCnu (fun j a ha => hμ (e.symm j) a ha)
    (fun j => hmass (e.symm j)) (fun j a ha => hatom (e.symm j) a ha)
    hprime hν hνmass hνatom hsize' (fun x => r (x ∘ e)) (fun x => w (x ∘ e))
    (fun x hx b hb => hw (x ∘ e) (hsupport x hx) b hb)
  have heflag (x : Fin (Fintype.card ι) → ℤ) (b : ℕ) :
      PolynomialFlagReplacement.flagError (rename e P) x b=flagError P (x ∘ e) b := by
    rw [fin_flagError_eq,flagError_rename_equiv]
  simp_rw [heflag] at hh
  rw [totalDegree_rename_equiv] at hh
  rw [expectation_reindex_eq_product_sum e S μ
    (fun x => ∑b∈B,ν b*(if r x b then w x b*flagError P x b else 0))] at hh
  exact hh

end Ostmann.Arithmetic.PolynomialFlagReplacementUnnormalized

end

end OAI
