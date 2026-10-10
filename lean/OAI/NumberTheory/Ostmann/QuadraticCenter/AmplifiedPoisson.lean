import OAI.NumberTheory.Ostmann.QuadraticCenter.AmplifierPoissonExpansion
import OAI.NumberTheory.Ostmann.QuadraticCenter.CompositeCenter
import OAI.NumberTheory.Ostmann.QuadraticCenter.WeightedPoisson

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open Ostmann.QuadraticSieve
open scoped BigOperators FourierTransform SchwartzMap

def subsetQuadraticDual {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (U : Finset ι)
    (q : ℕ) [NeZero q] (X : ℝ) (t r s : ℤ) : ℂ := by
  let d := ∏ i : U, p i
  letI : NeZero d := ⟨(subset_modulus_pos p U).ne'⟩
  exact ((X / (q * d) : ℝ) : ℂ) * gaussSum (jacobiDirichletCharacter q) ZMod.stdAddChar *
    ∑' u : ℤ, (jacobiSym (u * r) q : ℂ) *
      ZMod.stdAddChar (((u * r : ℤ) : ZMod q) * (t : ZMod q)) *
      ZMod.dft (subsetCenteredProduct p hcop S U) (-((u * s : ℤ) : ZMod d)) *
      𝓕 SchwartzCutoff.psi ((u : ℝ) * X / (q * d))

theorem subset_quadratic_poisson {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (U : Finset ι)
    {q : ℕ} [NeZero q] (hqd : q.Coprime (∏ i : U, p i))
    (hq : Odd q) (hsq : Squarefree q) {X : ℝ} (hX : 0 < X) (t r s : ℤ)
    (hbez : ((∏ i : U, p i : ℕ) : ℤ) * r + (q : ℤ) * s = 1) :
    (∑' n : ℤ, (jacobiSym (n - t) q : ℂ) *
      subsetCenteredProduct p hcop S U (n : ZMod (∏ i : U, p i)) *
        SchwartzCutoff.psi ((n : ℝ) / X)) = subsetQuadraticDual p hcop S U q X t r s := by
  let : NeZero (∏ i : U, p i) := ⟨(subset_modulus_pos p U).ne'⟩
  exact weighted_translated_quadratic_poisson hqd hq hsq r s hbez X hX t
    (subsetCenteredProduct p hcop S U) SchwartzCutoff.psi

theorem amplified_quadratic_poisson {ι : Type*} [Fintype ι]
    (p : ι → ℕ) [∀ i, NeZero (p i)]
    (hcop : Pairwise (fun i j => (p i).Coprime (p j)))
    (S : ∀ i, Finset (ZMod (p i))) (lam : ℝ)
    {q : ℕ} [NeZero q] (hqL : q.Coprime (∏ i, p i))
    (hq : Odd q) (hsq : Squarefree q) {X : ℝ} (hX : 0 < X) (t : ℤ) :
    ∃ r s : Finset ι → ℤ,
      (∀ U : Finset ι, ((∏ i : U, p i : ℕ) : ℤ) * r U + (q : ℤ) * s U = 1) ∧
      (∑' n : ℤ, (jacobiSym (n - t) q : ℂ) *
        (amplifier p hcop S lam (n : ZMod (∏ i, p i)) : ℂ) *
          SchwartzCutoff.psi ((n : ℝ) / X)) =
        ∑ U : Finset ι, (lam : ℂ) ^ U.card * subsetQuadraticDual p hcop S U q X t (r U) (s U) := by
  classical
  have hc (U : Finset ι) : q.Coprime (∏ i : U, p i) :=
    hqL.of_dvd_right (subset_modulus_dvd p U)
  choose r s hrs using (fun U : Finset ι => exists_crt_bezout (hc U))
  refine ⟨r, s, hrs, ?_⟩
  rw [amplified_transform_subset_expansion p hcop S lam q t hX]
  apply Finset.sum_congr rfl
  intro U hU
  rw [subset_quadratic_poisson p hcop S U (hc U) hq hsq hX t (r U) (s U) (hrs U)]

end Ostmann.QuadraticCenter

end

end OAI
