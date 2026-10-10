import OAI.NumberTheory.Ostmann.Characters.TemplateDiagonalMatchingUnary

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.DiagonalEstimate
open Ostmann.Preliminaries TemplateDiagonalMatching
attribute [local instance] Classical.propDecidable
variable {I : Type*} [Fintype I] [DecidableEq I] {N : ℕ}

def copiedNormalization (E : I → Finset (PrimeUpTo N)) : ℝ :=
  ∏i,(primeShellMass (E i))⁻¹

omit [DecidableEq I] in
theorem copiedNormalization_nonneg (E : I → Finset (PrimeUpTo N))
    (hE : ∀i,0<primeShellMass (E i)) : 0≤copiedNormalization E := by
  exact Finset.prod_nonneg fun i _ => inv_nonneg.mpr (hE i).le

theorem tuple_mass_le_normalized (E : I → Finset (PrimeUpTo N))
    (hE : ∀i,0<primeShellMass (E i)) (f : I → PrimeUpTo N)
    (R : ℝ) (hR : 0<R) (hf : R≤((∏i,(f i).val : ℕ):ℝ)) :
    (productPrior (fun i => primeShellPrior (E i) (hE i))).mass f ≤
      copiedNormalization E/R := by
  rw [tuple_prior_mass_eq]
  split_ifs
  · exact div_le_div_of_nonneg_left (copiedNormalization_nonneg E hE) hR hf
  · exact div_nonneg (copiedNormalization_nonneg E hE) hR.le

theorem matched_mass_factorization (E : I → Finset (PrimeUpTo N))
    (hE : ∀i,0<primeShellMass (E i)) (f : I → PrimeUpTo N)
    (e : Equiv.Perm I) (T Δ : ℝ) :
    (productPrior (fun i => primeShellPrior (E i) (hE i))).mass (f ∘ e) =
      (copiedNormalization E * Real.exp (-T-Δ)) *
      (Real.exp (T+Δ)/((∏i,(f i).val : ℕ):ℝ)) *
      ∏i,if f (e i)∈E i then (1:ℝ) else 0 := by
  rw [matched_tuple_prior_mass_eq_unary]
  have he : Real.exp (-T-Δ)*Real.exp (T+Δ)=1 := by
    rw [←Real.exp_add]
    have hz : -T-Δ+(T+Δ)=0 := by ring
    rw [hz,Real.exp_zero]
  dsimp only [copiedNormalization]
  calc
    _ = (∏i,(primeShellMass (E i))⁻¹) *
        (Real.exp (-T-Δ)*Real.exp (T+Δ)) /
        ((∏i,(f i).val : ℕ):ℝ) * (∏i,if f (e i)∈E i then (1:ℝ) else 0) := by rw [he]; ring
    _ = _ := by ring

theorem tuple_mass_le_exp_window (E : I → Finset (PrimeUpTo N))
    (hE : ∀i,0<primeShellMass (E i)) (f : I → PrimeUpTo N)
    (T Δ W : ℝ) (hf : Real.exp (T+Δ-W)≤((∏i,(f i).val : ℕ):ℝ)) :
    (productPrior (fun i => primeShellPrior (E i) (hE i))).mass f ≤
      copiedNormalization E * Real.exp (-T-Δ+W) := by
  have h := tuple_mass_le_normalized E hE f _ (Real.exp_pos _) hf
  have he : (Real.exp (T+Δ-W))⁻¹=Real.exp (-T-Δ+W) := by
    rw [←Real.exp_neg]
    congr 1
    ring
  simpa only [div_eq_mul_inv,he] using h

end Ostmann.Characters.DiagonalEstimate

end

end OAI
