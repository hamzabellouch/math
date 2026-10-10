import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateRootEnergy

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.DiagonalEstimate
open Ostmann.Preliminaries Ostmann.Construction
attribute [local instance] Classical.propDecidable

def matchedRootContribution {I κ : Type*} [Fintype I] [Fintype κ] [DecidableEq I] {N : ℕ}
    (E : I → Finset (PrimeUpTo N)) (hE : ∀i,0<primeShellMass (E i))
    (A : Finset (Equiv.Perm I)) (F : (I→PrimeUpTo N)→κ→ℂ) : ℂ :=
  let μ := productPrior (fun i => primeShellPrior (E i) (hE i))
  ∑s,∑e∈A,∑f,((μ.mass f*μ.mass (f ∘ e):ℝ):ℂ)*F f s*conj (F (f ∘ e) s)

theorem weighted_pair_re_le (p q : ℝ) (hp : 0≤p) (hq : 0≤q) (z w : ℂ) :
    (((p*q:ℝ):ℂ)*z*conj w).re ≤p*q*‖z‖*‖w‖ := by
  have h := Complex.re_le_norm (((p*q:ℝ):ℂ)*z*conj w)
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hp hq),
    abs_of_nonneg hp,abs_of_nonneg hq,Complex.norm_conj] using h

theorem matchedRootContribution_re_le {I κ : Type*} [Fintype I] [Fintype κ]
    [DecidableEq I] {N : ℕ}
    (E : I → Finset (PrimeUpTo N)) (hE : ∀i,0<primeShellMass (E i))
    (A : Finset (Equiv.Perm I)) (F : (I→PrimeUpTo N)→κ→ℂ) :
    (matchedRootContribution E hE A F).re ≤
      let μ := productPrior (fun i => primeShellPrior (E i) (hE i))
      ∑s,∑e∈A,∑f,μ.mass f*μ.mass (f ∘ e)*‖F f s‖*‖F (f ∘ e) s‖ := by
  simp only [matchedRootContribution,Complex.re_sum]
  apply Finset.sum_le_sum
  intro s hs
  apply Finset.sum_le_sum
  intro e he
  apply Finset.sum_le_sum
  intro f hf
  exact weighted_pair_re_le _ _ (FinitePrior.mass_nonneg _ _) (FinitePrior.mass_nonneg _ _) _ _

theorem matchedRootContribution_le_normalized_energy {I κ : Type*} [Fintype I]
    [Fintype κ] [DecidableEq I] {N : ℕ}
    (E : I → Finset (PrimeUpTo N)) (hE : ∀i,0<primeShellMass (E i))
    (A : Finset (Equiv.Perm I)) (F : (I→PrimeUpTo N)→κ→ℂ) (T Δ W : ℝ)
    (hrange : ∀f,(productPrior (fun i => primeShellPrior (E i) (hE i))).mass f≠0 →
      ∀s,F f s≠0 → Real.exp (T+Δ-W)≤((∏i,(f i).val : ℕ):ℝ)) :
    (matchedRootContribution E hE A F).re ≤
      (A.card:ℝ)*(copiedNormalization E*Real.exp (-T-Δ+W))*
        (productPrior (fun i => primeShellPrior (E i) (hE i))).mean (fun f => ∑s,‖F f s‖^2) :=
  (matchedRootContribution_re_le E hE A F).trans
    (harmonic_matching_vector_norm_sum_le E hE A F T Δ W hrange)

theorem matchedRootContribution_partition {I κ : Type*} [Fintype I] [Fintype κ]
    [DecidableEq I] {N : ℕ}
    (E : I → Finset (PrimeUpTo N)) (hE : ∀i,0<primeShellMass (E i))
    (A : Finset (Equiv.Perm I)) (F : (I→PrimeUpTo N)→κ→ℂ) :
    matchedRootContribution E hE Finset.univ F =
      matchedRootContribution E hE A F+matchedRootContribution E hE (Finset.univ\A) F := by
  unfold matchedRootContribution
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  symm
  exact Finset.sum_add_sum_compl A _

end Ostmann.Characters.DiagonalEstimate

end

end OAI
