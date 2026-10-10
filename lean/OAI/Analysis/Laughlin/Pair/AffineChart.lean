import OAI.Analysis.Laughlin.Pair.SpinorCube
import OAI.Analysis.Laughlin.Spin.OrbitalExpansion

namespace OAI

namespace Laughlin
open MvPolynomial
open scoped BigOperators

noncomputable def pairAffineChart {N : ℕ} (i j : Fin N) :
    MvPolynomial (SpinorVariables N) ℂ →+* MvPolynomial (Fin N) PairDiagonal.Poly :=
  eval₂Hom (C.comp (Polynomial.C.comp Polynomial.C)) (fun kb =>
    if kb.2 then
      if kb.1=i then C (Polynomial.C Polynomial.X)
      else if kb.1=j then C Polynomial.X else X kb.1
    else 1)

theorem pairAffineChart_bracket {N : ℕ} (i j : Fin N) (hij : i ≠ j) :
    pairAffineChart i j (bracket i j) = C PairDiagonal.diagonal := by
  unfold bracket
  rw [map_sub, map_mul, map_mul]
  simp [pairAffineChart, Ne.symm hij, PairDiagonal.diagonal]

theorem pairAffineChart_pair {N Q : ℕ} (i j : Fin N) (hij : i ≠ j)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) :
    pairAffineChart i j
      (pairSpinorPolynomial C (X (i,false)) (X (i,true)) (X (j,false)) (X (j,true)) Q ψ) =
      C (pairAffinePolynomial Q ψ) := by
  unfold pairSpinorPolynomial pairAffinePolynomial
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  simp [pairAffineChart, eval₂Hom, Ne.symm hij,
    ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]

noncomputable def spectatorWeight {N Q : ℕ} (i j : Fin N) (a : Configuration N Q) : ℂ :=
  ∏ k ∈ (Finset.univ.erase i).erase j, (Real.sqrt (Nat.choose Q (a k).val : ℝ) : ℂ)

noncomputable def affineExponent {N Q : ℕ} (a : Configuration N Q) : Fin N →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun k => (a k).val) (by simp)

theorem affineExponent_injective (N Q : ℕ) :
    Function.Injective (affineExponent (N := N) (Q := Q)) := by
  intro a b h
  funext k
  apply Fin.ext
  exact congrArg (fun d => d k) h

theorem spectatorWeight_ne_zero {N Q : ℕ} (i j : Fin N) (a : Configuration N Q) :
    spectatorWeight i j a ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  apply Complex.ofReal_ne_zero.mpr
  apply Real.sqrt_ne_zero'.mpr
  exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ (a k).isLt)

theorem pairAffineChart_spectator {N Q : ℕ} (i j : Fin N) (hij : i ≠ j)
    (a : PairSpectators (Q := Q) i j) :
    pairAffineChart i j (spectatorPolynomial i j a.val) =
      monomial (affineExponent a.val) (Polynomial.C (Polynomial.C (spectatorWeight i j a.val))) := by
  classical
  unfold spectatorPolynomial
  simp only [map_prod]
  have he (k : Fin N) (hk : k ∈ (Finset.univ.erase i).erase j) :
      pairAffineChart i j (spinOrbitalPolynomial Q k (a.val k)) =
        C (Polynomial.C (Polynomial.C (Real.sqrt (Nat.choose Q (a.val k).val : ℝ) : ℂ))) *
          X k^(a.val k).val := by
    have hki := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hkj := (Finset.mem_erase.mp hk).1
    simp [pairAffineChart, spinOrbitalPolynomial, eval₂Hom, hki, hkj]
  rw [Finset.prod_congr rfl he, Finset.prod_mul_distrib, monomial_eq]
  simp only [← map_prod, ← RingHom.comp_apply, spectatorWeight]
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [affineExponent, Finsupp.onFinset_apply]
  rw [prod_pair_split i j hij]
  simp [a.property.1, a.property.2]

end Laughlin

end OAI
