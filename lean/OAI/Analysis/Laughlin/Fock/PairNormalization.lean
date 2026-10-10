import OAI.Analysis.Laughlin.Exterior.PairConjugation
import OAI.Analysis.Laughlin.Operators.NormalOrderFour
import OAI.Analysis.Laughlin.Pair.Orthonormality

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem annihilate_vacuum {Q : ℕ} (i : Fin (Q+1)) : annihilate i (1 : Space Q) = 0 := by
  simp [annihilate]

theorem two_annihilate_two_create {Q : ℕ} (a b i j : Fin (Q+1)) :
    annihilate b (annihilate a (create i (create j (1 : Space Q)))) =
      (delta a i*delta b j-delta b i*delta a j) • (1 : Space Q) := by
  have h := LinearMap.congr_fun (normal_order_four a b i j) (1 : Space Q)
  simpa [Module.End.mul_apply, annihilate_vacuum, smul_smul, sub_smul] using h

theorem pairEnd_two_create (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ)
    (i j : Fin (Q+1)) :
    pairEnd Q c (create i (create j (1 : Space Q))) = (c i j-c j i) • (1 : Space Q) := by
  simp only [pairEnd, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
    two_annihilate_two_create, smul_smul]
  simp [delta, mul_sub, sub_smul, mul_ite, ite_smul, Finset.sum_sub_distrib]

theorem sourcePairEnd_two_create (Q p : ℕ) (i j : Fin (Q+1)) :
    sourcePairEnd Q p (create i (create j (1 : Space Q))) =
      ((Real.sqrt 2*pairCoefficient Q p i j : ℝ) : ℂ) • (1 : Space Q) := by
  unfold sourcePairEnd
  rw [pairEnd_two_create]
  have hne : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hc : pairCoefficient Q p i j / Real.sqrt 2 - pairCoefficient Q p j i / Real.sqrt 2 =
      Real.sqrt 2*pairCoefficient Q p i j := by
    rw [pairCoefficient_swap Q p i j]
    calc
      _ = 2*pairCoefficient Q p i j / Real.sqrt 2 := by ring
      _ = (Real.sqrt 2*Real.sqrt 2)*pairCoefficient Q p i j / Real.sqrt 2 := by
        rw [Real.mul_self_sqrt (by norm_num)]
      _ = _ := by field_simp
  have h := congrArg (fun r : ℝ => (r : ℂ)) hc
  push_cast at h ⊢
  exact congrArg (fun c : ℂ => c • (1 : Space Q)) h

noncomputable def sourcePairVector (Q p : ℕ) : Space Q :=
  ∑ i, ∑ j, ((pairCoefficient Q p i j / Real.sqrt 2 : ℝ) : ℂ) •
    create i (create j (1 : Space Q))

theorem sourcePairEnd_pairVector (Q p q : ℕ) (hQ : 2 ≤ Q) (hp : p ≤ 2*Q-2) :
    sourcePairEnd Q p (sourcePairVector Q q) = (if p = q then (1 : ℂ) else 0) • (1 : Space Q) := by
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (show Real.sqrt (2 : ℝ) ≠ 0 by positivity)
  unfold sourcePairVector
  simp only [map_sum, map_smul, sourcePairEnd_two_create, smul_smul]
  have he (i j : Fin (Q+1)) :
      ((pairCoefficient Q q i j / Real.sqrt 2 : ℝ) : ℂ)*
        ((Real.sqrt 2*pairCoefficient Q p i j : ℝ) : ℂ) =
      ((pairCoefficient Q p i j : ℂ)*(pairCoefficient Q q i j : ℂ)) := by
    push_cast
    field_simp
  simp_rw [he]
  simp only [← Finset.sum_smul]
  have hg := congrArg (fun r : ℝ => (r : ℂ)) (pairCoefficient_gram Q p q hQ hp)
  push_cast at hg
  by_cases h : p = q
  · simp only [ite_eq_left h, Complex.ofReal_one] at hg ⊢
    rw [hg]
  · simp only [ite_eq_right h, Complex.ofReal_zero] at hg ⊢
    rw [hg]

end Laughlin.Fock

end OAI
