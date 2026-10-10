import OAI.Analysis.Mahler.WedgeUnit

namespace OAI

namespace Mahler
variable {E J : Type*} [AddCommGroup E] [Module ℝ E] [Fintype J]

def twoOnePermutation : Equiv.Perm (Fin 3) :=
  (finSumFinEquiv (m := 2) (n := 1)).symm.trans
    ((Equiv.sumComm (Fin 2) (Fin 1)).trans finSumFinEquiv)

lemma twoOnePermutation_sign : Equiv.Perm.sign twoOnePermutation = 1 := by decide

lemma wedge_two_one_fin (basis : Module.Basis J ℝ E)
    (A : E [⋀^Fin 2]→ₗ[ℝ] ℂ) (a : E [⋀^Fin 1]→ₗ[ℝ] ℂ) :
    (wedge A a).domDomCongr finSumFinEquiv =
      (wedge a A).domDomCongr finSumFinEquiv := by
  have h := congrArg (fun C : E [⋀^Fin 1 ⊕ Fin 2]→ₗ[ℝ] ℂ =>
    C.domDomCongr finSumFinEquiv) (wedge_swap basis A a)
  rw [← AlternatingMap.domDomCongr_trans] at h
  have he : (Equiv.sumComm (Fin 2) (Fin 1)).trans finSumFinEquiv =
      (finSumFinEquiv (m := 2) (n := 1)).trans twoOnePermutation := by
    ext i
    simp [twoOnePermutation]
  rw [he, AlternatingMap.domDomCongr_trans, AlternatingMap.domDomCongr_perm,
    twoOnePermutation_sign, one_smul] at h
  exact h

def derivativeLeftEquiv (n : ℕ) : Fin 3 ⊕ Fin n ≃ Fin (2+n+1) :=
  finSumFinEquiv.trans (finCongr (by omega))

def derivativeRightEquiv (n : ℕ) : Fin 2 ⊕ Fin (n+1) ≃ Fin (2+n+1) :=
  finSumFinEquiv.trans (finCongr (by omega))

lemma wedge_derivative_assoc (basis : Module.Basis J ℝ E) {n : ℕ}
    (a : E [⋀^Fin 1]→ₗ[ℝ] ℂ) (A : E [⋀^Fin 2]→ₗ[ℝ] ℂ)
    (B : E [⋀^Fin n]→ₗ[ℝ] ℂ) :
    (wedge a ((wedge A B).domDomCongr finSumFinEquiv)).domDomCongr
        (prependFinEquiv (2+n)) =
      (wedge ((wedge a A).domDomCongr (prependFinEquiv 2)) B).domDomCongr
        (derivativeLeftEquiv n) := by
  have h1 := wedge_reindex basis (Equiv.refl (Fin 1))
    (finSumFinEquiv (m := 2) (n := n)) a (wedge A B)
  have h2 := wedge_reindex basis (prependFinEquiv 2) (Equiv.refl (Fin n))
    (wedge a A) B
  simp only [AlternatingMap.domDomCongr_refl] at h1 h2
  rw [← h1, ← h2, ← AlternatingMap.domDomCongr_trans,
    ← AlternatingMap.domDomCongr_trans, ← wedge_assoc basis,
    ← AlternatingMap.domDomCongr_trans]
  congr 1
  ext i
  rcases i with (i | i) | i
  · fin_cases i ; rfl
  · fin_cases i <;> rfl
  · simp [derivativeLeftEquiv, prependFinEquiv, finSumFinEquiv]
    omega

lemma wedge_derivative_move_two (basis : Module.Basis J ℝ E) {n : ℕ}
    (a : E [⋀^Fin 1]→ₗ[ℝ] ℂ) (A : E [⋀^Fin 2]→ₗ[ℝ] ℂ)
    (B : E [⋀^Fin n]→ₗ[ℝ] ℂ) :
    (wedge a ((wedge A B).domDomCongr finSumFinEquiv)).domDomCongr
        (prependFinEquiv (2+n)) =
      (wedge A ((wedge a B).domDomCongr (prependFinEquiv n))).domDomCongr
        (derivativeRightEquiv n) := by
  rw [wedge_derivative_assoc basis]
  have hp : prependFinEquiv 2 = (finSumFinEquiv (m := 1) (n := 2)) := by
    ext i
    cases i with
    | inl i => fin_cases i; rfl
    | inr i => fin_cases i <;> rfl
  rw [hp, ← wedge_two_one_fin basis]
  have h1 := wedge_reindex basis (finSumFinEquiv (m := 2) (n := 1))
    (Equiv.refl (Fin n)) (wedge A a) B
  have h2 := wedge_reindex basis (Equiv.refl (Fin 2)) (prependFinEquiv n) A (wedge a B)
  simp only [AlternatingMap.domDomCongr_refl] at h1 h2
  rw [← h1, ← h2, ← AlternatingMap.domDomCongr_trans,
    ← AlternatingMap.domDomCongr_trans, ← wedge_assoc basis,
    ← AlternatingMap.domDomCongr_trans]
  congr 1
  ext i
  rcases i with (i | i) | i
  · fin_cases i <;> rfl
  · fin_cases i ; rfl
  · change 3 + i.val = 2 + (i.val + 1)
    omega

end Mahler

end OAI
