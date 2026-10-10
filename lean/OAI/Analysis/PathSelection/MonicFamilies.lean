import Mathlib

namespace OAI

/-! Monic polynomial families and scalar specialization. -/

noncomputable section
open Set Filter Topology Metric Polynomial
open scoped BigOperators NNReal ENNReal

open Set Metric Filter Topology Complex Polynomial
open scoped BigOperators
namespace DegeneratingTrees

def monicFamily {R : Type*} [Semiring R] {d : ℕ} (c : Fin d → R) : R[X] :=
  X^d + ∑ i : Fin d, monomial (i : ℕ) (c i)

lemma monicFamily_coeff {R : Type*} [Semiring R] {d : ℕ} (c : Fin d → R) (n : ℕ) :
    (monicFamily c).coeff n = if hn : n < d then c ⟨n,hn⟩ else if n = d then 1 else 0 := by
  classical
  simp only [monicFamily,coeff_add,coeff_X_pow,finsetSum_coeff,coeff_monomial]
  by_cases hn : n < d
  · rw [dite_eq_left hn,ite_eq_right (ne_of_lt hn)]
    rw [Finset.sum_eq_single (⟨n,hn⟩ : Fin d)]
    · simp
    · intro j hj hjn
      have hjv : (j : ℕ) ≠ n := fun h => hjn (Fin.ext h)
      simp [hjv]
    · simp
  · rw [dite_eq_right hn]
    have hs : ∑ i : Fin d, (if (i : ℕ) = n then c i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hne : (i : ℕ) ≠ n := by
        intro he
        exact hn (he ▸ i.isLt)
      simp [hne]
    rw [hs,add_zero]

lemma monicFamily_natDegree_le {R : Type*} [Semiring R] {d : ℕ} (c : Fin d → R) :
    (monicFamily c).natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  simp [monicFamily_coeff,not_lt.mpr hn.le,ne_of_gt hn]

lemma monicFamily_monic {R : Type*} [Semiring R] {d : ℕ} (c : Fin d → R) :
    (monicFamily c).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one d (monicFamily_natDegree_le c)
    (by simp [monicFamily_coeff])

lemma monicFamily_natDegree {R : Type*} [Semiring R] [Nontrivial R] {d : ℕ}
    (c : Fin d → R) : (monicFamily c).natDegree = d :=
  natDegree_eq_of_le_of_coeff_ne_zero (monicFamily_natDegree_le c)
    (by simp [monicFamily_coeff])

lemma eq_monicFamily {R : Type*} [Semiring R] {P : R[X]} (hP : P.Monic) :
    P = monicFamily (fun i : Fin P.natDegree => P.coeff i) := by
  ext n
  rw [monicFamily_coeff]
  split_ifs with hn hd
  · rfl
  · subst n; exact hP.coeff_natDegree
  · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_ne (Nat.le_of_not_gt hn) (Ne.symm hd))

lemma monicFamily_eval {R : Type*} [Semiring R] {d : ℕ} (c : Fin d → R) (z : R) :
    (monicFamily c).eval z = z^d + ∑ i : Fin d, c i * z^(i : ℕ) := by
  simp [monicFamily,eval_finsetSum,eval_X_pow]

lemma monicFamily_eval_analytic {d : ℕ} (c : Fin d → ℂ) (a : ℂ) :
    AnalyticAt ℂ (fun x : (Fin d → ℂ) × ℂ =>
      (monicFamily (fun i => c i + x.1 i)).eval (x.2 + a)) 0 := by
  simp only [monicFamily_eval]
  apply AnalyticAt.add
  · exact (analyticAt_snd.add analyticAt_const).pow d
  · apply Finset.analyticAt_fun_sum
    intro i hi
    have hcoord : AnalyticAt ℂ (fun x : (Fin d → ℂ) × ℂ => x.1 i) 0 :=
      ((ContinuousLinearMap.proj i : (Fin d → ℂ) →L[ℂ] ℂ).analyticAt _).comp analyticAt_fst
    exact (analyticAt_const.add hcoord).mul ((analyticAt_snd.add analyticAt_const).pow i.val)

 
lemma taylor_coeff_penultimate {R : Type*} [CommRing R] {P : R[X]}
    (hP : P.Monic) (hd : 0 < P.natDegree) (r : R) :
    (taylor r P).coeff (P.natDegree-1) = P.coeff (P.natDegree-1) + (P.natDegree : R)*r := by
  let d := P.natDegree
  have hD : P = monicFamily (fun i : Fin d => P.coeff i) := eq_monicFamily hP
  have htrans := congrArg (taylor r) hD
  rw [htrans]
  simp only [monicFamily,map_add,map_sum,taylor_X_pow,taylor_monomial,coeff_add,
    finsetSum_coeff,coeff_C_mul,coeff_X_add_C_pow]
  have hchoose : d.choose (d-1) = d := by
    obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (show d ≠ 0 from Nat.ne_of_gt hd)
    rw [hn]
    simp
  have hsub : d - (d-1) = 1 := by omega
  have hs : ∑ i : Fin d, P.coeff i * (r ^ ((i : ℕ) - (d-1)) *
      ((i : ℕ).choose (d-1) : R)) = P.coeff (d-1) := by
    rw [Finset.sum_eq_single (⟨d-1,by omega⟩ : Fin d)]
    · simp
    · intro i hi hine
      have hil : (i : ℕ) < d-1 := by
        have := i.isLt
        have hne : (i : ℕ) ≠ d-1 := fun he => hine (Fin.ext he)
        omega
      simp [Nat.choose_eq_zero_of_lt hil]
    · simp
  change r^(d-(d-1)) * (d.choose (d-1) : R) + _ = _
  rw [hchoose,hsub,pow_one,hs]
  ring

end DegeneratingTrees
end

end OAI
