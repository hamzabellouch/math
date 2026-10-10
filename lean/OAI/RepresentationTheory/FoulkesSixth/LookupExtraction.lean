import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.Lookup

namespace OAI

noncomputable section

namespace Foulkes.Lookup
open MvPolynomial Finset Foulkes.Strips

lemma strictAnti_gap {n : ℕ} {v : Fin n → ℕ} (hv : StrictAnti v)
    (j k : Fin n) (hjk : j ≤ k) : v k + k.val ≤ v j + j.val := by
  have hh : ∀ t, j.val ≤ t → ∀ ht : t < n, v ⟨t,ht⟩ + t ≤ v j + j.val := by
    intro t hjt
    induction t, hjt using Nat.le_induction with
    | base => intro ht; simp
    | succ t hjt ih =>
      intro ht
      have ht' : t < n := by omega
      have hstep := hv (show (⟨t,ht'⟩ : Fin n) < ⟨t+1,ht⟩ from by simp)
      have hprev := ih ht'
      omega
  exact hh k.val hjk k.isLt

lemma staircase_le_of_strictAnti {n : ℕ} {v : Fin n → ℕ} (hv : StrictAnti v)
    (j : Fin n) : staircase n j ≤ v j := by
  have hn : 0 < n := Nat.zero_lt_of_lt j.isLt
  let k : Fin n := ⟨n-1, by omega⟩
  have hjk : j ≤ k := by change j.val ≤ n-1; omega
  have hh := strictAnti_gap hv j k hjk
  simp only [k, staircase] at *
  omega

lemma sortedPartition_antitone {n : ℕ} (v : Fin n → ℕ) (hv : Function.Injective v) :
    Antitone (sortedPartition v) := by
  intro j k hjk
  have hs := sortDesc_strict v hv
  have hg := strictAnti_gap hs j k hjk
  have hj := staircase_le_of_strictAnti hs j
  have hk := staircase_le_of_strictAnti hs k
  simp only [sortedPartition, staircase, Function.comp_apply] at *
  have hjn := j.isLt
  have hkn := k.isLt
  omega

lemma shifted_sortedPartition {n : ℕ} (v : Fin n → ℕ) (hv : Function.Injective v) :
    shifted (sortedPartition v) = v ∘ sortDesc v := by
  funext j
  exact Nat.sub_add_cancel (staircase_le_of_strictAnti (sortDesc_strict v hv) j)

def signedLookup {n : ℕ} (f : (Fin n → ℕ) → ℤ) (v : Fin n → ℤ) : ℤ := by
  classical
  exact if hn : ∀ j, 0 ≤ v j then
    let w := fun j => (v j).toNat
    if Function.Injective w then
      (Equiv.Perm.sign (sortDesc w) : ℤ) * f (sortedPartition w)
    else 0
  else 0

def coeffZ {n : ℕ} (v : Fin n → ℤ) (p : MvPolynomial (Fin n) ℤ) : ℤ := by
  classical
  exact if ∀ j, 0 ≤ v j then p.coeff (expVector (fun j => (v j).toNat)) else 0

theorem signedLookup_eq_coeffZ {n : ℕ} (p : MvPolynomial (Fin n) ℤ)
    (hp : ∀ σ : Equiv.Perm (Fin n), rename σ p = p) (v : Fin n → ℤ) :
    signedLookup (schurCoeff p) v = coeffZ v (p * alternant (staircase n)) := by
  classical
  unfold signedLookup coeffZ
  by_cases hn : ∀ j, 0 ≤ v j
  · simp only [dite_eq_left hn, ite_eq_left hn]
    let w := fun j => (v j).toNat
    change (if Function.Injective w then _ else _) = _
    have ha := alternating_mul_symmetric hp (alternant_alternating (staircase n))
    by_cases hw : Function.Injective w
    · rw [ite_eq_left hw]
      unfold schurCoeff
      rw [shifted_sortedPartition w hw]
      exact (coeff_eq_sign_mul_comp ha w (sortDesc w)).symm
    · rw [ite_eq_right hw]
      obtain ⟨j,k,he,hjk⟩ := Function.not_injective_iff.mp hw
      exact (coeff_repeated ha w hjk he).symm
  · simp only [dite_eq_right hn, ite_eq_right hn]

lemma coeffZ_monomial_mul {n : ℕ} (l : Fin n → ℕ) (d : Fin n →₀ ℕ)
    (p : MvPolynomial (Fin n) ℤ) :
    (monomial d 1 * p).coeff (expVector l) =
      coeffZ (fun j => (l j : ℤ) - d j) p := by
  classical
  rw [coeff_monomial_mul']
  unfold coeffZ
  have hiff : d ≤ expVector l ↔ ∀ j, 0 ≤ (l j : ℤ) - d j := by
    simp [Finsupp.le_def, expVector]
  by_cases hd : d ≤ expVector l
  · rw [ite_eq_left hd, ite_eq_left (hiff.mp hd), one_mul]
    congr 1
    ext j
    simp [expVector]
  · rw [ite_eq_right hd, ite_eq_right (mt hiff.mpr hd)]

theorem target_newton (n b : ℕ) (mu : Fin n → ℕ) :
    (b : ℤ) * Q n b mu =
      ∑ i ∈ Finset.Icc 1 b, ∑ d : Complete.Degree (Fin n) 6,
        signedLookup (Q n (b-i))
          (fun j => (shifted mu j : ℤ) - (i : ℤ) * d.val j) := by
  have hh := congrArg
    (fun p : MvPolynomial (Fin n) ℤ =>
      (p * alternant (staircase n)).coeff (expVector (shifted mu)))
    (Complete.pleth_newton n b 6)
  change (((b : ℤ) • Complete.pleth n b 6) * alternant (staircase n)).coeff
      (expVector (shifted mu)) = _ at hh
  rw [smul_mul_assoc, coeff_smul] at hh
  simp only [Finset.sum_mul, coeff_sum, zsmul_eq_mul] at hh
  change (b : ℤ) * Q n b mu = _ at hh
  rw [hh]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro d hd
  rw [mul_assoc, coeffZ_monomial_mul]
  have he : (fun j : Fin n => (shifted mu j : ℤ) - ((i • d.val) j : ℕ)) =
      (fun j => (shifted mu j : ℤ) - (i : ℤ) * d.val j) := by
    funext j
    simp
  rw [he]
  exact (signedLookup_eq_coeffZ (Complete.pleth n (b-i) 6)
    (Complete.rename_pleth n (b-i) 6) _).symm

end Foulkes.Lookup

end

end OAI
