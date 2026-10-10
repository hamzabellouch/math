import Mathlib
import OAI.RepresentationTheory.FoulkesSixth.AlternantExpansion

namespace OAI

noncomputable section

namespace Foulkes.Complete
open MvPolynomial Finset

lemma homogeneous_h {α : Type*} [Finite α] (b : ℕ) : (h α b).IsHomogeneous b := by
  classical
  apply IsHomogeneous.sum
  intro d hd
  exact isHomogeneous_monomial 1 d.property

lemma homogeneous_pleth (n b a : ℕ) : (pleth n b a).IsHomogeneous (a*b) := by
  unfold pleth alphabetH
  apply (homogeneous_h b).eval₂
  · intro r
    change (C r : MvPolynomial (Fin n) ℤ).IsHomogeneous 0
    exact isHomogeneous_C _ _
  · intro d
    exact isHomogeneous_monomial 1 d.property

end Foulkes.Complete

namespace Foulkes.Lookup
open MvPolynomial Finset Foulkes.Strips

lemma degree_expVector {n : ℕ} (v : Fin n → ℕ) :
    (expVector v).degree = ∑ j, v j := by
  simpa using Finsupp.degree_eq_sum (expVector v)

lemma homogeneous_alternant {n : ℕ} (m : Fin n → ℕ) :
    (alternant m).IsHomogeneous (∑ j, m j) := by
  classical
  have ha : alternant m = ∑ σ : Equiv.Perm (Fin n),
      Equiv.Perm.sign σ • ∏ c, (X (σ c) : MvPolynomial (Fin n) ℤ) ^ m c :=
    Matrix.det_apply _
  rw [ha]
  apply IsHomogeneous.sum
  intro σ hσ
  rw [perm_prod_monomial]
  change ((Equiv.Perm.sign σ : ℤ) • monomial (expVector (fun r => m (σ.symm r))) 1).IsHomogeneous _
  rw [smul_monomial]
  apply isHomogeneous_monomial
  rw [degree_expVector, Equiv.sum_comp σ.symm m]

abbrev Partition (n d : ℕ) :=
  {e : Complete.Degree (Fin n) d // Antitone (fun j => e.val j)}

instance (n d : ℕ) : Fintype (Partition n d) := by
  classical
  infer_instance

def partVec {n d : ℕ} (mu : Partition n d) (j : Fin n) : ℕ := mu.val.val j

lemma partVec_antitone {n d : ℕ} (mu : Partition n d) : Antitone (partVec mu) := mu.property

lemma partVec_sum {n d : ℕ} (mu : Partition n d) : ∑ j, partVec mu j = d := by
  change (∑ j, mu.val.val j) = d
  rw [← Finsupp.degree_eq_sum]
  exact mu.val.property

def unshift {n : ℕ} (v : Fin n → ℕ) (j : Fin n) : ℕ := v j - staircase n j

lemma unshift_antitone {n : ℕ} {v : Fin n → ℕ} (hv : StrictAnti v) :
    Antitone (unshift v) := by
  intro j k hjk
  have hg := strictAnti_gap hv j k hjk
  have hj := staircase_le_of_strictAnti hv j
  have hk := staircase_le_of_strictAnti hv k
  simp only [unshift, staircase] at *
  have hjn := j.isLt
  have hkn := k.isLt
  omega

lemma shifted_unshift {n : ℕ} {v : Fin n → ℕ} (hv : StrictAnti v) :
    shifted (unshift v) = v := by
  funext j
  exact Nat.sub_add_cancel (staircase_le_of_strictAnti hv j)

lemma unshift_sum {n d : ℕ} {v : Fin n → ℕ} (hv : StrictAnti v)
    (hd : ∑ j, v j = d + ∑ j, staircase n j) : ∑ j, unshift v j = d := by
  have hh : (∑ j, unshift v j) + ∑ j, staircase n j = ∑ j, v j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => congrFun (shifted_unshift hv) j)
  omega

def unshiftPartition {n d : ℕ} {v : Fin n → ℕ} (hv : StrictAnti v)
    (hd : ∑ j, v j = d + ∑ j, staircase n j) : Partition n d :=
  ⟨⟨expVector (unshift v), by rw [degree_expVector]; exact unshift_sum hv hd⟩,
    unshift_antitone hv⟩

lemma partVec_injective {n d : ℕ} : Function.Injective (@partVec n d) := by
  intro v w h
  apply Subtype.ext
  apply Subtype.ext
  ext j
  exact congrFun h j

lemma shifted_injective {n : ℕ} : Function.Injective (@shifted n) := by
  intro v w h
  funext j
  exact Nat.add_right_cancel (congrFun h j)

theorem homogeneous_schur_expansion {n d : ℕ} (p : MvPolynomial (Fin n) ℤ)
    (hp : ∀ σ : Equiv.Perm (Fin n), rename σ p = p) (hd : p.IsHomogeneous d) :
    p * alternant (staircase n) =
      ∑ mu : Partition n d, schurCoeff p (partVec mu) • alternant (shifted (partVec mu)) := by
  classical
  apply eq_of_strict_coefficients
    (alternating_mul_symmetric hp (alternant_alternating _))
    (alternating_sum _ _ (fun _ _ => alternating_smul _ (alternant_alternating _)))
  intro v hv
  simp only [coeff_sum, coeff_smul]
  by_cases hsize : ∑ j, v j = d + ∑ j, staircase n j
  · let mu : Partition n d := unshiftPartition hv hsize
    have he : shifted (partVec mu) = v := shifted_unshift hv
    rw [Finset.sum_eq_single mu]
    · rw [coeff_alternant_strict _ _ (shifted_strictAnti (partVec_antitone mu)) hv, ite_eq_left he]
      simp only [smul_eq_mul, mul_one, schurCoeff, he]
    · intro nu hnu hne
      rw [coeff_alternant_strict _ _ (shifted_strictAnti (partVec_antitone nu)) hv]
      have hn : shifted (partVec nu) ≠ v := by
        intro hh
        exact hne (partVec_injective (shifted_injective (hh.trans he.symm)))
      simp [hn]
    · simp
  · have hgrad := hd.mul (homogeneous_alternant (staircase n))
    rw [hgrad.coeff_eq_zero (by simpa [degree_expVector] using hsize)]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro mu hmu
    rw [coeff_alternant_strict _ _ (shifted_strictAnti (partVec_antitone mu)) hv]
    have hn : shifted (partVec mu) ≠ v := by
      intro hh
      apply hsize
      rw [← hh]
      simp only [shifted, Finset.sum_add_distrib, partVec_sum]
    simp [hn]

end Foulkes.Lookup

end

end OAI
