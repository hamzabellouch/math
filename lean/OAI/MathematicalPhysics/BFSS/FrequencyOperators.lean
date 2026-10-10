import Mathlib
import OAI.MathematicalPhysics.BFSS.FermionQuantization

namespace OAI

/-! Quantized-frequency commutators and self-adjointness. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix Finset
variable {N : ℕ} (M : AlgebraData N)

def thetaPair (r : FrequencyIndex N) : Fermion N →L[ℂ] Fermion N := M.theta r.1 r.2

lemma thetaPair_CAR (r s : FrequencyIndex N) :
    M.thetaPair r*M.thetaPair s+M.thetaPair s*M.thetaPair r =
      if r = s then 1 else 0 := by
  rw [thetaPair,thetaPair,M.theta_CAR]
  by_cases h : r = s
  · subst s
    simp
  · have hh : ¬(r.1 = s.1 ∧ r.2 = s.2) := fun hh => h (Prod.ext hh.1 hh.2)
    simp only [ite_eq_right h,ite_eq_right hh]
    exact zero_smul ℕ (1 : Fermion N →L[ℂ] Fermion N)

lemma thetaPair_product_commutator (r s t : FrequencyIndex N) :
    (M.thetaPair r*M.thetaPair s)*M.thetaPair t-
      M.thetaPair t*(M.thetaPair r*M.thetaPair s) =
      (if s = t then M.thetaPair r else 0) -
        (if r = t then M.thetaPair s else 0) := by
  calc
    _ = M.thetaPair r*(M.thetaPair s*M.thetaPair t+M.thetaPair t*M.thetaPair s)-
        (M.thetaPair r*M.thetaPair t+M.thetaPair t*M.thetaPair r)*M.thetaPair s := by
      noncomm_ring
    _ = _ := by
      rw [M.thetaPair_CAR,M.thetaPair_CAR]
      split_ifs <;> simp_all only [mul_one,one_mul,mul_zero,zero_mul,sub_self]

theorem quantizeFrequency_commutator (K : FrequencyMatrix N) (hK : K.transpose = -K)
    (t : FrequencyIndex N) :
    M.quantizeFrequency K*M.thetaPair t-M.thetaPair t*M.quantizeFrequency K =
      Complex.I • ∑ r : FrequencyIndex N, (K r t : ℂ) • M.thetaPair r := by
  have hdist (c : ℂ) (A B : Fermion N →L[ℂ] Fermion N) :
      (c • A)*B-B*(c • A) = c • (A*B-B*A) := by
    calc
      _ = c • (A*B)-c • (B*A) := by rw [smul_mul_assoc,mul_smul_comm]
      _ = _ := (smul_sub c (A*B) (B*A)).symm
  have he : K t = fun r => -K r t := by
    funext r
    have h := congrArg (fun A : FrequencyMatrix N => A r t) hK
    exact h
  have hd (r s : FrequencyIndex N) :
      ((K r s : ℂ) • (M.thetaPair r*M.thetaPair s))*M.thetaPair t-
        M.thetaPair t*((K r s : ℂ) • (M.thetaPair r*M.thetaPair s)) =
        (K r s : ℂ) • ((if s = t then M.thetaPair r else 0)-
          (if r = t then M.thetaPair s else 0)) := by
    rw [hdist,M.thetaPair_product_commutator]
  have hs : (∑ r : FrequencyIndex N, ∑ s : FrequencyIndex N,
      (K r s : ℂ) • ((if s = t then M.thetaPair r else 0)-
        (if r = t then M.thetaPair s else 0))) =
      (∑ r : FrequencyIndex N, (K r t : ℂ) • M.thetaPair r)-
        (∑ r : FrequencyIndex N, (K t r : ℂ) • M.thetaPair r) := by
    simp only [smul_sub,Finset.sum_sub_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_eq_single t]
      · rw [ite_eq_left rfl]
      · intro s _ hst
        simp only [ite_eq_right hst,smul_zero]
      · simp
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      rw [Finset.sum_eq_single t]
      · rw [ite_eq_left rfl]
      · intro r _ hrt
        simp only [ite_eq_right hrt,smul_zero]
      · simp
  change ((Complex.I/2) • (∑ r, ∑ s, (K r s : ℂ) •
      (M.thetaPair r*M.thetaPair s)))*M.thetaPair t-
      M.thetaPair t*((Complex.I/2) • (∑ r, ∑ s, (K r s : ℂ) •
      (M.thetaPair r*M.thetaPair s))) = _
  rw [hdist]
  simp only [Finset.sum_mul,Finset.mul_sum,←Finset.sum_sub_distrib,hd]
  have hneg (c : ℂ) (A : Fermion N →L[ℂ] Fermion N) :
      (-c) • A = -(c • A) := neg_smul c A
  have hn : (∑ r : FrequencyIndex N, (K t r : ℂ) • M.thetaPair r) =
      -(∑ r : FrequencyIndex N, (K r t : ℂ) • M.thetaPair r) := by
    rw [he]
    simp only [Complex.ofReal_neg,hneg,Finset.sum_neg_distrib]
  rw [hs,hn,sub_neg_eq_add]
  module

end
end BFSSQuantum.AlgebraData

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix Finset
variable {N : ℕ} (M : AlgebraData N)

lemma thetaPair_star (r : FrequencyIndex N) : star (M.thetaPair r) = M.thetaPair r :=
  M.theta_selfAdjoint r.1 r.2

theorem quantizeFrequency_selfAdjoint (K : FrequencyMatrix N) (hK : K.transpose = -K) :
    IsSelfAdjoint (M.quantizeFrequency K) := by
  have hn (r s : FrequencyIndex N) : K s r = -K r s :=
    congrArg (fun A : FrequencyMatrix N => A r s) hK
  have hstar (c : ℂ) (A : Fermion N →L[ℂ] Fermion N) :
      star (c • A) = star c • star A := star_smul c A
  have hss (f : FrequencyIndex N → (Fermion N →L[ℂ] Fermion N)) :
      star (∑ r, f r) = ∑ r, star (f r) := star_sum Finset.univ f
  have hp (A B : Fermion N →L[ℂ] Fermion N) : star (A*B) = star B*star A := star_mul A B
  have hneg (c : ℂ) (A : Fermion N →L[ℂ] Fermion N) :
      (-c) • A = -(c • A) := neg_smul c A
  have hr (c : ℝ) : star (c : ℂ) = (c : ℂ) := by simp
  have hi : star (Complex.I/2) = -(Complex.I/2) := by simp; ring
  have hs : (∑ r : FrequencyIndex N, ∑ s : FrequencyIndex N,
      (K r s : ℂ) • (M.thetaPair s*M.thetaPair r)) =
      -(∑ r : FrequencyIndex N, ∑ s : FrequencyIndex N,
        (K r s : ℂ) • (M.thetaPair r*M.thetaPair s)) := by
    rw [Finset.sum_comm]
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r _
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s _
    rw [hn r s,Complex.ofReal_neg,hneg]
  change star ((Complex.I/2) • (∑ r : FrequencyIndex N, ∑ s : FrequencyIndex N,
    (K r s : ℂ) • (M.thetaPair r*M.thetaPair s))) = _
  simp only [hstar,hss,hp,M.thetaPair_star,hr,hi]
  rw [hs]
  change -(Complex.I/2) • (-_) = (Complex.I/2) • _
  exact neg_smul_neg _ _

end
end BFSSQuantum.AlgebraData

end OAI
