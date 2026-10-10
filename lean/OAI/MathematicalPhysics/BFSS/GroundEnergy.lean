import Mathlib
import OAI.MathematicalPhysics.BFSS.GroundLine

namespace OAI

/-! Spectral quantization and the exact fermionic zero-point energy. -/

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix Finset
open scoped ComplexConjugate
variable {N : ℕ} (M : AlgebraData N)

lemma complexFrequency_spectral_entry (K : FrequencyMatrix N) (hK : K.transpose = -K)
    (r s : FrequencyIndex N) :
    Complex.I*(K r s : ℂ) = ∑ j,
      ((complexFrequency_hermitian K hK).eigenvectorBasis j r)*
      ((complexFrequency_hermitian K hK).eigenvalues j : ℂ)*
      conj ((complexFrequency_hermitian K hK).eigenvectorBasis j s) := by
  let hH := complexFrequency_hermitian K hK
  have he := congrArg (fun A : Matrix (FrequencyIndex N) (FrequencyIndex N) ℂ => A r s)
    hH.spectral_theorem
  change Complex.I*(K r s : ℂ) = ∑ j,
    ((hH.eigenvectorUnitary : Matrix (FrequencyIndex N) (FrequencyIndex N) ℂ)*
      Matrix.diagonal (fun j => (hH.eigenvalues j : ℂ))) r j*
      star (hH.eigenvectorUnitary : Matrix (FrequencyIndex N) (FrequencyIndex N) ℂ) j s at he
  simpa only [Matrix.mul_diagonal,Matrix.star_apply,hH.eigenvectorUnitary_apply,
    RCLike.star_def] using he

lemma thetaMode_product (v w : FrequencyIndex N → ℂ) :
    M.thetaMode v*M.thetaMode w =
      ∑ r : FrequencyIndex N, ∑ s : FrequencyIndex N,
        (v r*w s) • (M.thetaPair r*M.thetaPair s) := by
  unfold thetaMode
  simp only [Finset.sum_mul,Finset.mul_sum,smul_mul_smul]
  rw [Finset.sum_comm]

lemma sum_move_last {J W : Type*} [Fintype J] [AddCommMonoid W] (f : J → J → J → W) :
    (∑ r, ∑ s, ∑ j, f r s j) = ∑ j, ∑ r, ∑ s, f r s j := by
  calc
    _ = ∑ r, ∑ j, ∑ s, f r s j := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

theorem quantizeFrequency_diagonal (K : FrequencyMatrix N) (hK : K.transpose = -K) :
    M.quantizeFrequency K = (1/2 : ℂ) • ∑ j : FrequencyIndex N,
      ((complexFrequency_hermitian K hK).eigenvalues j : ℂ) •
        (M.thetaMode ((complexFrequency_hermitian K hK).eigenvectorBasis j)*
          M.thetaMode (fun r => conj ((complexFrequency_hermitian K hK).eigenvectorBasis j r))) := by
  let hH := complexFrequency_hermitian K hK
  have hsum (f : FrequencyIndex N → ℂ) (T : Fermion N →L[ℂ] Fermion N) :
      (∑ j, f j) • T = ∑ j, f j • T :=
    @Finset.sum_smul (FrequencyIndex N) ℂ (Fermion N →L[ℂ] Fermion N) _ _ _ f Finset.univ T
  have hstart : M.quantizeFrequency K = (1/2:ℂ) •
      ∑ r : FrequencyIndex N, ∑ s : FrequencyIndex N,
        (Complex.I*(K r s : ℂ)) • (M.thetaPair r*M.thetaPair s) := by
    unfold quantizeFrequency
    simp only [Finset.smul_sum,smul_smul]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro s _
    change ((Complex.I/2)*(K r s : ℂ)) • (M.thetaPair r*M.thetaPair s) = _
    congr 1
    ring
  rw [hstart]
  congr 1
  calc
    _ = ∑ r : FrequencyIndex N, ∑ s : FrequencyIndex N, ∑ j : FrequencyIndex N,
        (hH.eigenvectorBasis j r*(hH.eigenvalues j : ℂ)*conj (hH.eigenvectorBasis j s)) •
          (M.thetaPair r*M.thetaPair s) := by
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      rw [complexFrequency_spectral_entry K hK r s]
      exact hsum _ _
    _ = ∑ j : FrequencyIndex N, ∑ r : FrequencyIndex N, ∑ s : FrequencyIndex N,
        (hH.eigenvectorBasis j r*(hH.eigenvalues j : ℂ)*conj (hH.eigenvectorBasis j s)) •
          (M.thetaPair r*M.thetaPair s) := sum_move_last _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [M.thetaMode_product]
      simp only [Finset.smul_sum,smul_smul]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      congr 1
      ring

end
end BFSSQuantum.AlgebraData

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix Finset
open scoped ComplexConjugate
variable {N : ℕ}

lemma complexFrequency_eigenvalues_sum (K : FrequencyMatrix N) (hK : K.transpose = -K) :
    (∑ j, (complexFrequency_hermitian K hK).eigenvalues j) = 0 := by
  classical
  have hz (r : FrequencyIndex N) : K r r = 0 := by
    have h := congrArg (fun A : FrequencyMatrix N => A r r) hK
    change K r r = -K r r at h
    linarith
  have ht : Matrix.trace (complexFrequency K) = 0 := by
    unfold Matrix.trace
    apply Finset.sum_eq_zero
    intro r _
    change Complex.I*(K r r : ℂ) = 0
    rw [hz,Complex.ofReal_zero,mul_zero]
  have hsum := (complexFrequency_hermitian K hK).trace_eq_sum_eigenvalues
  rw [hsum] at ht
  have hreal := congrArg Complex.re ht
  simpa using hreal

lemma negative_sum_eq_abs {J : Type*} [Fintype J] (ev : J → ℝ) (hev : ∑ j, ev j = 0) :
    (∑ j, if ev j < 0 then ev j else 0) = -(1/2:ℝ)*(∑ j, |ev j|) := by
  have h (j : J) : (if ev j < 0 then ev j else 0) = (ev j-|ev j|)/2 := by
    split_ifs with hj
    · rw [abs_of_neg hj]
      ring
    · rw [abs_of_nonneg (not_lt.mp hj)]
      ring
  simp_rw [h]
  rw [←Finset.sum_div,Finset.sum_sub_distrib,hev]
  ring

variable (M : AlgebraData N)

theorem normal_fermion_ground_energy_value (q : Boson N)
    (hq : M.deformedBosonicPotential 1 1 q = 0) (E : ℝ) (u : Fermion N) (hu : u ≠ 0)
    (he : M.quantizeFrequency (M.normalFermionFrequency q) u = (E : ℂ) • u)
    (hmin : ∀ (e : ℝ) (w : Fermion N), w ≠ 0 →
      M.quantizeFrequency (M.normalFermionFrequency q) w = (e : ℂ) • w → E ≤ e) :
    E = -(1/4:ℝ)*∑ j, |(complexFrequency_hermitian (M.normalFermionFrequency q)
      (M.normalFermionFrequency_skew q)).eigenvalues j| := by
  let K := M.normalFermionFrequency q
  have hs := M.normalFermionFrequency_skew q
  let hH := complexFrequency_hermitian K hs
  let b := hH.eigenvectorBasis
  let ev := hH.eigenvalues
  have hn (j : FrequencyIndex N) : (∑ r, b j r*conj (b j r)) = 1 := by
    calc
      _ = inner ℂ (b j) (b j) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct]
        unfold dotProduct
        apply Finset.sum_congr rfl
        intro r _
        simp only [Pi.star_apply,Complex.star_def]
      _ = 1 := by rw [inner_self_eq_norm_sq_to_K,b.orthonormal.1 j]; simp
  have hterm (j : FrequencyIndex N) :
      (ev j : ℂ) • M.thetaMode (b j) (M.thetaMode (fun r => conj (b j r)) u) =
        (if ev j < 0 then (ev j : ℂ) else 0) • u := by
    have hm := complexFrequency_eigenmode K hs j
    by_cases hj : ev j < 0
    · have hk := M.quantizeFrequency_ground_killed K hs E u he hmin (b j) (ev j) hj hm
      have hc := congrArg (fun T : Fermion N →L[ℂ] Fermion N => T u)
        (M.thetaMode_CAR (b j) (fun r => conj (b j r)))
      rw [hn,one_smul] at hc
      simp only [_root_.add_apply,mul_apply_eq_comp,
        one_apply_eq_self] at hc
      change M.thetaMode (b j) (M.thetaMode (fun r => conj (b j r)) u)+
        M.thetaMode (fun r => conj (b j r)) (M.thetaMode (b j) u) = u at hc
      rw [hk,map_zero,add_zero] at hc
      rw [hc,ite_eq_left hj]
    · have hp : 0 < ev j := lt_of_le_of_ne (not_lt.mp hj)
        (Ne.symm (M.normal_frequency_eigenvalues_ne_zero q hq j))
      have hk := M.quantizeFrequency_ground_killed K hs E u he hmin
        (fun r => conj (b j r)) (-ev j) (neg_neg_of_pos hp)
        (complexFrequency_conjugate_mode K (b j) (ev j) hm)
      rw [hk,map_zero,ite_eq_right hj,smul_zero,zero_smul]
  have hd := congrArg (fun T : Fermion N →L[ℂ] Fermion N => T u)
    (M.quantizeFrequency_diagonal K hs)
  simp only [_root_.smul_apply,_root_.sum_apply,
    mul_apply_eq_comp] at hd
  change M.quantizeFrequency K u = (1/2:ℂ) •
    ∑ j : FrequencyIndex N, (ev j : ℂ) •
      M.thetaMode (b j) (M.thetaMode (fun r => conj (b j r)) u) at hd
  simp_rw [hterm] at hd
  have hcast (j : FrequencyIndex N) :
      (if ev j < 0 then (ev j : ℂ) else 0) = ((if ev j < 0 then ev j else 0 : ℝ) : ℂ) := by
    split_ifs <;> rfl
  simp only [hcast,←Finset.sum_smul,←Complex.ofReal_sum,smul_smul] at hd
  have hnegative := negative_sum_eq_abs ev (complexFrequency_eigenvalues_sum K hs)
  rw [hnegative,Complex.ofReal_mul,Complex.ofReal_neg] at hd
  have hco : (1/2:ℂ)*(-(1/2:ℂ)*(∑ j, |ev j| : ℝ)) =
      ((-(1/4:ℝ)*∑ j, |ev j| : ℝ) : ℂ) := by push_cast; ring
  norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] at hd
  rw [hco,he] at hd
  have hz : ((E : ℂ)-((-(1/4:ℝ)*∑ j, |ev j| : ℝ) : ℂ)) • u = 0 := by
    rw [sub_smul,hd,sub_self]
  have hEq := (smul_eq_zero.mp hz).resolve_right hu
  exact Complex.ofReal_injective (sub_eq_zero.mp hEq)

end
end BFSSQuantum.AlgebraData

namespace BFSSQuantum.AlgebraData
noncomputable section
open Matrix Finset
variable {N : ℕ} (M : AlgebraData N)

def normalFermionZeroPoint (q : Boson N) : ℝ :=
  -(1/4:ℝ)*∑ j, |(complexFrequency_hermitian (M.normalFermionFrequency q)
    (M.normalFermionFrequency_skew q)).eigenvalues j|

theorem normal_fermion_ground_exact (q : Boson N)
    (hq : M.deformedBosonicPotential 1 1 q = 0) :
    ∃ u : Fermion N, u ≠ 0 ∧
      M.quantizeFrequency (M.normalFermionFrequency q) u =
        (M.normalFermionZeroPoint q : ℂ) • u ∧
      (∀ (e : ℝ) (w : Fermion N), w ≠ 0 →
        M.quantizeFrequency (M.normalFermionFrequency q) w = (e : ℂ) • w →
        M.normalFermionZeroPoint q ≤ e) ∧
      ∀ z : Fermion N,
        M.quantizeFrequency (M.normalFermionFrequency q) z =
          (M.normalFermionZeroPoint q : ℂ) • z ↔ z ∈ Submodule.span ℂ {u} := by
  obtain ⟨E,u,hu,he,hm,hl⟩ := M.normal_fermion_ground_line q hq
  have hv : E = M.normalFermionZeroPoint q :=
    M.normal_fermion_ground_energy_value q hq E u hu he hm
  subst E
  exact ⟨u,hu,he,hm,hl⟩

end
end BFSSQuantum.AlgebraData

end OAI
