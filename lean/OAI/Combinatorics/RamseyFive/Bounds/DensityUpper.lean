import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.Q

namespace OAI

namespace SharpRamseyFive.ProjectiveIncidence
open Module
open scoped Classical LinearAlgebra.Projectivization BigOperators
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V]
  [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

lemma density_upper {d : ℕ} (hd : 1 ≤ d) :
    (Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d ≤ 1/(Nat.card K:ℝ) := by
  have hq : (0:ℝ) < Nat.card K := by exact_mod_cast (Finite.one_lt_card (α:=K)).le
  have hQ : (0:ℝ) < Q (Nat.card K) d := by exact_mod_cast Q_pos (Nat.card K) d
  have hrec : (Q (Nat.card K) d:ℝ)=Nat.card K*Q (Nat.card K) (d-1)+1 := by
    exact_mod_cast Q_recurrence (q:=Nat.card K) hd
  apply (div_le_div_iff₀ hQ hq).mpr
  nlinarith

theorem incidence_rectangle_sqrt (hdim : finrank K V=5)
    (A : Finset (ℙ K V)) (B : Finset (ℙ K (Dual K V))) (C : ℝ)
    (hC : 0 ≤ C) (hcap : (A.card:ℝ)*B.card ≤ C^2*(Nat.card K:ℝ)^5) :
    (incidences A B:ℝ) ≤ (C+1)*Real.sqrt ((Nat.card K:ℝ)^3*A.card*B.card) := by
  let q : ℝ := Nat.card K
  let z : ℝ := (A.card:ℝ)*B.card
  let s : ℝ := Real.sqrt (q^3*z)
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  have hz : 0 ≤ z := by dsimp [z];positivity
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s^2=q^3*z := Real.sq_sqrt (by positivity)
  have hz2 : z^2 ≤ (C*q*s)^2 := by
    calc
      _ = z*z := by ring
      _ ≤ (C^2*q^5)*z := mul_le_mul_of_nonneg_right hcap hz
      _ = _ := by rw [mul_pow,mul_pow,hsq];ring
  have hzbound : z/q ≤ C*s := by
    apply (div_le_iff₀ hq).mpr
    simpa [mul_assoc,mul_left_comm,mul_comm] using (sq_le_sq₀ hz (by positivity)).mp hz2
  have hdens := mul_le_mul_of_nonneg_right (density_upper (K:=K) (d:=4) (by omega)) hz
  have hm := (abs_le.mp (incidence_mixing (d:=4) hdim (by omega) A B)).2
  change (incidences A B:ℝ)-(Q (Nat.card K) 3:ℝ)/Q (Nat.card K) 4*A.card*B.card ≤ _ at hm
  have he : Real.sqrt ((Nat.card K:ℝ)^(4-1)*A.card*B.card)=s := by simp [s,q,z,mul_assoc]
  rw [he] at hm
  change (Q (Nat.card K) (4-1):ℝ)/Q (Nat.card K) 4*z ≤ 1/q*z at hdens
  have hdens' : (Q (Nat.card K) 3:ℝ)/Q (Nat.card K) 4*A.card*B.card ≤ z/q := by
    simpa [z,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hdens
  have hc : (incidences A B:ℝ) ≤ (C+1)*s := by nlinarith
  simpa [s,q,z,mul_assoc] using hc

theorem incidence_rectangle_log (hdim : finrank K V=5)
    (A : Finset (ℙ K V)) (B : Finset (ℙ K (Dual K V))) (C : ℝ)
    (hC : 0 ≤ C) (hcap : (A.card:ℝ)*B.card ≤ C^2*(Nat.card K:ℝ)^5)
    (hA : 0 < A.card) (hB : 0 < B.card) (hI : 0 < incidences A B) :
    Real.log (incidences A B:ℝ) ≤ Real.log (C+1)+(3:ℝ)/2*Real.log (Nat.card K)+
      (Real.log (A.card:ℝ)+Real.log (B.card:ℝ))/2 := by
  have hq : (0:ℝ) < Nat.card K := by exact_mod_cast (Finite.one_lt_card (α:=K)).le
  have hAr : (0:ℝ) < A.card := by exact_mod_cast hA
  have hBr : (0:ℝ) < B.card := by exact_mod_cast hB
  have hIr : (0:ℝ) < incidences A B := by exact_mod_cast hI
  have hs : (0:ℝ) < (Nat.card K:ℝ)^3*A.card*B.card := by positivity
  have hh := Real.log_le_log hIr (incidence_rectangle_sqrt hdim A B C hC hcap)
  rw [Real.log_mul (by linarith : C+1≠0) (Real.sqrt_pos.mpr hs).ne',Real.log_sqrt hs.le,
    Real.log_mul (mul_pos (pow_pos hq _) hAr).ne' hBr.ne',
    Real.log_mul (pow_pos hq _).ne' hAr.ne',Real.log_pow] at hh
  nlinarith

end SharpRamseyFive.ProjectiveIncidence

end OAI
