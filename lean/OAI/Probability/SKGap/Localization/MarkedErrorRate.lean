import Mathlib
import OAI.Probability.SKGap.Localization.ProjectedMarkedIBP

namespace OAI

section
noncomputable section
namespace SKGap
open Real
open scoped NNReal ENNReal

lemma power_tail_absorptions (k : ℕ) {c n p : ℝ} (hc : 0<c) (hn : 0<n)
    (hp : p≤3*exp (-c*n)) :
    n^k*p≤(3*((k+1).factorial:ℝ)/c^(k+1))/n ∧
      n^k*sqrt p≤(sqrt 3*((k+1).factorial:ℝ)/(c/2)^(k+1))/n := by
  have h1 := power_exponential_bound (k+1) hc hn.le
  have h2 := power_exponential_bound (k+1) (half_pos hc) hn.le
  have hsp : sqrt p≤ sqrt 3*exp (-(c/2)*n) := by
    apply (sqrt_le_sqrt hp).trans_eq
    rw [sqrt_mul (by norm_num : (0:ℝ)≤3),← exp_half]
    congr 2
    ring
  constructor
  · apply (le_div_iff₀ hn).mpr
    have hh := mul_le_mul_of_nonneg_left hp (pow_nonneg hn.le (k+1))
    calc
      n^k*p*n=n^(k+1)*p := by rw [pow_succ];ring
      _ ≤ n^(k+1)*(3*exp (-c*n)) := hh
      _ = 3*(n^(k+1)*exp (-c*n)) := by ring
      _ ≤ 3*(((k+1).factorial:ℝ)/c^(k+1)) := mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = _ := by ring
  · apply (le_div_iff₀ hn).mpr
    calc
      n^k*sqrt p*n=n^(k+1)*sqrt p := by rw [pow_succ];ring
      _ ≤ n^(k+1)*(sqrt 3*exp (-(c/2)*n)) := mul_le_mul_of_nonneg_left hsp (pow_nonneg hn.le _)
      _ = sqrt 3*(n^(k+1)*exp (-(c/2)*n)) := by ring
      _ ≤ sqrt 3*(((k+1).factorial:ℝ)/(c/2)^(k+1)) := mul_le_mul_of_nonneg_left h2 (sqrt_nonneg _)
      _ = _ := by ring

lemma marked_coordinate_factor {n : ℕ} (hn : 0<n) :
    (((Fintype.card (MatrixCoordinates (Fin n)):NNReal)^(1/(2:ℝ≥0∞)).toReal:NNReal):ℝ)≤2*(n:ℝ)^2 := by
  have hnr : (1:ℝ)≤n := by exact_mod_cast hn
  have he : (1/(2:ℝ≥0∞)).toReal=(1/2:ℝ) := by norm_num
  rw [NNReal.coe_rpow,NNReal.coe_natCast,he]
  have hcard : (Fintype.card (MatrixCoordinates (Fin n)):ℝ)=(n:ℝ)^2+n := by
    simp [MatrixCoordinates,pow_two]
  rw [hcard]
  exact (rpow_le_self_of_one_le (by nlinarith : (1:ℝ)≤(n:ℝ)^2+n) (by norm_num : (1/2:ℝ)≤1)).trans
    (by nlinarith)

def markedRateConstant (j R c : ℝ) (L K B C : NNReal) (D E : ℝ) : ℝ :=
  (B:ℝ)*R*C*(3/c)+B*C*sqrt (2*j)*(sqrt 3*6/(c/2)^3)+
    (2*(sqrt (2*j))^2*(L*C+B*K:NNReal)+j*(D*C+B*E))*(360/c^5)

theorem markedError_absorption {n : ℕ} (hn : 0<n) {j R c p : ℝ}
    (hj : 0≤j) (hR : 0≤R) (hc : 0<c) (hp0 : 0≤p) (hp : p≤3*exp (-c*(n:ℝ)))
    (L K B C : NNReal) {D E : ℝ} (hD : 0≤D) (hE : 0≤E) :
    markedError (ι:=Fin n) (j/(n:ℝ)) R L K B C D E p≤
      markedRateConstant j R c L K B C D E/(n:ℝ) := by
  have hnr : (1:ℝ)≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hr : j/(n:ℝ)≤j := div_le_self hj hnr
  have hs : sqrt (2*(j/(n:ℝ)))≤ sqrt (2*j) := sqrt_le_sqrt (by linarith)
  have hcoord := marked_coordinate_factor hn
  have h0 := (power_tail_absorptions 0 hc hn0 hp).1
  have h2 := (power_tail_absorptions 2 hc hn0 hp).2
  have h4 := (power_tail_absorptions 4 hc hn0 hp).1
  norm_num only [pow_zero,one_mul,Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat] at h0 h2 h4
  let S := sqrt (2*j)
  let V : ℝ := (L*C+B*K:NNReal)
  let Z : ℝ := D*C+B*E
  have hS : 0≤S := sqrt_nonneg _
  have hV : 0≤V := NNReal.coe_nonneg _
  have hZ : 0≤Z := by dsimp [Z];positivity
  have ht : sqrt (2*(j/(n:ℝ)))*
      ((L*C+B*K:NNReal)*(⟨sqrt (2*(j/(n:ℝ))),sqrt_nonneg _⟩*
        (Fintype.card (MatrixCoordinates (Fin n)):NNReal)^(1/(2:ℝ≥0∞)).toReal):NNReal)≤
        2*S^2*V*(n:ℝ)^2 := by
    simp only [NNReal.coe_mul]
    have hh := mul_le_mul hs
      (mul_le_mul_of_nonneg_left (mul_le_mul hs hcoord
        (NNReal.coe_nonneg _) hS) hV) (by positivity) hS
    apply hh.trans_eq
    dsimp [S,V]
    ring
  have hu : sqrt (2*(j/(n:ℝ)))*
      ((L*C+B*K:NNReal)*(⟨sqrt (2*(j/(n:ℝ))),sqrt_nonneg _⟩*
        (Fintype.card (MatrixCoordinates (Fin n)):NNReal)^(1/(2:ℝ≥0∞)).toReal):NNReal)+
        (j/(n:ℝ))*(D*C+B*E)≤(2*S^2*V+j*Z)*(n:ℝ)^2 := by
    have hnn : (1:ℝ)≤(n:ℝ)^2 := one_le_pow₀ hnr
    have h1 := add_le_add ht (mul_le_mul_of_nonneg_right hr hZ)
    have h2 : j*Z≤j*Z*(n:ℝ)^2 := by nlinarith [mul_nonneg (mul_nonneg hj hZ) (sub_nonneg.mpr hnn)]
    dsimp only [Z] at h1 h2 ⊢
    nlinarith only [h1,h2]
  have hm : markedError (ι:=Fin n) (j/(n:ℝ)) R L K B C D E p≤
      (B:ℝ)*R*C*p+B*C*S*((n:ℝ)^2*sqrt p)+(2*S^2*V+j*Z)*((n:ℝ)^4*p) := by
    unfold markedError
    simp only [Fintype.card_fin]
    apply add_le_add
    · apply add_le_add le_rfl
      have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs
        (show 0≤(B:ℝ)*C*(n:ℝ)^2 by positivity)) (sqrt_nonneg p)
      convert hh using 1; dsimp [S]; ring
    · have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu (sq_nonneg (n:ℝ))) hp0
      convert hh using 1; ring
  apply hm.trans
  have hb0 := mul_le_mul_of_nonneg_left h0 (show 0≤(B:ℝ)*R*C by positivity)
  have hb2 := mul_le_mul_of_nonneg_left h2 (show 0≤(B:ℝ)*C*S by positivity)
  have hb4 := mul_le_mul_of_nonneg_left h4 (show 0≤2*S^2*V+j*Z by positivity)
  apply (add_le_add (add_le_add hb0 hb2) hb4).trans_eq
  unfold markedRateConstant
  dsimp only [S,V,Z]
  ring
end SKGap
end
end

end OAI
