import Mathlib
import OAI.NumberTheory.CubicGram.GramDyad

namespace OAI

/-! Scale-normalized coprime envelopes and divisor losses. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma gram_coprime_envelope {N a Z ε : ℝ} (hN : 0 < N) (ha : 0 < a)
    (haN : a ≤ 2*N) (hZ : 0 < Z) (hε : 0 < ε) :
    let c := Z/(27*a*N)
    (Z^2/(81*a*N))*(((2*N)^ε/c)*((2*N)*gramDyadConstant ε*c^(-ε) +
      gramDyadConstant (1+ε)*c^(-(1+ε)) +
      (2*N)^(2/3 : ℝ)*gramDyadConstant (2/3+ε)*c^(-(2/3+ε)))) ≤
    (108*(gramDyadConstant ε+gramDyadConstant (1+ε)+gramDyadConstant (2/3+ε))*(108 : ℝ)^ε) *
      (N^3/Z)^ε*(Z*N+N^2+N^2*Z^(1/3 : ℝ)) := by
  let q : ℝ := 27*a*N/Z
  have hq : 0 < q := by dsimp [q]; positivity
  have hi : Z/(27*a*N) = q⁻¹ := by dsimp [q]; rw [inv_div]
  dsimp only
  rw [hi]
  have hp (p : ℝ) : (q⁻¹)^(-p) = q^p := by
    rw [Real.inv_rpow hq.le,Real.rpow_neg hq.le,inv_inv]
  rw [hp,hp,hp,Real.rpow_add hq,Real.rpow_add hq,Real.rpow_one]
  let D := gramDyadConstant ε+gramDyadConstant (1+ε)+gramDyadConstant (2/3+ε)
  have hk0 := gramDyadConstant_pos hε
  have hk1 := gramDyadConstant_pos (by linarith : 0 < 1+ε)
  have hk2 := gramDyadConstant_pos (by linarith : 0 < 2/3+ε)
  have hD : 0 < D := by dsimp [D]; positivity
  have he : Z^2/(81*a*N)*((2*N)^ε/q⁻¹*(2*N*gramDyadConstant ε*q^ε +
      gramDyadConstant (1+ε)*(q*q^ε)+(2*N)^(2/3 : ℝ)*gramDyadConstant (2/3+ε)*(q^(2/3 : ℝ)*q^ε))) =
      (1/3 : ℝ)*(2*N*q)^ε*(2*N*gramDyadConstant ε*Z+
        gramDyadConstant (1+ε)*(Z*q)+gramDyadConstant (2/3+ε)*Z*(2*N*q)^(2/3 : ℝ)) := by
    rw [Real.mul_rpow (by positivity : 0 ≤ 2*N) hq.le,
      Real.mul_rpow (by positivity : 0 ≤ 2*N) hq.le]
    dsimp [q]
    field_simp
    ring
  rw [he]
  have hB : 2*N*q ≤ 108*(N^3/Z) := by
    dsimp [q]
    calc
      2*N*(27*a*N/Z) = (54*a*N^2)/Z := by ring
      _ ≤ (108*N^3)/Z := div_le_div_of_nonneg_right (by
        nlinarith [mul_nonneg (by linarith : 0 ≤ 2*N-a) (sq_nonneg N)]) hZ.le
      _ = _ := by ring
  have heps := Real.rpow_le_rpow (by positivity : 0 ≤ 2*N*q) hB hε.le
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 108) (by positivity : 0 ≤ N^3/Z)] at heps
  have hqbound : Z*q ≤ 54*N^2 := by dsimp [q]; field_simp; nlinarith
  have hthird : Z*(2*N*q)^(2/3 : ℝ) ≤ 108*N^2*Z^(1/3 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity : 0 ≤ 2*N*q) hB (by norm_num : (0 : ℝ) ≤ 2/3)) hZ.le
    have hr : Z*(108*(N^3/Z))^(2/3 : ℝ) = (108 : ℝ)^(2/3 : ℝ)*N^2*Z^(1/3 : ℝ) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 108) (by positivity : 0 ≤ N^3/Z),
        Real.div_rpow (by positivity : 0 ≤ N^3) hZ.le,← Real.rpow_natCast,
        ← Real.rpow_mul hN.le]
      norm_num
      have heZ : Z/(Z^(2/3 : ℝ)) = Z^(1/3 : ℝ) := by
        nth_rw 1 [← Real.rpow_one Z]
        rw [← Real.rpow_sub hZ]
        norm_num
      rw [show Z*((108 : ℝ)^(2/3 : ℝ)*(N^2/Z^(2/3 : ℝ))) =
        (108 : ℝ)^(2/3 : ℝ)*N^2*(Z/Z^(2/3 : ℝ)) by ring,heZ]
    rw [hr] at h
    apply h.trans
    gcongr
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 108)
      (by norm_num : (2/3 : ℝ) ≤ 1)).trans_eq (Real.rpow_one _)
  have hb : 2*N*gramDyadConstant ε*Z+gramDyadConstant (1+ε)*(Z*q)+
      gramDyadConstant (2/3+ε)*Z*(2*N*q)^(2/3 : ℝ) ≤
      108*D*(Z*N+N^2+N^2*Z^(1/3 : ℝ)) := by
    have hk0D : gramDyadConstant ε ≤ D := by dsimp [D]; linarith
    have hk1D : gramDyadConstant (1+ε) ≤ D := by dsimp [D]; linarith
    have hk2D : gramDyadConstant (2/3+ε) ≤ D := by dsimp [D]; linarith
    calc
      _ ≤ D*(2*N*Z+(54*N^2)+(108*N^2*Z^(1/3 : ℝ))) := by
        have h0 := mul_le_mul_of_nonneg_right hk0D (by positivity : 0 ≤ 2*N*Z)
        have h1 := mul_le_mul hk1D hqbound (by positivity) hD.le
        have h2 := mul_le_mul hk2D hthird (by positivity) hD.le
        nlinarith
      _ ≤ _ := by nlinarith [mul_nonneg (hD.le) (by positivity : 0 ≤ Z*N),
        mul_nonneg hD.le (sq_nonneg N)]
  have h := mul_le_mul heps hb (by positivity) (by positivity)
  have hL : 0 ≤ (2*N*q)^ε*(2*N*gramDyadConstant ε*Z+gramDyadConstant (1+ε)*(Z*q)+
      gramDyadConstant (2/3+ε)*Z*(2*N*q)^(2/3 : ℝ)) := by positivity
  dsimp [D] at h
  nlinarith

theorem primaryCharacterGram_coprime_normalized (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset Eisenstein) (N : ℝ), 1 ≤ 2*N →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ N ≤ norm b ∧ norm b ≤ 2*N) →
      ∀ (a : Eisenstein), primary a → Squarefree a → norm a ≤ 2*N →
      (∀ b ∈ S, IsCoprime a b ∧ a ≠ b) → ∀ (Z : ℝ), 0 < Z →
      (∑ b ∈ S, ‖primaryCharacterGram a b W Z‖^2) ≤
        C*(N^3/Z)^ε*(Z*N+N^2+N^2*Z^(1/3 : ℝ)) := by
  obtain ⟨C,hC,hc⟩ := primaryCharacterGram_coprime_explicit W hW hW' hε hε1
  have hk0 := gramDyadConstant_pos hε
  have hk1 := gramDyadConstant_pos (by linarith : 0 < 1+ε)
  have hk2 := gramDyadConstant_pos (by linarith : 0 < 2/3+ε)
  refine ⟨C*(108*(gramDyadConstant ε+gramDyadConstant (1+ε)+
    gramDyadConstant (2/3+ε))*(108 : ℝ)^ε),by positivity,?_⟩
  intro S N hN hS a ha hsa han hab Z hZ
  have hNa : 0 < norm a := norm_pos_of_ne_zero (primary_ne_zero ha)
  have h := mul_le_mul_of_nonneg_left (gram_coprime_envelope (by linarith) hNa han hZ hε) hC.le
  have hh := hc S N hN hS a ha hsa hab Z hZ
  dsimp only at h hh
  nlinarith

lemma gram_scaled_loss {P Z K M ε : ℝ} (hP : 1 ≤ P) (hZ : 1 ≤ Z)
    (hK : 1 ≤ K) (hM : 1 ≤ M) (hMP : M ≤ 2*P) (hε : 0 < ε) :
    ((P/K)^3/(Z/M))^ε * ((Z/M)*(P/K)+(P/K)^2+(P/K)^2*(Z/M)^(1/3 : ℝ)) ≤
    (2 : ℝ)^ε * P^(4*ε) * (Z*P+P^2+P^2*Z^(1/3 : ℝ)) := by
  have hP0 : 0 < P := by linarith
  have hZ0 : 0 < Z := by linarith
  have hK0 : 0 < K := by linarith
  have hM0 : 0 < M := by linarith
  have hnP : P/K ≤ P := div_le_self hP0.le hK
  have hzZ : Z/M ≤ Z := div_le_self hZ0.le hM
  have hx : (P/K)^3/(Z/M) ≤ 2*P^4 := by
    rw [div_div_eq_mul_div]
    calc
      _ ≤ (P^3*(2*P))/1 := by gcongr
      _ = _ := by ring
  have hxpow := Real.rpow_le_rpow (by positivity : 0 ≤ (P/K)^3/(Z/M)) hx hε.le
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : 0 ≤ P^4),
    ← Real.rpow_natCast P 4,← Real.rpow_mul hP0.le] at hxpow
  have hshape : (Z/M)*(P/K)+(P/K)^2+(P/K)^2*(Z/M)^(1/3 : ℝ) ≤
      Z*P+P^2+P^2*Z^(1/3 : ℝ) := by gcongr
  exact mul_le_mul hxpow hshape (by positivity) (by positivity)

end CubicFirstMoment
end
end

end OAI
