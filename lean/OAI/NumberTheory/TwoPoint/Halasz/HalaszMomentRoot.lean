import OAI.NumberTheory.TwoPoint.Halasz.HalaszSelectedDoubleMoment

namespace OAI

/-! Extracting the normalized exponential-sum saving from its even moment. -/
namespace TwoPointCorrelations

lemma halasz_moment_root {x B M N d : ℝ} {p : ℕ}
    (hp : 0<p) (hx : 0≤x) (hB : 0≤B) (hM : 0<M) (hN : 0<N)
    (h : x^p≤B*M^(2*p)*N^d) :
    x/M^2≤B^((p:ℝ)⁻¹)*N^(d/(p:ℝ)) := by
  have hpR : 0<(p:ℝ) := by exact_mod_cast hp
  have hden : 0<(M^2)^p := pow_pos (pow_pos hM 2) p
  have hn : (x/M^2)^p≤B*N^d := by
    rw [div_pow]
    apply (div_le_iff₀ hden).mpr
    convert h using 1
    rw [← pow_mul]
    ring
  have hroot : x/M^2≤(B*N^d)^((p:ℝ)⁻¹) := by
    apply (Real.le_rpow_inv_iff_of_pos (by positivity : 0≤x/M^2)
      (mul_nonneg hB (Real.rpow_nonneg hN.le _)) hpR).mpr
    simpa only [Real.rpow_natCast] using hn
  apply hroot.trans_eq
  rw [Real.mul_rpow hB (Real.rpow_nonneg hN.le _),← Real.rpow_mul hN.le]
  rw [div_eq_mul_inv]

lemma halasz_moment_transfer {x A D M N ε σ d : ℝ} {p : ℕ}
    (hp : 0<p) (hx : 0≤x) (hA : 0≤A) (hD : 0≤D)
    (hM : 1≤M) (hMN : M≤N) (hε : 0≤ε) (hδ : ε-σ≤d)
    (h : x^p≤A*M^(((2*p:ℕ):ℝ)+ε)*D*N^(-σ)) :
    x/M^2≤(A*D)^((p:ℝ)⁻¹)*N^(d/(p:ℝ)) := by
  have hM0 : 0<M := by linarith
  have hN : 1≤N := hM.trans hMN
  have hN0 : 0<N := hM0.trans_le hMN
  apply halasz_moment_root hp hx (mul_nonneg hA hD) hM0 hN0
  apply h.trans
  have hscale : M^ε*N^(-σ)≤N^d := by
    calc
      _ ≤ N^ε*N^(-σ) := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow hM0.le hMN hε) (Real.rpow_nonneg hN0.le _)
      _ = N^(ε-σ) := by rw [← Real.rpow_add hN0]; rfl
      _ ≤ N^d := Real.rpow_le_rpow_of_exponent_le hN hδ
  rw [Real.rpow_add hM0,Real.rpow_natCast]
  calc
    _ = (A*D*M^(2*p))*(M^ε*N^(-σ)) := by ring
    _ ≤ (A*D*M^(2*p))*N^d :=
      mul_le_mul_of_nonneg_left hscale (by positivity)

end TwoPointCorrelations

end OAI
