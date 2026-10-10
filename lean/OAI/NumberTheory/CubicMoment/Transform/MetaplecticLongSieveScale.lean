import OAI.NumberTheory.CubicMoment.Transform.MetaplecticTailSieve

namespace OAI

/-! The exact cube-length scaling in the long Type-I sieve bound. -/
noncomputable section
namespace CubicFirstMoment

lemma metaplectic_long_cube_scale {n E V ε : ℝ}
    (hE : 0 < E) (hEn : E ≤ n) (hV : 0 ≤ V) (hε : ε ≤ 1) :
    n^(1+2*ε)*(V/n^3) ≤ V*E^(-2+2*ε) := by
  have hn : 0 < n := hE.trans_le hEn
  have he : n^(1+2*ε)/n^3 = n^(-2+2*ε) := by
    rw [←Real.rpow_natCast n 3,←Real.rpow_sub hn]
    congr 1
    ring
  calc
    _ = V*(n^(1+2*ε)/n^3) := by ring
    _ = V*n^(-2+2*ε) := by rw [he]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hE hEn (by linarith)) hV

lemma metaplectic_long_sieve_scale {n E N U B ε : ℝ}
    (hE : 1 ≤ E) (hEn : E ≤ n) (hN : 0 ≤ N) (hU : 0 ≤ U) (hB : 0 ≤ B)
    (hε : 0 ≤ ε) (hεsmall : ε ≤ 1) :
    n^(1+2*ε)*(N*(B*(U/n^3)))^ε*(B*(U/n^3))*
        (N+B*(U/n^3)+(N*(B*(U/n^3)))^(2/3:ℝ)) ≤
      (N*(B*U))^ε*(B*U)*E^(-2+2*ε)*
        (N+B*(U/E^3)+(N*(B*(U/E^3)))^(2/3:ℝ)) := by
  have hEp : 0 < E := zero_lt_one.trans_le hE
  have hn : 0 < n := hEp.trans_le hEn
  have hn1 : 1 ≤ n := hE.trans hEn
  have hz0 : 0 ≤ B*(U/n^3) := by positivity
  have hze0 : 0 ≤ B*(U/E^3) := by positivity
  have hz : B*(U/n^3) ≤ B*U := mul_le_mul_of_nonneg_left
    (div_le_self hU (one_le_pow₀ hn1)) hB
  have hze : B*(U/n^3) ≤ B*(U/E^3) := by
    apply mul_le_mul_of_nonneg_left _ hB
    exact div_le_div_of_nonneg_left hU (pow_pos hEp 3)
      (pow_le_pow_left₀ hEp.le hEn 3)
  have hp : (N*(B*(U/n^3)))^ε ≤ (N*(B*U))^ε :=
    Real.rpow_le_rpow (mul_nonneg hN hz0) (mul_le_mul_of_nonneg_left hz hN) hε
  have hs : N+B*(U/n^3)+(N*(B*(U/n^3)))^(2/3:ℝ) ≤
      N+B*(U/E^3)+(N*(B*(U/E^3)))^(2/3:ℝ) := by
    gcongr
  have hc : n^(1+2*ε)*(B*(U/n^3)) ≤ (B*U)*E^(-2+2*ε) := by
    simpa only [mul_div_assoc] using metaplectic_long_cube_scale hEp hEn
      (mul_nonneg hB hU) hεsmall
  calc
    _ = (n^(1+2*ε)*(B*(U/n^3)))*(N*(B*(U/n^3)))^ε*
        (N+B*(U/n^3)+(N*(B*(U/n^3)))^(2/3:ℝ)) := by ring
    _ ≤ ((B*U)*E^(-2+2*ε))*(N*(B*U))^ε*
        (N+B*(U/E^3)+(N*(B*(U/E^3)))^(2/3:ℝ)) :=
      mul_le_mul (mul_le_mul hc hp (by positivity) (by positivity)) hs
        (by positivity) (by positivity)
    _ = _ := by ring

lemma metaplectic_long_dyad_scale {E ε : ℝ} (hE : 0 < E) :
    (36*E)^2*E^(-2+2*ε) = 1296*E^(2*ε) := by
  rw [mul_pow,show (36:ℝ)^2 = 1296 by norm_num,←Real.rpow_two E,
    mul_assoc,←Real.rpow_add hE]
  rw [show (2:ℝ)+(-2+2*ε) = 2*ε by ring]

end CubicFirstMoment

end

end OAI
