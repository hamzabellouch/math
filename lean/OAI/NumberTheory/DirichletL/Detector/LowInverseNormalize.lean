import OAI.NumberTheory.DirichletL.Detector.LowCentralGeometry

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical

lemma low_inverse_power_cancel (Z d α : ℝ) (hZ : 0<Z) :
    Z^(5/6-2*d+α)*(Z^d)^2/Z^(5/6:ℝ)=Z^α := by
  have hp : (Z^d)^2=Z^(2*d) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
    congr 1
    push_cast
    ring
  rw [hp,←Real.rpow_add hZ,←Real.rpow_sub hZ]
  congr 1
  ring

lemma low_inverse_sqrt_normalized (q C B Z L d α H E : ℝ) (n : ℕ)
    (hq : 0<q) (hC : 0≤C) (_hB : 0≤B) (hZ : 0<Z) (hL : 0<L) (hH : 1≤H)
    (hE : 0≤E) (hEL : E≤C*H^n*Z^(5/6-2*d+α)) (hLB : L≤B*Z^d) :
    Real.sqrt E/Real.sqrt (q*Z^(5/6:ℝ)/L^2)≤
      Real.sqrt (C*B^2/q)*H^n*Z^(α/2) := by
  have hratio : E/(q*Z^(5/6:ℝ)/L^2)≤(C*B^2/q)*H^n*Z^α := by
    calc
      _≤(C*H^n*Z^(5/6-2*d+α))/(q*Z^(5/6:ℝ)/L^2) :=
        div_le_div_of_nonneg_right hEL (by positivity)
      _=(C*H^n*Z^(5/6-2*d+α))*L^2/(q*Z^(5/6:ℝ)) := by field_simp
      _≤(C*H^n*Z^(5/6-2*d+α))*(B*Z^d)^2/(q*Z^(5/6:ℝ)) := by
        gcongr
      _=(C*B^2/q)*H^n*(Z^(5/6-2*d+α)*(Z^d)^2/Z^(5/6:ℝ)) := by ring
      _=_ := by rw [low_inverse_power_cancel Z d α hZ]
  rw [←Real.sqrt_div hE]
  apply (Real.sqrt_le_sqrt hratio).trans
  rw [Real.sqrt_mul (by positivity),Real.sqrt_mul (by positivity)]
  have hp : Real.sqrt (Z^α)=Z^(α/2) := by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hZ.le]
    congr 1
    ring
  rw [hp]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_self_iff.mpr (Or.inr (one_le_pow₀ hH))) (by positivity)) (by positivity)

end SevenEighths.ProbePhysical
end

end OAI
