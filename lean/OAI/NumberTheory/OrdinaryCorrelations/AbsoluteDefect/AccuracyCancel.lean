import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PhaseNatMul
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.MajorWidth

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinaryUniformWidth
open OrdinaryCorrelations OrdinaryMellinModulus OrdinaryAdditiveBilinear Finset Filter

lemma accuracy_cancel (m : ℕ) : (2:ℝ)^(2*m)*accuracy m=1 := by
  unfold accuracy
  rw [←mul_pow];norm_num

lemma accuracy_sq_cancel (m : ℕ) : (2:ℝ)^(4*m)*(accuracy m)^2=1 := by
  unfold accuracy
  rw [←pow_mul,show 2*m*2=4*m by omega,←mul_pow];norm_num

lemma approxBound_large_K (A c k v t m : ℕ) : 2*primeEnd t m≤approxBound A c k v t m := by
  unfold approxBound;omega

lemma approxBound_large_H (A c k v t m : ℕ) :
    2*Real.pi*majorWidth A c k v m*(2:ℝ)^(2*m)≤approxBound A c k v t m := by
  have hc := Nat.le_ceil (2*Real.pi*majorWidth A c k v m*(2:ℝ)^(2*m))
  apply hc.trans
  exact_mod_cast (show Nat.ceil (2*Real.pi*majorWidth A c k v m*(2:ℝ)^(2*m))≤approxBound A c k v t m by unfold approxBound;omega)

lemma shortWidth_large_H (A c k v t m : ℕ) :
    (2:ℝ)^(2*m)*majorWidth A c k v m≤ shortWidth A c k v t m := by
  have hc := Nat.le_ceil ((2:ℝ)^(2*m)*majorWidth A c k v m)
  apply hc.trans
  exact_mod_cast (show Nat.ceil ((2:ℝ)^(2*m)*majorWidth A c k v m)≤ shortWidth A c k v t m by unfold shortWidth;omega)

lemma shortWidth_large_smooth (A c k v t m : ℕ) :
    8*(approxBound A c k v t m:ℝ)*primeEnd t m*(primeSpan t m+1:ℕ)^2*(2:ℝ)^(4*m)
      ≤ shortWidth A c k v t m := by
  have hc := Nat.le_ceil (8*(approxBound A c k v t m:ℝ)*primeEnd t m*(primeSpan t m+1:ℕ)^2*(2:ℝ)^(4*m))
  apply hc.trans
  exact_mod_cast (show Nat.ceil (8*(approxBound A c k v t m:ℝ)*primeEnd t m*(primeSpan t m+1:ℕ)^2*(2:ℝ)^(4*m))≤ shortWidth A c k v t m by unfold shortWidth;omega)

lemma major_radius (A c k v t m : ℕ) {q : ℕ} (hq : 0<q) :
    1/(((approxBound A c k v t m:ℝ)+1)*q) ≤ accuracy m/(2*Real.pi*majorWidth A c k v m) := by
  have hH := majorWidth_pos A c k v m
  have hN : (0:ℝ)<approxBound A c k v t m := by exact_mod_cast approxBound_pos A c k v t m
  have hq1 : (1:ℝ)≤q := by exact_mod_cast hq
  have hq0 : (0:ℝ)<q := zero_lt_one.trans_le hq1
  have hh := mul_le_mul_of_nonneg_left (approxBound_large_H A c k v t m) (accuracy_pos m).le
  have he : accuracy m*(2*Real.pi*majorWidth A c k v m*(2:ℝ)^(2*m))=2*Real.pi*majorWidth A c k v m := by
    calc
      _ =(2*Real.pi*majorWidth A c k v m)*((2:ℝ)^(2*m)*accuracy m) := by ring
      _ = _ := by rw [accuracy_cancel,mul_one]
  rw [he] at hh
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have hn : (approxBound A c k v t m:ℝ)≤((approxBound A c k v t m:ℝ)+1)*q := by nlinarith only [hq1,hN]
  simpa only [one_mul] using hh.trans (mul_le_mul_of_nonneg_left hn (accuracy_pos m).le)

lemma minor_radius (A c k v t m : ℕ) {q : ℕ} (hq : 0<q) :
    1/(((approxBound A c k v t m:ℝ)+1)*q) ≤ 1/(2*(q:ℝ)*primeEnd t m) := by
  have hq0 : (0:ℝ)<q := by exact_mod_cast hq
  have hK : (0:ℝ)<primeEnd t m := by exact_mod_cast primeEnd_pos t m
  apply one_div_le_one_div_of_le (by positivity)
  have hN : 2*(primeEnd t m:ℝ)≤approxBound A c k v t m := by exact_mod_cast approxBound_large_K A c k v t m
  nlinarith only [hN,hq0]

lemma smooth_loss_small (A c k v t m : ℕ) :
    (primeSpan t m:ℝ)*Real.sqrt (8*(approxBound A c k v t m:ℝ)*primeEnd t m/shortWidth A c k v t m)≤accuracy m := by
  let R : ℝ := primeSpan t m
  let S : ℝ := shortWidth A c k v t m
  let Z : ℝ := 8*(approxBound A c k v t m:ℝ)*primeEnd t m
  have hR : 0≤R := Nat.cast_nonneg _
  have hS : 0<S := by dsimp [S];exact_mod_cast shortWidth_pos A c k v t m
  have hZ : 0≤Z := by dsimp [Z];positivity
  have hs : Z*(R+1)^2*(2:ℝ)^(4*m)≤S := by
    simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_pow] using shortWidth_large_smooth A c k v t m
  have hx := mul_le_mul_of_nonneg_right hs (sq_nonneg (accuracy m))
  have he : Z*(R+1)^2*(2:ℝ)^(4*m)*accuracy m^2=Z*(R+1)^2 := by
    rw [mul_assoc (Z*(R+1)^2),accuracy_sq_cancel,mul_one]
  rw [he] at hx
  have hfrac : Z*(R+1)^2/S≤accuracy m^2 := by
    apply (div_le_iff₀ hS).mpr
    nlinarith only [hx]
  have hsq : ((R+1)*Real.sqrt (Z/S))^2≤accuracy m^2 := by
    rw [mul_pow,Real.sq_sqrt (div_nonneg hZ hS.le)]
    have he : (R+1)^2*(Z/S)=Z*(R+1)^2/S := by ring
    rw [he]
    exact hfrac
  have hle := (sq_le_sq₀ (by positivity : 0≤(R+1)*Real.sqrt (Z/S)) (accuracy_pos m).le).mp hsq
  change R*Real.sqrt (Z/S)≤accuracy m
  exact (mul_le_mul_of_nonneg_right (by linarith : R≤R+1) (Real.sqrt_nonneg _)).trans hle

end OrdinaryUniformWidth

end

end OAI
