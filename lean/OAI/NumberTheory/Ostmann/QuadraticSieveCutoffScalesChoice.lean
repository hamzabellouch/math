import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
namespace Ostmann.QuadraticSieve

def smoothingCutoff (M N : ℕ) (η : ℝ) : ℕ :=
  ⌈(2*(N:ℝ)^2/M)*((M:ℝ)*N)^η⌉₊

theorem smoothingCutoff_size {M N : ℕ} {η : ℝ} (hM : 0<M) (hN : 0<N)
    (hη : 0<η) (hscale : 4*(N:ℝ)*((M:ℝ)*N)^η ≤ M) :
    0<smoothingCutoff M N η ∧ smoothingCutoff M N η≤M ∧
      (2*(N:ℝ)^2/M)*((M:ℝ)*N)^η ≤ (smoothingCutoff M N η:ℝ) ∧
      (smoothingCutoff M N η:ℝ) ≤ ((M:ℝ)*N)^3 ∧
      (smoothingCutoff M N η:ℝ) ≤ (2*(N:ℝ)^2/M)*((M:ℝ)*N)^η+1 := by
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hM1 : (1:ℝ)≤M := by exact_mod_cast hM
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hP1 : (1:ℝ)≤(M:ℝ)*N := by nlinarith
  have hT1 : 1≤((M:ℝ)*N)^η := Real.one_le_rpow hP1 hη.le
  have hT0 : 0<((M:ℝ)*N)^η := by positivity
  have hNM : (N:ℝ)≤M := by nlinarith [mul_le_mul_of_nonneg_left hT1 hNr.le]
  have hA : 0<(2*(N:ℝ)^2/M)*((M:ℝ)*N)^η := by positivity
  have hAM : (2*(N:ℝ)^2/M)*((M:ℝ)*N)^η ≤ M := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hMr).mpr
    nlinarith [mul_le_mul_of_nonneg_left hscale hNr.le]
  have hK : smoothingCutoff M N η≤M := Nat.ceil_le.mpr hAM
  have hKr : (smoothingCutoff M N η:ℝ)≤M := by exact_mod_cast hK
  refine ⟨Nat.ceil_pos.mpr hA,hK,Nat.le_ceil _,?_,(Nat.ceil_lt_add_one hA.le).le⟩
  have hMP : (M:ℝ)≤(M:ℝ)*N := by nlinarith
  exact hKr.trans (hMP.trans (by nlinarith [sq_nonneg (((M:ℝ)*N)-1)]))

theorem smoothingCutoff_sqrt_bound {M N : ℕ} {η : ℝ} (hM : 0<M) (hN : 0<N)
    (hη : 0<η) (hscale : 4*(N:ℝ)*((M:ℝ)*N)^η ≤ M) :
    Real.sqrt ((M:ℝ)/(smoothingCutoff M N η:ℝ))*N ≤ M := by
  have hc := smoothingCutoff_size hM hN hη hscale
  have hMr : (0:ℝ)<M := by exact_mod_cast hM
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  have hKr : (0:ℝ)<smoothingCutoff M N η := by exact_mod_cast hc.1
  have hM1 : (1:ℝ)≤M := by exact_mod_cast hM
  have hN1 : (1:ℝ)≤N := by exact_mod_cast hN
  have hP1 : (1:ℝ)≤(M:ℝ)*N := by nlinarith
  have hT1 : 1≤((M:ℝ)*N)^η := Real.one_le_rpow hP1 hη.le
  have hbase : (N:ℝ)^2/(M:ℝ) ≤ (smoothingCutoff M N η:ℝ) := by
    have ha : 0≤2*(N:ℝ)^2/(M:ℝ) := by positivity
    have he := mul_le_mul_of_nonneg_left hT1 ha
    calc
      (N:ℝ)^2/M ≤ 2*((N:ℝ)^2/M) := by nlinarith [div_nonneg (sq_nonneg (N:ℝ)) hMr.le]
      _ = 2*(N:ℝ)^2/M := by ring
      _ ≤ (2*(N:ℝ)^2/M)*((M:ℝ)*N)^η := by simpa only [mul_one] using he
      _ ≤ (smoothingCutoff M N η:ℝ) := hc.2.2.1
  have hprod : (N:ℝ)^2 ≤ (smoothingCutoff M N η:ℝ)*M :=
    (div_le_iff₀ hMr).mp hbase
  have hs : (Real.sqrt ((M:ℝ)/(smoothingCutoff M N η:ℝ))*N)^2 ≤ (M:ℝ)^2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hKr).mpr
    nlinarith [mul_le_mul_of_nonneg_left hprod hMr.le]
  nlinarith [Real.sqrt_nonneg ((M:ℝ)/(smoothingCutoff M N η:ℝ))]

end Ostmann.QuadraticSieve

end

end OAI
