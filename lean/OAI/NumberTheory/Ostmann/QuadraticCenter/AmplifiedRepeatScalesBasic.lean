import OAI.NumberTheory.Ostmann.QuadraticCenter.ParameterCostBounds

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter

def amplifiedRepeatTau (Z K k : ℕ) : ℝ :=
  Real.exp (-Real.log Z/2+(1/125:ℝ)*(K:ℝ)/(k:ℝ))

theorem amplifiedRepeatTau_pos (Z K k : ℕ) : 0<amplifiedRepeatTau Z K k := Real.exp_pos _

theorem repeat_error_le_of_scale {J τ : ℝ} {k : ℕ} (hJ : 0<J) (hτ : 0<τ) (hk : 2≤k)
    (hscale : 4*((k:ℝ)+1)^2≤Real.sqrt J*τ) :
    4*((((k:ℝ)+1)*(k:ℝ)^2/J)*(τ+(k:ℝ)/Real.sqrt J)^(k-2))≤τ^k := by
  have hk0 : (0:ℝ)≤k := Nat.cast_nonneg k
  have hsJ : 0<Real.sqrt J := Real.sqrt_pos.2 hJ
  have hsJ2 := Real.sq_sqrt hJ.le
  let a : ℝ := (k:ℝ)/(Real.sqrt J*τ)
  have ha : 0≤a := by dsimp [a]; positivity
  have hka : (k:ℝ)*a≤1 := by
    dsimp [a]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (mul_pos hsJ hτ)).mpr
    nlinarith
  have hnk : ((k-2:ℕ):ℝ)≤k := by exact_mod_cast Nat.sub_le k 2
  have hp : (1+a)^(k-2)≤3 := by
    calc
      _ ≤ (Real.exp a)^(k-2) := pow_le_pow_left₀ (by positivity)
        (by linarith [Real.add_one_le_exp a]) _
      _ = Real.exp (((k-2:ℕ):ℝ)*a) := (Real.exp_nat_mul a (k-2)).symm
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr
        ((mul_le_mul_of_nonneg_right hnk ha).trans hka)
      _ ≤ 3 := Real.exp_one_lt_three.le
  have hpoly : 12*((k:ℝ)+1)*(k:ℝ)^2≤16*((k:ℝ)+1)^4 := by
    have hx : 0≤16*((k:ℝ)+1)^4-12*((k:ℝ)+1)*(k:ℝ)^2 := by
      ring_nf
      positivity
    linarith
  have hsq : 16*((k:ℝ)+1)^4≤J*τ^2 := by
    have hh := pow_le_pow_left₀ (by positivity : (0:ℝ)≤4*((k:ℝ)+1)^2) hscale 2
    simp only [mul_pow,hsJ2] at hh
    nlinarith
  have hcoef : 12*((k:ℝ)+1)*(k:ℝ)^2/J≤τ^2 :=
    (div_le_iff₀ hJ).mpr ((hpoly.trans hsq).trans_eq (mul_comm J (τ^2)))
  have he : τ+(k:ℝ)/Real.sqrt J=τ*(1+a) := by
    dsimp [a]
    field_simp
  rw [he,mul_pow]
  calc
    _ = (4*((k:ℝ)+1)*(k:ℝ)^2/J)*τ^(k-2)*(1+a)^(k-2) := by ring
    _ ≤ (4*((k:ℝ)+1)*(k:ℝ)^2/J)*τ^(k-2)*3 :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (12*((k:ℝ)+1)*(k:ℝ)^2/J)*τ^(k-2) := by ring
    _ ≤ τ^2*τ^(k-2) := mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = τ^k := by rw [←pow_add,Nat.add_sub_of_le hk]

theorem amplifiedRepeatTau_mass {X c₀ : ℝ} {Z K k : ℕ}
    (hX : 0<X) (hc₀ : 0<c₀) (hZ : 0<Real.log Z) (hk : 0<k)
    (horder : Real.log X/Real.log Z+10≤(k:ℝ))
    (hc : Real.log c₀≤5*Real.log Z) :
    X*c₀*(amplifiedRepeatTau Z K k)^k≤Real.sqrt X*Real.exp ((2/125:ℝ)*K) := by
  have hkR : (k:ℝ)≠0 := by exact_mod_cast hk.ne'
  have hlog : Real.log X+10*Real.log Z≤(k:ℝ)*Real.log Z := by
    have hh := mul_le_mul_of_nonneg_right horder hZ.le
    rw [add_mul,div_mul_cancel₀ _ hZ.ne'] at hh
    exact hh
  have hpow : (amplifiedRepeatTau Z K k)^k=
      Real.exp (-(k:ℝ)*Real.log Z/2+(1/125:ℝ)*K) := by
    unfold amplifiedRepeatTau
    rw [←Real.exp_nat_mul]
    congr 1
    field_simp
  have hsqrt : Real.sqrt X=Real.exp (Real.log X/2) := by
    rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hX]
    congr 1
    ring
  rw [hpow,hsqrt,←Real.exp_add]
  have he : X*c₀*Real.exp (-(k:ℝ)*Real.log Z/2+(1/125:ℝ)*K)=
      Real.exp (Real.log X+Real.log c₀-(k:ℝ)*Real.log Z/2+(1/125:ℝ)*K) := by
    have hXc : X*c₀=Real.exp (Real.log X+Real.log c₀) := by
      rw [Real.exp_add,Real.exp_log hX,Real.exp_log hc₀]
    rw [hXc,←Real.exp_add]
    congr 1
    ring
  rw [he]
  apply Real.exp_le_exp.mpr
  nlinarith [(show (0:ℝ)≤K from Nat.cast_nonneg K)]

end Ostmann.QuadraticCenter

end

end OAI
