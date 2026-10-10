import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section
open Polynomial
namespace NCHitting

variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
theorem wronskian_mul_common (g p q : F[X]) :
    Polynomial.wronskian (g*p) (g*q) = g^2 * Polynomial.wronskian p q := by
  simp only [Polynomial.wronskian, Polynomial.derivative_mul]
  ring

theorem eq_smul_of_wronskian_eq_zero (p q : F[X]) (hp : p ≠ 0)
    (hw : Polynomial.wronskian p q = 0) : ∃ c : F, q = c • p := by
  classical
  let : GCDMonoid F[X] := IsBezout.toGCDDomain _
  obtain ⟨a, b, ha, hb, hab⟩ := extract_gcd p q
  let g := gcd p q
  change p = g * a at ha
  change q = g * b at hb
  have hg : g ≠ 0 := by
    intro h
    apply hp
    simpa [h] using ha
  have ha0 : a ≠ 0 := by
    intro h
    apply hp
    simpa [h] using ha
  have hwab : Polynomial.wronskian a b = 0 := by
    have hfactor : Polynomial.wronskian p q = g^2 * Polynomial.wronskian a b :=
      (congrArg₂ Polynomial.wronskian ha hb).trans (wronskian_mul_common g a b)
    rw [hfactor] at hw
    exact (mul_eq_zero.mp hw).resolve_left (pow_ne_zero _ hg)
  have hcop : IsCoprime a b := (gcd_isUnit_iff a b).mp hab
  obtain ⟨had, hbd⟩ := hcop.wronskian_eq_zero_iff.mp hwab
  have hac : a = C (a.coeff 0) := Polynomial.eq_C_of_derivative_eq_zero had
  have hbc : b = C (b.coeff 0) := Polynomial.eq_C_of_derivative_eq_zero hbd
  have hac0 : a.coeff 0 ≠ 0 := by
    intro h
    apply ha0
    simpa [h] using hac
  refine ⟨b.coeff 0 / a.coeff 0, ?_⟩
  rw [Polynomial.smul_eq_C_mul]
  calc
    q = g * C (b.coeff 0) := hb.trans (congrArg (g * ·) hbc)
    _ = C (b.coeff 0 / a.coeff 0) * (g * C (a.coeff 0)) := by
      rw [mul_left_comm, ← C_mul, div_mul_cancel₀ _ hac0]
    _ = C (b.coeff 0 / a.coeff 0) * p :=
      congrArg (C (b.coeff 0 / a.coeff 0) * ·) (ha.trans (congrArg (g * ·) hac)).symm

section FormalResidue
open PowerSeries

theorem coeff_X_mul_derivative (v : PowerSeries F) (k : ℕ) :
    PowerSeries.coeff k (PowerSeries.X * PowerSeries.derivative (R := F) v) =
      (k : F) * PowerSeries.coeff k v := by
  cases k with
  | zero => simp
  | succ k =>
    have hs := PowerSeries.coeff_X_pow_mul (PowerSeries.derivative (R := F) v) 1 k
    simp only [pow_one] at hs
    rw [hs, PowerSeries.coeff_derivative]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

theorem X_mul_derivative_X_pow (k : ℕ) :
    PowerSeries.X * PowerSeries.derivative (R := F) ((PowerSeries.X : PowerSeries F)^k) =
      PowerSeries.C (k : F) * PowerSeries.X^k := by
  ext r
  rw [coeff_X_mul_derivative, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  split_ifs with hr
  · subst r; rfl
  · simp

private theorem formal_wronskian_factor (A v Q S : PowerSeries F) (k : ℕ) :
    (PowerSeries.X * Q) *
        ((PowerSeries.X^k * A) * PowerSeries.derivative (R := F) (A*v) -
          PowerSeries.derivative (R := F) (PowerSeries.X^k * A) * (A*v)) +
        (PowerSeries.X^k * A)^2 * S =
      PowerSeries.X^k * A^2 *
        (Q * (PowerSeries.X * PowerSeries.derivative (R := F) v - PowerSeries.C (k : F) * v) +
          PowerSeries.X^k * S) := by
  simp only [Derivation.leibniz, smul_eq_mul]
  calc
    _ = PowerSeries.X^k * A^2 * (Q * (PowerSeries.X * PowerSeries.derivative (R := F) v) +
          PowerSeries.X^k * S) -
        (PowerSeries.X * PowerSeries.derivative (R := F) (PowerSeries.X^k)) * A^2 * Q * v := by
          ring
    _ = _ := by rw [X_mul_derivative_X_pow]; ring

theorem formal_residue_obstruction (p0 p Q S : PowerSeries F)
    (hp0 : p0 ≠ 0) (hQ : PowerSeries.constantCoeff Q ≠ 0)
    (h : (PowerSeries.X * Q) *
        (p0 * PowerSeries.derivative (R := F) p - PowerSeries.derivative (R := F) p0 * p) +
        p0^2 * S = 0) : PowerSeries.constantCoeff S = 0 := by
  let k := p0.order.toNat
  let A := p0.divXPowOrder
  let v := A⁻¹ * p
  have hA : PowerSeries.constantCoeff A ≠ 0 := by
    exact mt PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.mp hp0
  have hA0 : A ≠ 0 := by
    intro he
    exact hA (by simp [he])
  have hpa : PowerSeries.X^k * A = p0 := PowerSeries.X_pow_order_mul_divXPowOrder
  have hav : A*v = p := by
    dsimp [v]
    rw [← mul_assoc, MvPowerSeries.mul_inv_cancel A hA, one_mul]
  have hf : PowerSeries.X^k * A^2 *
      (Q * (PowerSeries.X * PowerSeries.derivative (R := F) v - PowerSeries.C (k : F) * v) +
        PowerSeries.X^k * S) = 0 := by
    rw [← formal_wronskian_factor]
    simpa only [hpa, hav] using h
  have hn : PowerSeries.X^k * A^2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) (pow_ne_zero _ hA0)
  have he := (mul_eq_zero.mp hf).resolve_left hn
  have he' :
      (PowerSeries.X * PowerSeries.derivative (R := F) v - PowerSeries.C (k : F) * v) +
        PowerSeries.X^k * (Q⁻¹*S) = 0 := by
    calc
      _ = Q⁻¹ *
          (Q * (PowerSeries.X * PowerSeries.derivative (R := F) v - PowerSeries.C (k : F) * v) +
            PowerSeries.X^k * S) := by
        simp only [mul_add, ← mul_assoc, MvPowerSeries.inv_mul_cancel Q hQ, one_mul]
        ring
      _ = 0 := by rw [he, mul_zero]
  have hk := congrArg (PowerSeries.coeff k) he'
  have heuler : PowerSeries.coeff k
      (PowerSeries.X * PowerSeries.derivative (R := F) v - PowerSeries.C (k : F) * v) = 0 := by
    rw [map_sub, coeff_X_mul_derivative, PowerSeries.coeff_C_mul, sub_self]
  have hshift : PowerSeries.coeff k (PowerSeries.X^k * (Q⁻¹*S)) =
      PowerSeries.constantCoeff (Q⁻¹*S) := by
    simpa only [zero_add, PowerSeries.coeff_zero_eq_constantCoeff] using
      PowerSeries.coeff_X_pow_mul (Q⁻¹*S) k 0
  rw [map_add, heuler, zero_add, hshift, map_zero] at hk
  rw [map_mul] at hk
  change (MvPowerSeries.constantCoeff Q⁻¹) * PowerSeries.constantCoeff S = 0 at hk
  rw [MvPowerSeries.constantCoeff_inv] at hk
  exact (mul_eq_zero.mp hk).resolve_left (inv_ne_zero hQ)

theorem polynomial_residue_obstruction (a : F) (p0 p Q S : F[X])
    (hp0 : p0 ≠ 0) (hQ : Q.eval a ≠ 0)
    (h : ((Polynomial.X - Polynomial.C a) * Q) *
        (p0 * p.derivative - p0.derivative * p) + p0^2 * S = 0) : S.eval a = 0 := by
  let shift := Polynomial.X + Polynomial.C a
  have hzero : (p0.comp shift : PowerSeries F) ≠ 0 := by
    simpa [shift, Polynomial.comp_X_add_C_eq_zero_iff] using hp0
  have hQzero : PowerSeries.constantCoeff (Q.comp shift : PowerSeries F) ≠ 0 := by
    simpa [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero,
      shift, Polynomial.eval_comp] using hQ
  have heq : (PowerSeries.X * (Q.comp shift : PowerSeries F)) *
      ((p0.comp shift : PowerSeries F) * PowerSeries.derivative (R := F) (p.comp shift : PowerSeries F) -
        PowerSeries.derivative (R := F) (p0.comp shift : PowerSeries F) * (p.comp shift : PowerSeries F)) +
      (p0.comp shift : PowerSeries F)^2 * (S.comp shift : PowerSeries F) = 0 := by
    have hh := congrArg (fun r : F[X] => (r.comp shift : PowerSeries F)) h
    simpa [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.sub_comp, Polynomial.pow_comp,
      PowerSeries.derivative_coe, Polynomial.derivative_comp, shift] using hh
  have hs := formal_residue_obstruction _ _ _ _ hzero hQzero heq
  simpa [Polynomial.constantCoeff_coe, Polynomial.coeff_zero_eq_eval_zero,
    shift, Polynomial.eval_comp] using hs

end FormalResidue

section DistinctPoles
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def poleProduct (a : ι → F) : F[X] := ∏ i, (Polynomial.X - Polynomial.C (a i))

def puncturedPoleProduct (a : ι → F) (i : ι) : F[X] :=
  ∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (a j))

omit [CharZero F] in
theorem poleProduct_eq (a : ι → F) (i : ι) :
    poleProduct a = (Polynomial.X - Polynomial.C (a i)) * puncturedPoleProduct a i := by
  exact (Finset.mul_prod_erase Finset.univ (fun j => Polynomial.X - Polynomial.C (a j))
    (Finset.mem_univ i)).symm

omit [CharZero F] in
theorem eval_puncturedPoleProduct_self_ne_zero (a : ι → F) (ha : Function.Injective a) (i : ι) :
    (puncturedPoleProduct a i).eval (a i) ≠ 0 := by
  simp only [puncturedPoleProduct, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  intro he
  have hji := (Finset.mem_erase.mp hj).1
  exact hji (ha he).symm

omit [CharZero F] in
theorem eval_puncturedPoleProduct_other (a : ι → F) (i j : ι) (hij : i ≠ j) :
    (puncturedPoleProduct a j).eval (a i) = 0 := by
  simp only [puncturedPoleProduct, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  apply Finset.prod_eq_zero (i := i)
  · simp [hij]
  · simp

theorem no_polynomial_log_primitive (a : ι → F) (ha : Function.Injective a)
    (p0 p : F[X]) (hp0 : p0 ≠ 0) (c : ι → F)
    (h : poleProduct a * (p0 * p.derivative - p0.derivative * p) +
      p0^2 * (∑ i, Polynomial.C (c i) * puncturedPoleProduct a i) = 0) :
    ∀ i, c i = 0 := by
  intro i
  have hr := polynomial_residue_obstruction (a i) p0 p (puncturedPoleProduct a i)
    (∑ j, Polynomial.C (c j) * puncturedPoleProduct a j) hp0
    (eval_puncturedPoleProduct_self_ne_zero a ha i) (by simpa [poleProduct_eq a i] using h)
  have heval : (∑ j, Polynomial.C (c j) * puncturedPoleProduct a j).eval (a i) =
      c i * (puncturedPoleProduct a i).eval (a i) := by
    rw [Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C]
    apply Finset.sum_eq_single i
    · intro j hj hji
      simp [eval_puncturedPoleProduct_other a i j (Ne.symm hji)]
    · simp
  rw [heval] at hr
  exact (mul_eq_zero.mp hr).resolve_right (eval_puncturedPoleProduct_self_ne_zero a ha i)

end DistinctPoles

end NCHitting

end

end OAI
