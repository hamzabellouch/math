import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section

namespace NCHitting

open PowerSeries Matrix

variable {F : Type*} [Field F]

def derivativeIter : ℕ → PowerSeries F → PowerSeries F
  | 0, f => f
  | j + 1, f => PowerSeries.derivative (R := F) (derivativeIter j f)

@[simp] theorem derivativeIter_zero (f : PowerSeries F) : derivativeIter 0 f = f := rfl

@[simp] theorem derivativeIter_add (j : ℕ) (f g : PowerSeries F) :
    derivativeIter j (f + g) = derivativeIter j f + derivativeIter j g := by
  induction j with
  | zero => rfl
  | succ j ih => simp [derivativeIter, ih]

@[simp] theorem derivativeIter_smul (j : ℕ) (c : F) (f : PowerSeries F) :
    derivativeIter j (c • f) = c • derivativeIter j f := by
  induction j with
  | zero => rfl
  | succ j ih => simp [derivativeIter, ih]

theorem derivativeIter_sum {ι : Type*} (j : ℕ) (s : Finset ι) (f : ι → PowerSeries F) :
    derivativeIter j (∑ i ∈ s, f i) = ∑ i ∈ s, derivativeIter j (f i) := by
  induction j with
  | zero => rfl
  | succ j ih => simp [derivativeIter, ih]

theorem coeff_derivativeIter (j r : ℕ) (f : PowerSeries F) :
    PowerSeries.coeff r (derivativeIter j f) =
      PowerSeries.coeff (r+j) f * ((r+j).descFactorial j : F) := by
  induction j generalizing r with
  | zero => simp [derivativeIter]
  | succ j ih =>
    rw [derivativeIter, PowerSeries.coeff_derivative, ih]
    have he : r + 1 + j = r + (j + 1) := by omega
    have hs : r + (j + 1) - j = r + 1 := by omega
    rw [he, Nat.descFactorial_succ, hs, Nat.cast_mul]
    push_cast
    ring

theorem coeff_X_pow_derivativeIter (j r : ℕ) (f : PowerSeries F) :
    PowerSeries.coeff r (PowerSeries.X ^ j * derivativeIter j f) =
      PowerSeries.coeff r f * (r.descFactorial j : F) := by
  rw [PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_derivativeIter, Nat.sub_add_cancel h]
  · rw [Nat.descFactorial_of_lt (by omega), Nat.cast_zero, mul_zero]

def derivativeTail (f : PowerSeries F) (a j : ℕ) : PowerSeries F :=
  PowerSeries.mk fun r => PowerSeries.coeff (r+a) f * ((r+a).descFactorial j : F)

@[simp] theorem coeff_derivativeTail (f : PowerSeries F) (a j r : ℕ) :
    PowerSeries.coeff r (derivativeTail f a j) =
      PowerSeries.coeff (r+a) f * ((r+a).descFactorial j : F) := by
  simp [derivativeTail]

theorem X_pow_derivativeIter_eq (f : PowerSeries F) (a j : ℕ)
    (h : ∀ r < a, PowerSeries.coeff r f = 0) :
    PowerSeries.X ^ j * derivativeIter j f =
      PowerSeries.X ^ a * derivativeTail f a j := by
  ext r
  rw [coeff_X_pow_derivativeIter, PowerSeries.coeff_X_pow_mul']
  split_ifs with ha
  · rw [coeff_derivativeTail, Nat.sub_add_cancel ha]
  · rw [h r (by omega), zero_mul]

def wronskianMatrix {k : ℕ} (b : Fin k → PowerSeries F) :
    Matrix (Fin k) (Fin k) (PowerSeries F) :=
  fun j l => derivativeIter j.val (b l)

def wronskian {k : ℕ} (b : Fin k → PowerSeries F) : PowerSeries F :=
  (wronskianMatrix b).det

theorem wronskian_linearCombination {k : ℕ} (b : Fin k → PowerSeries F)
    (C : Matrix (Fin k) (Fin k) F) :
    wronskian (fun l => ∑ i : Fin k, C i l • b i) =
      wronskian b * PowerSeries.C C.det := by
  have he : wronskianMatrix (fun l => ∑ i : Fin k, C i l • b i) =
      wronskianMatrix b * (PowerSeries.C : F →+* PowerSeries F).mapMatrix C := by
    funext j l
    change derivativeIter j.val (∑ i : Fin k, C i l • b i) =
      ∑ i : Fin k, derivativeIter j.val (b i) * PowerSeries.C (C i l)
    rw [derivativeIter_sum]
    simp only [derivativeIter_smul]
    simp only [PowerSeries.smul_eq_C_mul]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [wronskian, he, Matrix.det_mul, ← RingHom.map_det]
  rfl

def normalizedWronskianMatrix {k : ℕ} (b : Fin k → PowerSeries F)
    (a : Fin k → ℕ) : Matrix (Fin k) (Fin k) (PowerSeries F) :=
  fun j l => derivativeTail (b l) (a l) j.val

theorem wronskianMatrix_scaling {k : ℕ} (b : Fin k → PowerSeries F)
    (a : Fin k → ℕ) (h : ∀ l r, r < a l → PowerSeries.coeff r (b l) = 0) :
    Matrix.diagonal (fun j : Fin k => (PowerSeries.X : PowerSeries F)^j.val) *
      wronskianMatrix b =
    normalizedWronskianMatrix b a *
      Matrix.diagonal (fun l => (PowerSeries.X : PowerSeries F)^(a l)) := by
  ext j l
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, wronskianMatrix,
    normalizedWronskianMatrix]
  rw [X_pow_derivativeIter_eq (b l) (a l) j.val (h l), mul_comm]

theorem wronskian_det_scaling {k : ℕ} (b : Fin k → PowerSeries F)
    (a : Fin k → ℕ) (h : ∀ l r, r < a l → PowerSeries.coeff r (b l) = 0) :
    ((∏ j : Fin k, (PowerSeries.X : PowerSeries F)^j.val) * wronskian b) =
      (normalizedWronskianMatrix b a).det *
        ∏ l : Fin k, (PowerSeries.X : PowerSeries F)^(a l) := by
  have hd := congrArg Matrix.det (wronskianMatrix_scaling b a h)
  simpa only [Matrix.det_mul, Matrix.det_diagonal, wronskian] using hd

theorem det_descFactorial {k : ℕ} (a : Fin k → ℕ) :
    (Matrix.of fun j l : Fin k => ((a l).descFactorial j.val : F)).det =
      (Matrix.vandermonde fun l => (a l : F)).det := by
  have hh := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
    (fun l : Fin k => (a l : F)) (fun j : Fin k => descPochhammer F j.val)
    (fun j => descPochhammer_natDegree F j.val)
    (fun j => monic_descPochhammer F j.val)
  rw [← Matrix.det_transpose]
  change (Matrix.of fun i j : Fin k => ((a i).descFactorial j.val : F)).det = _
  simpa only [descPochhammer_eval_eq_descFactorial] using hh.symm

theorem det_descFactorial_ne_zero [CharZero F] {k : ℕ} (a : Fin k → ℕ)
    (ha : Function.Injective a) :
    (Matrix.of fun j l : Fin k => ((a l).descFactorial j.val : F)).det ≠ 0 := by
  rw [det_descFactorial]
  apply Matrix.det_vandermonde_ne_zero_iff.mpr
  exact (Nat.cast_injective (R := F)).comp ha

theorem normalizedWronskian_constant_ne_zero [CharZero F] {k : ℕ} (b : Fin k → PowerSeries F)
    (a : Fin k → ℕ) (ha : Function.Injective a)
    (hb : ∀ l, PowerSeries.coeff (a l) (b l) ≠ 0) :
    PowerSeries.constantCoeff (normalizedWronskianMatrix b a).det ≠ 0 := by
  have he : (PowerSeries.constantCoeff : PowerSeries F →+* F).mapMatrix
      (normalizedWronskianMatrix b a) =
      (Matrix.of fun j l : Fin k => ((a l).descFactorial j.val : F)) *
        Matrix.diagonal (fun l => PowerSeries.coeff (a l) (b l)) := by
    funext j l
    rw [Matrix.mul_diagonal]
    change PowerSeries.constantCoeff (derivativeTail (b l) (a l) j.val) =
      ((a l).descFactorial j.val : F) * PowerSeries.coeff (a l) (b l)
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_derivativeTail, Nat.zero_add]
    exact mul_comm _ _
  rw [RingHom.map_det, he, Matrix.det_mul, Matrix.det_diagonal]
  exact mul_ne_zero (det_descFactorial_ne_zero a ha) (Finset.prod_ne_zero_iff.mpr (fun l _ => hb l))

theorem wronskian_order_sum [CharZero F] {k : ℕ} (b : Fin k → PowerSeries F)
    (a : Fin k → ℕ) (ha : Function.Injective a)
    (hb : ∀ l, PowerSeries.coeff (a l) (b l) ≠ 0)
    (hz : ∀ l r, r < a l → PowerSeries.coeff r (b l) = 0) :
    wronskian b ≠ 0 ∧
      (wronskian b).order.toNat + (∑ j : Fin k, j.val) = ∑ l : Fin k, a l := by
  have hc := normalizedWronskian_constant_ne_zero b a ha hb
  have hn : (normalizedWronskianMatrix b a).det ≠ 0 := by
    intro h
    exact hc (by rw [h, map_zero])
  have ho : (normalizedWronskianMatrix b a).det.order = 0 := by
    apply PowerSeries.order_eq_nat.mpr
    exact ⟨by simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hc,
      fun r hr => (Nat.not_lt_zero r hr).elim⟩
  have he := wronskian_det_scaling b a hz
  simp only [Finset.prod_pow_eq_pow_sum] at he
  have hw : wronskian b ≠ 0 := by
    intro h
    rw [h, mul_zero] at he
    exact (mul_ne_zero hn (pow_ne_zero _ PowerSeries.X_ne_zero)) he.symm
  refine ⟨hw, ?_⟩
  have hord := congrArg PowerSeries.order he
  rw [PowerSeries.order_mul, PowerSeries.order_mul, ho, zero_add,
    PowerSeries.order_X_pow, PowerSeries.order_X_pow,
    ← PowerSeries.coe_toNat_order hw] at hord
  have heq : (∑ j : Fin k, j.val) + (wronskian b).order.toNat = ∑ l : Fin k, a l := by
    exact_mod_cast hord
  omega

end NCHitting

end

end OAI
