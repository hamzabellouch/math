import OAI.Algebra.FormulaHitting.Series
import OAI.Algebra.FormulaHitting.RationalTransfer
import OAI.Algebra.FormulaHitting.Generator
import OAI.Algebra.FormulaHitting.Evaluation
import OAI.Algebra.FormulaHitting.FormulaSeries
import Mathlib.Data.Rat.Cast.Lemmas

namespace OAI

noncomputable section
namespace NCHitting

open Matrix

variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
theorem jet_eq_zero_iff (d : ℕ) (a : PowerSeries F) :
    jet d a = 0 ↔ ∀ r < d, PowerSeries.coeff r a = 0 := by
  constructor
  · intro h r hr
    exact congrFun h ⟨r, hr⟩
  · intro h
    ext r
    exact h r.val r.isLt

omit [CharZero F] in
theorem jet_ne_zero_of_order_lt (d : ℕ) (a : PowerSeries F)
    (horder : a.order < (d : ℕ∞)) : jet d a ≠ 0 := by
  intro h
  exact (not_le_of_gt horder)
    (PowerSeries.nat_le_order a d ((jet_eq_zero_iff d a).mp h))

def integrationMatrix (d i : ℕ) : Matrix (Fin d) (Fin d) F :=
  fun r q => (matrixEntry i r.val q.val : F)

theorem integrationMatrix_apply (d i : ℕ) (r q : Fin d) :
    integrationMatrix (F := F) d i r q =
      if q.val < r.val then
        (-1 : F) ^ (r.val - q.val - 1) /
          ((r.val : F) * (i : F) ^ (r.val - q.val))
      else 0 := by
  by_cases h : q.val < r.val <;> simp [integrationMatrix, matrixEntry, h]

theorem jet_J (d i : ℕ) (a : PowerSeries F) :
    jet d (J i a) = integrationMatrix d i *ᵥ jet d a := by
  ext r
  rw [jet_apply, coeff_J]
  simp only [Matrix.mulVec, dotProduct, integrationMatrix_apply, jet_apply]
  let term := fun q =>
    (if q < r.val then (-1 : F) ^ (r.val - q - 1) /
      ((r.val : F) * (i : F) ^ (r.val - q)) else 0) * PowerSeries.coeff q a
  change _ = ∑ q : Fin d, term q.val
  rw [Fin.sum_univ_eq_sum_range term d]
  calc
    _ = ∑ q ∈ Finset.range r.val, term q := by
      apply Finset.sum_congr rfl
      intro q hq
      simp only [term, ite_eq_left (Finset.mem_range.mp hq)]
    _ = ∑ q ∈ Finset.range d, term q := by
      apply Finset.sum_subset (Finset.range_mono (Nat.le_of_lt r.isLt))
      intro q hqd hqr
      have h : ¬q < r.val := by simpa using hqr
      simp [term, h]

theorem jet_wordSeries {n : ℕ} (d : ℕ) (w : Word n) :
    jet d (wordSeries (F := F) w) =
      (w.map (fun i => integrationMatrix (F := F) d (i.val + 1))).prod *ᵥ
        jet d (1 : PowerSeries F) := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [wordSeries_cons, jet_J, ih]
    simp only [List.map_cons, List.prod_cons, Matrix.mulVec_mulVec]

omit [CharZero F] in
theorem generator_cast_eq_integrationMatrix {n s : ℕ} (hns : 2 ≤ n * s)
    (i : Fin n) :
    (fun r q => (generator n s i r q : F)) =
      integrationMatrix (F := F) (dimension n s) (i.val + 1) := by
  ext r q
  simp only [integrationMatrix, generator_entry hns]

theorem Formula.jet_wordSum_eq_eval_mulVec {n : ℕ} (f : Formula F n) (d : ℕ) :
    jet d (f.polynomial.sum fun w a => a • wordSeries (F := F) w) =
      f.eval (algebraMap F (Matrix (Fin d) (Fin d) F))
        (fun i => integrationMatrix (F := F) d (i.val + 1)) *ᵥ
          jet d (1 : PowerSeries F) := by
  rw [Formula.eval_eq_sum]
  simp only [Finsupp.sum, map_sum, map_smul, Matrix.sum_mulVec,
    ← Algebra.smul_def, Matrix.smul_mulVec, jet_wordSeries]

theorem Formula.eval_ne_zero_of_jet_wordSum_ne_zero {n : ℕ}
    (f : Formula F n) (d : ℕ)
    (hjet : jet d (f.polynomial.sum fun w a => a • wordSeries (F := F) w) ≠ 0) :
    f.eval (algebraMap F (Matrix (Fin d) (Fin d) F))
      (fun i => integrationMatrix (F := F) d (i.val + 1)) ≠ 0 := by
  intro h
  apply hjet
  rw [f.jet_wordSum_eq_eval_mulVec d, h, Matrix.zero_mulVec]

theorem Formula.jet_series_eq_eval_mulVec {n : ℕ} (f : Formula F n) (d : ℕ) :
    jet d f.series =
      f.eval (algebraMap F (Matrix (Fin d) (Fin d) F))
        (fun i => integrationMatrix (F := F) d (i.val + 1)) *ᵥ
          jet d (1 : PowerSeries F) := by
  rw [f.series_eq_smul_sum, f.jet_wordSum_eq_eval_mulVec]

theorem Formula.eval_ne_zero_of_jet_series_ne_zero {n : ℕ} (f : Formula F n) (d : ℕ)
    (hjet : jet d f.series ≠ 0) :
    f.eval (algebraMap F (Matrix (Fin d) (Fin d) F))
      (fun i => integrationMatrix (F := F) d (i.val + 1)) ≠ 0 := by
  apply f.eval_ne_zero_of_jet_wordSum_ne_zero d
  rwa [← f.series_eq_smul_sum]

theorem Formula.eval_generator_ne_zero_of_jet_series_ne_zero {n s : ℕ}
    (f : Formula F n) (hns : 2 ≤ n * s)
    (hjet : jet (dimension n s) f.series ≠ 0) :
    f.eval (Matrix.scalar (Fin (dimension n s)))
      (fun i r q => (generator n s i r q : F)) ≠ 0 := by
  have hT : (fun (i : Fin n) r q => (generator n s i r q : F)) =
      (fun i => integrationMatrix (F := F) (dimension n s) (i.val + 1)) := by
    funext i
    exact generator_cast_eq_integrationMatrix hns i
  rw [hT]
  exact f.eval_ne_zero_of_jet_series_ne_zero (dimension n s) hjet

end NCHitting

end

end OAI
