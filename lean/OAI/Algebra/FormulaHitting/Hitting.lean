import OAI.Algebra.FormulaHitting.Multiplicity
import OAI.Algebra.FormulaHitting.DimensionBound
import OAI.Algebra.FormulaHitting.SystemOutput
import OAI.Algebra.FormulaHitting.SeriesFaithfulness
import OAI.Algebra.FormulaHitting.JetMatrix

namespace OAI

noncomputable section
namespace NCHitting

open Matrix PowerSeries

variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
theorem AcyclicRepresentation.scalarOutput_eq_contract {n : ℕ}
    (R : AcyclicRepresentation F n) :
    systemScalarOutput R.u R.v R.fundamentalMatrix =
      R.contract R.fundamentalMatrix := by
  simp only [systemScalarOutput, AcyclicRepresentation.contract,
    LinearMap.coe_mk, AddHom.coe_mk, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

theorem Formula.series_order_lt {n : ℕ} (f : Formula F n) (hn : 0 < n)
    (hf : f.coeff ≠ 0) :
    f.series.order.toNat <
      (n-1) * (Fintype.card f.representation.State).choose 2 +
        Fintype.card f.representation.State := by
  let R := f.representation
  have hq : AcyclicRepresentation.denominator (F := F) n ≠ 0 := by
    intro hz
    have he := AcyclicRepresentation.denominator_eval_zero_ne (F := F) (n := n)
    exact he (by rw [hz, Polynomial.eval_zero])
  have ho : systemScalarOutput R.u R.v R.fundamentalMatrix = f.series :=
    R.scalarOutput_eq_contract.trans f.system_output_eq_series
  have hbound := system_multiplicity n hn
    (AcyclicRepresentation.denominator (F := F) n) R.systemNumerator R.u R.v
    R.fundamentalMatrix (AcyclicRepresentation.denominator_degree (F := F) (n := n))
    hq R.systemNumerator_degree
    (R.fundamentalMatrix_isUnit f.representation_card_pos)
    R.fundamentalMatrix_polynomial_system
    (by rw [ho]; exact f.series_ne_zero hf)
  rwa [ho] at hbound

theorem Formula.eval_generator_one_ne_zero (f : Formula F 1)
    (hs : f.size ≤ 1) (hf : f.coeff ≠ 0) :
    f.eval (Matrix.scalar (Fin (dimension 1 1)))
      (fun i r q => (generator 1 1 i r q : F)) ≠ 0 := by
  let r : Fin (dimension 1 1) := ⟨0, by decide⟩
  rcases (Formula.size_le_one_iff f).mp hs with ⟨a, rfl⟩ | ⟨i, rfl⟩
  · intro hz
    have ha : a = 0 := by
      have he := congrFun (congrFun hz r) r
      simpa [Formula.eval, Matrix.scalar_apply] using he
    apply hf
    funext w
    simp [Formula.coeff, ha]
  · intro hz
    have he := congrFun (congrFun hz r) r
    simp [Formula.eval, generator_one] at he

theorem Formula.eval_generator_ne_zero {n s : ℕ} (f : Formula F n)
    (hn : 0 < n) (hs : 0 < s) (hsize : f.size ≤ s) (hf : f.coeff ≠ 0) :
    f.eval (Matrix.scalar (Fin (dimension n s)))
      (fun i r q => (generator n s i r q : F)) ≠ 0 := by
  by_cases he : n = 1 ∧ s = 1
  · rcases he with ⟨rfl, rfl⟩
    exact f.eval_generator_one_ne_zero hsize hf
  · have hns : 2 ≤ n*s := by
      have hnle : n ≤ n*s := by simpa using Nat.mul_le_mul_left n hs
      have hsle : s ≤ n*s := by simpa using Nat.mul_le_mul_right s hn
      omega
    have hm : Fintype.card f.representation.State ≤ 2*s :=
      f.representation_card_le.trans (Nat.mul_le_mul_left 2 hsize)
    have hbound : f.series.order.toNat < dimension n s := by
      rw [dimension_eq hns]
      exact (f.series_order_lt hn hf).trans_le (multiplicity_dimension_bound hn hs hm)
    apply f.eval_generator_ne_zero_of_jet_series_ne_zero hns
    apply jet_ne_zero_of_order_lt
    rw [← PowerSeries.coe_toNat_order (f.series_ne_zero hf), ENat.natCast_lt_natCast]
    exact hbound

theorem universal_hitting (n s : ℕ) (hn : 1 ≤ n) (hs : 1 ≤ s)
    (F : Type*) [Field F] [CharZero F] (f : Formula F n)
    (hsize : f.size ≤ s) (hf : ∃ w, f.coeff w ≠ 0) :
    f.eval (Matrix.scalar (Fin (dimension n s)))
      (fun i r q => (generator n s i r q : F)) ≠ 0 := by
  apply f.eval_generator_ne_zero hn hs hsize
  intro hz
  obtain ⟨w, hw⟩ := hf
  exact hw (congrFun hz w)

end NCHitting

end

end OAI
