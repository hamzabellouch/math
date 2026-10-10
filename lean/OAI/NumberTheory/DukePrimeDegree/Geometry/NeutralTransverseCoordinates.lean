import OAI.NumberTheory.DukePrimeDegree.Geometry.TransverseDiagonalFactorization

namespace OAI

/-! # The actual neutral coordinate in the upper-root chart

On the positive-diagonal chart the transverse slice is the product of its
unit-diagonal part and the trace-zero logarithmic diagonal. Right diagonal
translation fixes the first coordinate and translates the second. This is
the local center coordinate needed for comparison with the root kernel.
-/

noncomputable section
open Matrix Set
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

abbrev transverseNeutralSpace (n : ℕ) : Submodule ℝ (Fin n → ℝ) where
  carrier := {v | ∑ i, v i=0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    change ∑ i, v i=0 at hv
    change ∑ i, w i=0 at hw
    change ∑ i, (v+w) i=0
    simp only [Pi.add_apply,Finset.sum_add_distrib,hv,hw,add_zero]
  smul_mem' := by
    intro c v hv
    change ∑ i, v i=0 at hv
    change ∑ i, (c • v) i=0
    simp only [Pi.smul_apply,smul_eq_mul,←Finset.mul_sum,hv,mul_zero]

abbrev PositiveTransverse (n : ℕ) :=
  {s : UpperRootTransverse n // ∀ i, 0 < s.val.val i i}

abbrev UnitDiagonalTransverse (n : ℕ) :=
  {s : UpperRootTransverse n // ∀ i, s.val.val i i=1}

lemma transverseLogDiagonal_sum {n : ℕ} (s : PositiveTransverse n) :
    ∑ i, transverseLogDiagonal s.val i=0 := by
  simp only [transverseLogDiagonal,abs_of_pos (s.prop _)]
  rw [←Real.log_prod (fun i _ => (s.prop i).ne'),
    upperRootTransverse_diagonal_prod,Real.log_one]

def transverseNeutralCoordinate {n : ℕ} (s : PositiveTransverse n) :
    transverseNeutralSpace n :=
  ⟨transverseLogDiagonal s.val,transverseLogDiagonal_sum s⟩

def normalizedTransverse {n : ℕ} (s : PositiveTransverse n) : UpperRootTransverse n :=
  upperRootTransverseDiagonal (transverseNeutralCoordinate s).val
    (transverseNeutralCoordinate s).prop (-1) s.val

lemma normalizedTransverse_entry {n : ℕ} (s : PositiveTransverse n) (i j : Fin n) :
    (normalizedTransverse s).val.val i j=transverseColumnRatios s.val i j := by
  change (s.val.val*diagonalOneParameter _ _ (-1)).val i j=_
  rw [mul_diagonalOneParameter_entry]
  change s.val.val.val i j * Real.exp (Real.log |s.val.val.val j j| * (-1)) = _
  rw [abs_of_pos (s.prop j),mul_neg_one,Real.exp_neg,Real.exp_log (s.prop j)]
  rfl

lemma normalizedTransverse_diagonal {n : ℕ} (s : PositiveTransverse n) (i : Fin n) :
    (normalizedTransverse s).val.val i i=1 := by
  rw [normalizedTransverse_entry]
  exact div_self (s.prop i).ne'

def transverseUnitCoordinate {n : ℕ} (s : PositiveTransverse n) :
    UnitDiagonalTransverse n :=
  ⟨normalizedTransverse s,normalizedTransverse_diagonal s⟩

def transverseNeutralReconstruct {n : ℕ}
    (z : UnitDiagonalTransverse n × transverseNeutralSpace n) : PositiveTransverse n :=
  ⟨upperRootTransverseDiagonal z.2.val z.2.prop 1 z.1.val,by
    intro i
    change (z.1.val.val*diagonalOneParameter z.2.val z.2.prop 1).val i i > 0
    rw [mul_diagonalOneParameter_entry,z.1.prop i,one_mul]
    exact Real.exp_pos _⟩

lemma transverseNeutralReconstruct_coordinates {n : ℕ} (s : PositiveTransverse n) :
    transverseNeutralReconstruct (transverseUnitCoordinate s,transverseNeutralCoordinate s)=s := by
  apply Subtype.ext
  change upperRootTransverseDiagonal (transverseNeutralCoordinate s).val
    (transverseNeutralCoordinate s).prop 1
    (upperRootTransverseDiagonal (transverseNeutralCoordinate s).val
      (transverseNeutralCoordinate s).prop (-1) s.val)=s.val
  rw [←upperRootTransverseDiagonal_add,neg_add_cancel,upperRootTransverseDiagonal_zero]

lemma transverseNeutralCoordinate_reconstruct {n : ℕ}
    (z : UnitDiagonalTransverse n × transverseNeutralSpace n) :
    transverseNeutralCoordinate (transverseNeutralReconstruct z)=z.2 := by
  apply Subtype.ext
  funext i
  change Real.log |(z.1.val.val*diagonalOneParameter z.2.val z.2.prop 1).val i i|=z.2.val i
  rw [mul_diagonalOneParameter_entry,z.1.prop i,one_mul,mul_one,
    abs_of_pos (Real.exp_pos _),Real.log_exp]

lemma transverseUnitCoordinate_reconstruct {n : ℕ}
    (z : UnitDiagonalTransverse n × transverseNeutralSpace n) :
    transverseUnitCoordinate (transverseNeutralReconstruct z)=z.1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext i j
  change (normalizedTransverse (transverseNeutralReconstruct z)).val.val i j =
    z.1.val.val.val i j
  rw [normalizedTransverse_entry]
  change (z.1.val.val*diagonalOneParameter z.2.val z.2.prop 1).val i j /
    (z.1.val.val*diagonalOneParameter z.2.val z.2.prop 1).val j j = z.1.val.val.val i j
  rw [mul_diagonalOneParameter_entry,mul_diagonalOneParameter_entry,
    z.1.prop j,one_mul,mul_div_cancel_right₀ _ (Real.exp_ne_zero _)]

lemma continuous_transverseNeutralCoordinate (n : ℕ) :
    Continuous (@transverseNeutralCoordinate n) :=
  ((continuous_transverseLogDiagonal n).comp continuous_subtype_val).subtype_mk _

lemma continuous_transverseUnitCoordinate (n : ℕ) :
    Continuous (@transverseUnitCoordinate n) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  change Continuous (fun s : PositiveTransverse n => (normalizedTransverse s).val.val)
  have he : (fun s : PositiveTransverse n => (normalizedTransverse s).val.val)=
      fun s => transverseColumnRatios s.val := by
    funext s i j
    exact normalizedTransverse_entry s i j
  rw [he]
  exact (continuous_transverseColumnRatios n).comp continuous_subtype_val

lemma continuous_transverseNeutralReconstruct (n : ℕ) :
    Continuous (@transverseNeutralReconstruct n) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun z : UnitDiagonalTransverse n × transverseNeutralSpace n =>
    (z.1.val.val*diagonalOneParameter z.2.val z.2.prop 1).val i j)
  simp only [mul_diagonalOneParameter_entry,mul_one]
  have h₁ : Continuous (fun z : UnitDiagonalTransverse n × transverseNeutralSpace n =>
      z.1.val) := continuous_subtype_val.comp continuous_fst
  have h₂ : Continuous (fun z : UnitDiagonalTransverse n × transverseNeutralSpace n =>
      z.1.val.val) := continuous_subtype_val.comp h₁
  have hm : Continuous (fun z : UnitDiagonalTransverse n × transverseNeutralSpace n =>
      z.1.val.val.val) := continuous_subtype_val.comp h₂
  have he : Continuous (fun z : UnitDiagonalTransverse n × transverseNeutralSpace n =>
      z.2.val j) := (continuous_apply j).comp (continuous_subtype_val.comp continuous_snd)
  exact ((continuous_apply j).comp ((continuous_apply i).comp hm)).mul
    (Real.continuous_exp.comp he)

def neutralTransverseHomeomorph (n : ℕ) :
    PositiveTransverse n ≃ₜ UnitDiagonalTransverse n × transverseNeutralSpace n where
  toFun s := (transverseUnitCoordinate s,transverseNeutralCoordinate s)
  invFun := transverseNeutralReconstruct
  left_inv := transverseNeutralReconstruct_coordinates
  right_inv z := Prod.ext (transverseUnitCoordinate_reconstruct z)
    (transverseNeutralCoordinate_reconstruct z)
  continuous_toFun := (continuous_transverseUnitCoordinate n).prodMk
    (continuous_transverseNeutralCoordinate n)
  continuous_invFun := continuous_transverseNeutralReconstruct n

def positiveTransverseDiagonal {n : ℕ} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i=0) (t : ℝ) (s : PositiveTransverse n) : PositiveTransverse n :=
  ⟨upperRootTransverseDiagonal ell hell t s.val,by
    intro i
    change (s.val.val*diagonalOneParameter ell hell t).val i i > 0
    rw [mul_diagonalOneParameter_entry]
    exact mul_pos (s.prop i) (Real.exp_pos _)⟩

lemma transverseNeutralCoordinate_diagonal {n : ℕ} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i=0) (t : ℝ) (s : PositiveTransverse n) :
    (transverseNeutralCoordinate (positiveTransverseDiagonal ell hell t s)).val =
      fun i => (transverseNeutralCoordinate s).val i+ell i*t :=
  transverseLogDiagonal_diagonal ell hell t s.val

lemma transverseUnitCoordinate_diagonal {n : ℕ} (ell : Fin n → ℝ)
    (hell : ∑ i, ell i=0) (t : ℝ) (s : PositiveTransverse n) :
    transverseUnitCoordinate (positiveTransverseDiagonal ell hell t s)=
      transverseUnitCoordinate s := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext i j
  change (normalizedTransverse (positiveTransverseDiagonal ell hell t s)).val.val i j =
    (normalizedTransverse s).val.val i j
  rw [normalizedTransverse_entry,normalizedTransverse_entry]
  exact congrFun (congrFun (transverseColumnRatios_diagonal ell hell t s.val) i) j

end DukePrimeDegree

end

end OAI
