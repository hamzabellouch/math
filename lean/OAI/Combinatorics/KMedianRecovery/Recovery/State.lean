import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.FormTrans

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility
open scoped Matrix

structure State (n : ℕ) where
  shape : Matrix (Fin n) (Fin n) ℚ
  center : Fin n → ℚ

def badRow {n : ℕ} (rows : List (Row n)) (c : Fin n → ℚ) : Option (Row n) :=
  rows.find? (fun r => decide (r.bound<r.value c))

def advance {n : ℕ} (D : ℕ) (rows : List (Row n)) (S : State n) : State n :=
  match badRow rows S.center with
  | none => S
  | some r => if r.coeff=0 then S else
      ⟨rationalStepShape D S.shape r.coeff,rationalStepCenter S.shape r.coeff S.center⟩

def iterate {n : ℕ} (D : ℕ) (rows : List (Row n)) (S : State n) : ℕ → State n
  | 0 => S
  | t+1 => advance D rows (iterate D rows S t)

lemma badRow_none {n : ℕ} (rows : List (Row n)) (c : Fin n → ℚ) :
    badRow rows c=none ↔ ∀ r∈rows, r.Holds c := by
  simp only [badRow,List.find?_eq_none,decide_eq_true_eq,not_lt,Row.Holds]

lemma badRow_some {n : ℕ} (rows : List (Row n)) (c : Fin n → ℚ) (r : Row n)
    (hr : badRow rows c=some r) : r∈rows ∧ r.bound<r.value c := by
  have hb := List.find?_some (p:=fun q : Row n => decide (q.bound<q.value c)) hr
  exact ⟨List.mem_of_find?_eq_some hr,of_decide_eq_true hb⟩

lemma advance_eq_self {n : ℕ} (D : ℕ) (rows : List (Row n)) (S : State n)
    (h : ∀ r∈rows, r.Holds S.center) : advance D rows S=S := by
  simp only [advance,(badRow_none rows S.center).mpr h]

lemma iterate_stable {n : ℕ} (D : ℕ) (rows : List (Row n)) (S : State n)
    (t k : ℕ) (ht : ∀ r∈rows, r.Holds (iterate D rows S t).center) :
    iterate D rows S (t+k)=iterate D rows S t := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ,iterate,ih,advance_eq_self D rows _ ht]

lemma badRow_nonzero {n : ℕ} (rows : List (Row n)) (c : Fin n → ℚ) (r : Row n)
    (hr : badRow rows c=some r) (x : Fin n → ℝ) (hx : ∀ q∈rows, q.RealHolds x) :
    r.coeff≠0 := by
  intro he
  obtain ⟨hmem,hbad⟩ := badRow_some rows c r hr
  have hh := hx r hmem
  simp only [Row.RealHolds,Row.realValue,he,Pi.zero_apply,Rat.cast_zero,zero_mul,
    Finset.sum_const_zero] at hh
  have hhq : (0:ℚ)≤r.bound := (Rat.cast_nonneg (K:=ℝ)).mp hh
  simp only [Row.value,he,Pi.zero_apply,zero_mul,Finset.sum_const_zero] at hbad
  exact (not_lt_of_ge hhq) hbad

lemma advance_pos_lower {n : ℕ} (D : ℕ) (hD : 0<D) (rows : List (Row n)) (S : State n)
    (hn : 2≤n) (hS : (realMatrix S.shape).PosDef) :
    (realMatrix (advance D rows S).shape).PosDef ∧
    (realMatrix (advance D rows S).shape-(1/3:ℝ) • realMatrix S.shape).PosSemidef := by
  unfold advance
  split
  · exact ⟨hS,by simpa only [one_smul] using form_scalar_mono _ hS.posSemidef (1/3) 1 (by norm_num)⟩
  · split_ifs with ha
    · exact ⟨hS,by simpa only [one_smul] using form_scalar_mono _ hS.posSemidef (1/3) 1 (by norm_num)⟩
    · exact ⟨stepShape_pos D hD _ _ (by simpa using hn) hS ha,
        stepShape_lower D hD _ _ (by simpa using hn) hS ha⟩

lemma iterate_pos {n : ℕ} (D : ℕ) (hD : 0<D) (rows : List (Row n)) (S : State n)
    (hn : 2≤n) (hS : (realMatrix S.shape).PosDef) (t : ℕ) :
    (realMatrix (iterate D rows S t).shape).PosDef := by
  induction t with
  | zero => exact hS
  | succ t ih => exact (advance_pos_lower D hD rows _ hn ih).1

lemma iterate_shape_lower {n : ℕ} (D : ℕ) (hD : 0<D) (rows : List (Row n)) (S : State n)
    (hn : 2≤n) (hS : (realMatrix S.shape).PosDef) (h0 : (realMatrix S.shape-1).PosSemidef) (t : ℕ) :
    (realMatrix (iterate D rows S t).shape-(1/3:ℝ)^t • (1:Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  apply iterate_lower (fun t => realMatrix (iterate D rows S t).shape) h0 _ t
  intro k
  exact (advance_pos_lower D hD rows _ hn (iterate_pos D hD rows S hn hS k)).2

lemma advance_contains {n : ℕ} (D : ℕ) (hD : 0<D) (rows : List (Row n)) (S : State n)
    (hn : 2≤n) (hS : (realMatrix S.shape).PosDef) (x : Fin n → ℝ)
    (hx : ∀ q∈rows, q.RealHolds x)
    (hball : quad (realMatrix S.shape)⁻¹ (x-realVector S.center)≤1) :
    quad (realMatrix (advance D rows S).shape)⁻¹ (x-realVector (advance D rows S).center)≤1 := by
  unfold advance
  split
  · exact hball
  next r hr =>
    have ha := badRow_nonzero rows S.center r hr x hx
    rw [ite_eq_right ha]
    apply rational_step_contains D hD S.shape r.coeff S.center (by simpa using hn) hS ha x hball
    obtain ⟨hmem,hbad⟩ := badRow_some rows S.center r hr
    have hh := hx r hmem
    have hh' : (r.bound:ℝ)<(r.value S.center:ℝ) := Rat.cast_lt.mpr hbad
    have he : realVector r.coeff ⬝ᵥ (x-realVector S.center)=r.realValue x-(r.value S.center:ℝ) := by
      simp only [realVector,dotProduct,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib,
        Row.realValue,Row.value,Rat.cast_sum,Rat.cast_mul]
    rw [he]
    exact sub_nonpos.mpr (hh.trans hh'.le)

lemma iterate_contains {n : ℕ} (D : ℕ) (hD : 0<D) (rows : List (Row n)) (S : State n)
    (hn : 2≤n) (hS : (realMatrix S.shape).PosDef) (x : Fin n → ℝ)
    (hx : ∀ q∈rows, q.RealHolds x)
    (hball : quad (realMatrix S.shape)⁻¹ (x-realVector S.center)≤1) (t : ℕ) :
    quad (realMatrix (iterate D rows S t).shape)⁻¹ (x-realVector (iterate D rows S t).center)≤1 := by
  induction t with
  | zero => exact hball
  | succ t ih => exact advance_contains D hD rows _ hn (iterate_pos D hD rows S hn hS t) x hx ih

end MetricKMedianRecovery.Ellipsoid

end OAI
