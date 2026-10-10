import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceCoefficientRounding

namespace OAI

/-! Actual deletion of zero source bonds after common-denominator rounding. -/

namespace ContinuumCoulomb.SourceZeroFilter
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

def keep (e : Bond) : Bool := decide (e.2.2 ≠ 0)

def step (acc : List Bond) (e : Bond) : List Bond := if keep e then e :: acc else acc

theorem fold_step (xs acc : List Bond) :
    xs.foldl step acc = (xs.filter keep).reverse ++ acc := by
  induction xs generalizing acc with
  | nil => simp
  | cons e xs ih =>
    rw [List.foldl_cons, ih]
    by_cases h : keep e = true
    · simp only [step, h, ite_true, List.filter_cons_of_pos h, List.reverse_cons, List.append_assoc,
        List.singleton_append]
    · have hn : keep e = false := Bool.eq_false_iff.mpr h
      simp only [step, hn, Bool.false_eq_true, ite_false, List.filter_cons_of_neg h]

theorem filter_code_le (xs : List Bond) :
    (listCode bondCode (xs.filter keep)).length ≤ (listCode bondCode xs).length := by
  induction xs with
  | nil => simp
  | cons e xs ih =>
    by_cases h : keep e = true
    · rw [List.filter_cons_of_pos h]
      simp only [listCode_length_cons]
      omega
    · rw [List.filter_cons_of_neg h]
      simp only [listCode_length_cons]
      omega

noncomputable def isZero : Procedure bondCode Procedure.boolCode (fun e => decide (e.2.2 = 0)) :=
  (Procedure.binaryZero.comp (Procedure.intAbs.comp (Procedure.ratNum.comp
    ((Procedure.second _ _).comp (Procedure.second _ _))))).congrFun (by
      intro e
      simp only [Function.comp_apply, Int.natAbs_eq_zero, Rat.num_eq_zero])

noncomputable def stepProgram : Procedure (prodCode bondCode (listCode bondCode)) (listCode bondCode)
    (fun x => step x.2 x.1) := by
  let test := isZero.comp (Procedure.first bondCode (listCode bondCode))
  let acc := Procedure.second bondCode (listCode bondCode)
  exact (Procedure.conditional test acc (Procedure.listCons bondCode)).congrFun (by
    intro x
    unfold step keep
    by_cases h : x.1.2.2 = 0 <;> simp [h])

noncomputable def foldProgram : Procedure (prodCode (listCode bondCode) (listCode bondCode))
    (listCode bondCode) (fun x => x.1.foldl step x.2) :=
  Procedure.foldList zeroBond stepProgram Polynomial.X (by
    intro xs acc i
    rw [fold_step]
    have h := listCode_length_append bondCode ((xs.take i).filter keep).reverse acc
    rw [listCode_length_rev] at h
    have ht := (filter_code_le (xs.take i)).trans (listCode_length_take_le bondCode i xs)
    simp only [Polynomial.eval_X]
    omega)

noncomputable def filterProgram : Procedure (listCode bondCode) (listCode bondCode)
    (fun xs => xs.filter keep) :=
  ((Procedure.listReverse bondCode zeroBond).comp (foldProgram.comp
    ((Procedure.identity (listCode bondCode)).pair
      (Procedure.constant (listCode bondCode) (listCode bondCode) [])))).congrFun
      (by intro xs; simp only [Function.comp_apply, id_eq, fold_step, List.append_nil, List.reverse_reverse])

theorem nonzero_mem (xs : List Bond) (e : Bond) (he : e ∈ xs.filter keep) : e.2.2 ≠ 0 := by
  exact of_decide_eq_true (List.mem_filter.mp he).2

end ContinuumCoulomb.SourceZeroFilter

end OAI
