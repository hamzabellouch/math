import OAI.LinearAlgebra.MatrixMultiplication.Numerical.AllFieldCertificatesReplay

namespace OAI

/-! Exact rational intervals, logarithm bounds and arithmetic circuit soundness. -/

namespace MatrixMultiplication.AllFieldCertificates.Replay

def Op.refs : Op → List ℕ
  | .constant _ => []
  | .add i j => [i,j]
  | .neg i => [i]
  | .mul i j => [i,j]
  | .inv i => [i]
  | .log i => [i]

theorem Op.value_congr (op : Op) (v w : ℕ → ℝ)
    (h : ∀ j ∈ op.refs, v j = w j) : op.value v = op.value w := by
  cases op <;> simp_all [Op.refs, Op.value]

theorem evalFrom_size (ops : List Op) (vs : Array ℝ) :
    (evalFrom ops vs).size = vs.size + ops.length := by
  induction ops generalizing vs with
  | nil => simp [evalFrom]
  | cons op ops ih =>
    change (evalFrom ops (vs.push (op.value (fun i => vs[i]?.getD 0)))).size = _
    rw [ih]
    simp only [Array.size_push, List.length_cons]
    omega

theorem evalFrom_append_singleton (ops : List Op) (op : Op) (vs : Array ℝ) :
    evalFrom (ops ++ [op]) vs =
      (evalFrom ops vs).push (op.value (fun i => (evalFrom ops vs)[i]?.getD 0)) := by
  rw [evalFrom_append]
  rfl

theorem evalFrom_get_closed (ops : List Op) (i : ℕ) (op : Op)
    (hget : ops[i]? = some op) (hdeps : ∀ j ∈ op.refs, j < i) :
    (evalFrom ops #[])[i]?.getD 0 =
      op.value (fun j => (evalFrom ops #[])[j]?.getD 0) := by
  induction ops using List.reverseRecOn with
  | nil => simp at hget
  | append_singleton ops last ih =>
    have hs : (evalFrom ops #[]).size = ops.length := by simp [evalFrom_size]
    by_cases hi : i < ops.length
    · have hg : ops[i]? = some op := by
        simpa only [List.getElem?_append_left hi] using hget
      have old := ih hg
      rw [evalFrom_append_singleton]
      rw [Array.getElem?_push, ite_eq_right (by simpa only [hs] using (Nat.ne_of_lt hi))]
      rw [old]
      apply Op.value_congr
      intro j hj
      have hjlt : j < (evalFrom ops #[]).size := by
        rw [hs]
        exact (hdeps j hj).trans hi
      rw [Array.getElem?_push, ite_eq_right (Nat.ne_of_lt hjlt)]
    · have hbound : i < (ops ++ [last]).length :=
        (List.getElem?_eq_some_iff.mp hget).choose
      have hei : i = ops.length := by
        simp only [List.length_append, List.length_singleton] at hbound
        omega
      subst i
      have heop : last = op := by
        simpa only [List.getElem?_append_right (le_refl ops.length), Nat.sub_self,
          List.getElem?_cons_zero, Option.some.injEq] using hget
      subst op
      rw [evalFrom_append_singleton]
      have hindex :
          ((evalFrom ops #[]).push (last.value (fun j => (evalFrom ops #[])[j]?.getD 0)))[ops.length]? =
            some (last.value (fun j => (evalFrom ops #[])[j]?.getD 0)) := by
        rw [← hs, Array.getElem?_push_size]
      rw [hindex, Option.getD_some]
      apply Op.value_congr
      intro j hj
      have hjlt : j < (evalFrom ops #[]).size := by
        rw [hs]
        exact hdeps j hj
      rw [Array.getElem?_push, ite_eq_right (Nat.ne_of_lt hjlt)]

theorem Program.eval_get (p : Program) (i : ℕ) (op : Op)
    (hget : p[i]? = some op) (hdeps : ∀ j ∈ op.refs, j < i) :
    p.eval[i]?.getD 0 = op.value (fun j => p.eval[j]?.getD 0) := by
  have h := evalFrom_get_closed p.toList i op (by simpa using hget) hdeps
  simpa only [evalFrom, Array.foldl_toList, Program.eval] using h

def Program.WellFormed (p : Program) : Prop :=
  ∀ (i : ℕ) (op : Op), p[i]? = some op → ∀ j ∈ op.refs, j < i

theorem Program.eval_get_of_wellFormed (p : Program) (hw : p.WellFormed)
    (i : ℕ) (op : Op) (hget : p[i]? = some op) :
    p.eval[i]?.getD 0 = op.value (fun j => p.eval[j]?.getD 0) :=
  p.eval_get i op hget (hw i op hget)

end MatrixMultiplication.AllFieldCertificates.Replay

end OAI
