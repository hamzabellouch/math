import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.ExtraNodes
import OAI.Analysis.MutuallyUnbiased.Certificate.CompareMerge
import OAI.Analysis.MutuallyUnbiased.Moments.GramNormalization

namespace OAI

namespace MUB6.Certificate.Integer.Sparse

variable {ι κ : Type*}

def substitute (v : Sparse κ) (rows : κ → Sparse ι) : Sparse ι :=
  v.flatMap fun p => scale p.2 (rows p.1)

theorem eval_substitute (v : Sparse κ) (rows : κ → Sparse ι) (x : ι → ℝ) :
    eval (substitute v rows) x = eval v (fun k => eval (rows k) x) := by
  induction v with
  | nil => rfl
  | cons p v ih =>
    simp only [substitute, List.flatMap_cons, eval_append, eval_scale, eval_cons] at *
    rw [ih]

theorem eval_mul_left (v : Sparse ι) (x : ι → ℝ) (c : ℝ) :
    eval v (fun i => c * x i) = c * eval v x := by
  induction v with
  | nil => simp
  | cons p v ih => simp only [eval_cons, ih]; ring

end MUB6.Certificate.Integer.Sparse

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

abbrev OriginalKey := Fin 5502 ⊕ Fin 8

noncomputable def originalVector (B : Fin 7 → Basis) : OriginalKey → ℝ :=
  Sum.elim (fun i => mixedVector B (Sum.inr i))
    ![mixedMoment B node5502 node5502Labels,
      mixedMoment B node5503 node5503Labels,
      mixedMoment B node5504 node5504Labels,
      mixedMoment B node5505 node5505Labels,
      mixedMoment B node5506 node5506Labels,
      mixedMoment B node5507 node5507Labels,
      mixedMoment B node5508 node5508Labels,
      mixedMoment B node5509 node5509Labels]

def originalLess (a b : OriginalKey) : Bool :=
  match a, b with
  | .inl i, .inl j => decide (i < j)
  | .inl _, .inr _ => true
  | .inr _, .inl _ => false
  | .inr i, .inr j => decide (i < j)

def masterLess (a b : Master) : Bool :=
  match a, b with
  | .inl i, .inl j => decide (i < j)
  | .inl _, .inr _ => true
  | .inr _, .inl _ => false
  | .inr i, .inr j => decide (i < j)

end MUB6.Certificate.MixedTargetSemantics

end OAI
