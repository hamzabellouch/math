import OAI.MathematicalPhysics.RapidForcing.RatOperations
import OAI.MathematicalPhysics.RapidForcing.ComputableProfiles
import OAI.MathematicalPhysics.RapidForcing.TypedPrograms

namespace OAI

section
open Encodable Nat.Partrec
open scoped BigOperators
namespace RapidForcing.EffectiveArithmetic

@[fun_prop] lemma computable_rat_min : Computable (fun p : ℚ × ℚ => min p.1 p.2) := by
  simpa only [min_def] using (show Computable (fun p : ℚ × ℚ => if p.1 ≤ p.2 then p.1 else p.2) by fun_prop)

@[fun_prop] lemma computable_fin_app {S : Type} [Primcodable S] {d : ℕ} :
    Computable (fun p : (Fin d → S) × Fin d => p.1 p.2) := Computable.fin_app

lemma computable_fin_lambda {A S : Type} [Primcodable A] [Primcodable S] {d : ℕ}
    {f : A → Fin d → S} (hf : ∀ i, Computable (fun a => f a i)) : Computable f := by
  exact (Primrec.vector_get'.to_comp.comp (Computable.vector_ofFn hf)).of_eq
    (fun a => by ext i; simp)

lemma computable_fin_sum {A S : Type} [Primcodable A] [Primcodable S] [AddCommMonoid S]
    (hadd : Computable (fun p : S × S => p.1 + p.2)) {d : ℕ}
    {f : A → Fin d → S} (hf : ∀ i, Computable (fun a => f a i)) :
    Computable (fun a => ∑ i, f a i) := by
  have h := computable_list_foldr (Computable.list_ofFn hf) (Computable.const (0 : S))
    (hadd.comp Computable.snd).to₂
  exact h.of_eq (fun a => by simpa [List.sum_ofFn] using
    (show (List.ofFn (f a)).foldr (fun a b => a + b) 0 = (List.ofFn (f a)).sum by rfl))

end RapidForcing.EffectiveArithmetic
namespace RapidForcing.EffectiveProfile.Formula
open EffectiveArithmetic
attribute [local irreducible] runTyped
variable {d : ℕ}

@[fun_prop] lemma computable_bound : Computable (fun p : Formula d × ℚ => p.1.bound p.2) := by
  have h := computable_recOn (e := fun p : Formula d × ℚ => p.1) (by fun_prop)
    (c := fun _ q => |q|) (by unfold Computable₂; fun_prop)
    (v := fun p _ => |p.2|) (by unfold Computable₂; fun_prop)
    (a := fun _ p => p.2.2.1 + p.2.2.2) (by unfold Computable₂; fun_prop)
    (m := fun _ p => p.2.2.1 * p.2.2.2) (by unfold Computable₂; fun_prop)
    (p := fun _ p => p.1.bound) (by unfold Computable₂; fun_prop)
  exact h.of_eq (fun p => by induction p.1 <;> simp [bound, *])

@[fun_prop] lemma computable_diff : Computable (fun p : Formula d × Fin d => p.1.diff p.2) := by
  have h := computable_recOn (e := fun p : Formula d × Fin d => p.1) (by fun_prop)
    (c := fun _ _ => Formula.const 0) (by unfold Computable₂; fun_prop)
    (v := fun p j => Formula.const (if j = p.2 then 1 else 0)) (by unfold Computable₂; fun_prop)
    (a := fun _ p => Formula.add p.2.2.1 p.2.2.2) (by unfold Computable₂; fun_prop)
    (m := fun _ p => Formula.add (.mul p.2.2.1 p.2.1) (.mul p.1 p.2.2.2)) (by unfold Computable₂; fun_prop)
    (p := fun _ p => Formula.mul (.profile p.1.diff p.2.1) p.2.2) (by unfold Computable₂; fun_prop)
  exact h.of_eq (fun p => by induction p.1 <;> simp [diff, *])

abbrev EvalArgs (d : ℕ) := (Fin d → ℚ) × ℚ

def evalConst (p : ℚ × EvalArgs d) : Part Ball := Part.some (Ball.exact p.1)
def evalVar (p : Fin d × EvalArgs d) : Part Ball := Part.some (Ball.exact (p.2.1 p.1))
def evalAdd (p : (Code × Code) × EvalArgs d) : Part Ball := do
  let u : Ball ← runTyped p.1.1 (p.2.1, p.2.2 / 2)
  let v : Ball ← runTyped p.1.2 (p.2.1, p.2.2 / 2)
  pure (u.add v)
def evalMul (p : (Formula d × Formula d × Code × Code) × EvalArgs d) : Part Ball :=
  let R := 1 + ∑ i, |p.2.1 i|
  let η := min 1 (p.2.2 / (4 * (p.1.1.bound R + p.1.2.1.bound R + 2)))
  do
    let u : Ball ← runTyped p.1.2.2.1 (p.2.1, η)
    let v : Ball ← runTyped p.1.2.2.2 (p.2.1, η)
    pure (u.mul v)
def evalProfile (p : (Expr × Code) × EvalArgs d) : Part Ball := do
  let u : Ball ← runTyped p.1.2 (p.2.1, p.2.2 / (2 * (p.1.1.diff.bound + 1)))
  let v ← p.1.1.approx u.center (p.2.2 / 2)
  pure ⟨v.center, v.radius + p.1.1.diff.bound * u.radius⟩

lemma partrec_evalConst : Partrec (@evalConst d) :=
  (computable_ball_exact.comp Computable.fst).partrec
lemma partrec_evalVar : Partrec (@evalVar d) :=
  (computable_ball_exact.comp (Computable.fin_app.comp
    (Computable.fst.comp Computable.snd) Computable.fst)).partrec
lemma partrec_evalAdd : Partrec (@evalAdd d) := by
  have ha : Computable (fun p : (Code × Code) × EvalArgs d => (p.2.1, p.2.2 / 2)) := by fun_prop
  have hu := (partrec_runTyped (B := Ball)).comp
    ((show Computable (fun p : (Code × Code) × EvalArgs d => p.1.1) by fun_prop).pair ha)
  have hv := (partrec_runTyped (B := Ball)).comp
    ((show Computable (fun p : (Code × Code) × EvalArgs d => p.1.2) by fun_prop).pair ha)
  have h := hu.bind (((hv.comp Computable.fst).bind
    (computable_ball_add.comp ((Computable.snd.comp Computable.fst).pair Computable.snd)).partrec.to₂).to₂)
  exact h.of_eq (fun _ => rfl)

lemma computable_operandBox : Computable (fun q : Fin d → ℚ => 1 + ∑ i, |q i|) := by
  have h := computable_fin_sum computable_rat_add (f := fun q : Fin d → ℚ => fun i => |q i|)
    (fun i => computable_rat_abs.comp (Computable.fin_app.comp Computable.id (Computable.const i)))
  have h' := computable_rat_add.comp ((Computable.const 1).pair h)
  exact h'.of_eq (fun _ => rfl)

private def mulTolerance (p : ℚ × ℚ × ℚ) : ℚ := min 1 (p.1 / (4 * (p.2.1 + p.2.2 + 2)))
private lemma computable_mulTolerance : Computable mulTolerance := by
  unfold mulTolerance; fun_prop

lemma computable_evalMul_args : Computable (fun p :
    (Formula d × Formula d × Code × Code) × EvalArgs d =>
    (p.2.1, min 1 (p.2.2 / (4 * (p.1.1.bound (1 + ∑ i, |p.2.1 i|) +
        p.1.2.1.bound (1 + ∑ i, |p.2.1 i|) + 2))))) := by
  have hR := computable_operandBox.comp (show Computable (fun p :
    (Formula d × Formula d × Code × Code) × EvalArgs d => p.2.1) by fun_prop)
  have ha := computable_bound.comp ((show Computable (fun p :
    (Formula d × Formula d × Code × Code) × EvalArgs d => p.1.1) by fun_prop).pair hR)
  have hb := computable_bound.comp ((show Computable (fun p :
    (Formula d × Formula d × Code × Code) × EvalArgs d => p.1.2.1) by fun_prop).pair hR)
  have ht := computable_mulTolerance.comp ((Computable.snd.comp Computable.snd).pair (ha.pair hb))
  have h := (Computable.fst.comp Computable.snd).pair ht
  exact h.of_eq (fun _ => rfl)

lemma partrec_evalMul : Partrec (@evalMul d) := by
  have hu := (partrec_runTyped (B := Ball)).comp ((show
    Computable (fun p : (Formula d × Formula d × Code × Code) × EvalArgs d => p.1.2.2.1) by fun_prop).pair computable_evalMul_args)
  have hv := (partrec_runTyped (B := Ball)).comp ((show
    Computable (fun p : (Formula d × Formula d × Code × Code) × EvalArgs d => p.1.2.2.2) by fun_prop).pair computable_evalMul_args)
  have h := hu.bind (((hv.comp Computable.fst).bind
    (computable_ball_mul.comp ((Computable.snd.comp Computable.fst).pair Computable.snd)).partrec.to₂).to₂)
  exact h.of_eq (fun _ => rfl)

lemma partrec_evalProfile : Partrec (@evalProfile d) := by
  have ha : Computable (fun p : (Expr × Code) × EvalArgs d =>
      (p.2.1, p.2.2 / (2 * (p.1.1.diff.bound + 1)))) := by fun_prop
  have hu := (partrec_runTyped (B := Ball)).comp
    ((show Computable (fun p : (Expr × Code) × EvalArgs d => p.1.2) by fun_prop).pair ha)
  have hv := Expr.partrec_approx.comp (show Computable
    (fun p : ((Expr × Code) × EvalArgs d) × Ball =>
      (p.1.1.1, p.2.center, p.1.2.2 / 2)) by fun_prop)
  have hresult : Computable (fun p : (((Expr × Code) × EvalArgs d) × Ball) × Ball =>
      (⟨p.2.center, p.2.radius + p.1.1.1.1.diff.bound * p.1.2.radius⟩ : Ball)) := by fun_prop
  exact (hu.bind (hv.bind hresult.partrec.to₂).to₂).of_eq (fun _ => rfl)

noncomputable def constProgram (d : ℕ) : Code := typedCode (@evalConst d) partrec_evalConst
noncomputable def varProgram (d : ℕ) : Code := typedCode (@evalVar d) partrec_evalVar
noncomputable def addProgram (d : ℕ) : Code := typedCode (@evalAdd d) partrec_evalAdd
noncomputable def mulProgram (d : ℕ) : Code := typedCode (@evalMul d) partrec_evalMul
noncomputable def profileProgram (d : ℕ) : Code := typedCode (@evalProfile d) partrec_evalProfile

noncomputable def evaluator : Formula d → Code
  | .const q => (constProgram d).curry (encode q)
  | .var i => (varProgram d).curry (encode i)
  | .add a b => (addProgram d).curry (encode (a.evaluator, b.evaluator))
  | .mul a b => (mulProgram d).curry (encode (a, b, a.evaluator, b.evaluator))
  | .profile e a => (profileProgram d).curry (encode (e, a.evaluator))

@[fun_prop] lemma computable_evaluator : Computable (@evaluator d) := by
  have h := computable_recOn (e := (id : Formula d → Formula d)) Computable.id
    (c := fun _ q => (constProgram d).curry (encode q)) (by exact computable_specialize.comp ((Computable.const _).pair Computable.snd))
    (v := fun _ i => (varProgram d).curry (encode i)) (by exact computable_specialize.comp ((Computable.const _).pair (by fun_prop)))
    (a := fun _ p => (addProgram d).curry (encode (p.2.2.1, p.2.2.2))) (by exact computable_specialize.comp ((Computable.const _).pair (by fun_prop)))
    (m := fun _ p => (mulProgram d).curry (encode p)) (by exact computable_specialize.comp ((Computable.const _).pair (by fun_prop)))
    (p := fun _ p => (profileProgram d).curry (encode (p.1, p.2.2))) (by exact computable_specialize.comp ((Computable.const _).pair (by fun_prop)))
  exact h.of_eq (fun a => by induction a <;> simp_all only [id_eq, evaluator])

lemma runTyped_evaluator (a : Formula d) (q : Fin d → ℚ) (ε : ℚ) :
    runTyped a.evaluator (q, ε) = a.evalAt q ε := by
  induction a generalizing q ε with
  | const r =>
    simp only [evaluator, constProgram, runTyped_curry, runTyped_typedCode, evalConst, evalAt]
  | var i =>
    simp only [evaluator, varProgram, runTyped_curry, runTyped_typedCode, evalVar, evalAt]
  | add a b ha hb =>
    simp only [evaluator, addProgram, runTyped_curry, runTyped_typedCode, evalAdd, evalAt, ha, hb]
  | mul a b ha hb =>
    simp only [evaluator, mulProgram, runTyped_curry, runTyped_typedCode, evalMul, evalAt, ha, hb]
  | profile e a ha =>
    simp only [evaluator, profileProgram, runTyped_curry, runTyped_typedCode, evalProfile, evalAt, ha]

lemma partrec_evalAt : Partrec (fun p : Formula d × EvalArgs d => p.1.evalAt p.2.1 p.2.2) := by
  exact ((partrec_runTyped (B := Ball)).comp
    ((computable_evaluator.comp Computable.fst).pair Computable.snd)).of_eq
    (fun p => runTyped_evaluator p.1 p.2.1 p.2.2)

end RapidForcing.EffectiveProfile.Formula

end

end OAI
