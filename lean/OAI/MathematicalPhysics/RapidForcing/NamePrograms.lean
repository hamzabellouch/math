import OAI.MathematicalPhysics.RapidForcing.NamedForce
import OAI.MathematicalPhysics.RapidForcing.FormulaPrograms

namespace OAI

section
open Encodable Nat.Partrec
open scoped BigOperators
namespace RapidForcing.EffectiveProfile.Formula
open EffectiveArithmetic
attribute [local irreducible] runTyped bound Expr.bound Expr.diff diff
variable {d : ℕ}

private lemma computable_lipMul : Computable (fun p : (Formula d × ℚ) ×
    (Formula d × Formula d × ℚ × ℚ) =>
    p.2.1.bound p.1.2 * p.2.2.2.2 + p.2.2.1.bound p.1.2 * p.2.2.2.1) := by
  have ha := (@computable_bound d).comp (show Computable (fun p : (Formula d × ℚ) ×
    (Formula d × Formula d × ℚ × ℚ) => (p.2.1, p.1.2)) by fun_prop)
  have hb := (@computable_bound d).comp (show Computable (fun p : (Formula d × ℚ) ×
    (Formula d × Formula d × ℚ × ℚ) => (p.2.2.1, p.1.2)) by fun_prop)
  have hm₁ := computable_rat_mul.comp (ha.pair (show Computable (fun p : (Formula d × ℚ) ×
    (Formula d × Formula d × ℚ × ℚ) => p.2.2.2.2) by fun_prop))
  have hm₂ := computable_rat_mul.comp (hb.pair (show Computable (fun p : (Formula d × ℚ) ×
    (Formula d × Formula d × ℚ × ℚ) => p.2.2.2.1) by fun_prop))
  exact (computable_rat_add.comp (hm₁.pair hm₂)).of_eq (fun _ => rfl)

@[fun_prop] lemma computable_lipBound : Computable (fun p : Formula d × ℚ => p.1.lipBound p.2) := by
  have h := computable_recOn (e := fun p : Formula d × ℚ => p.1) (by fun_prop)
    (c := fun _ _ => (0 : ℚ)) (by unfold Computable₂; fun_prop)
    (v := fun _ _ => (1 : ℚ)) (by unfold Computable₂; fun_prop)
    (a := fun _ p => p.2.2.1 + p.2.2.2) (by unfold Computable₂; fun_prop)
    (m := fun a p => p.1.bound a.2 * p.2.2.2 + p.2.1.bound a.2 * p.2.2.1) computable_lipMul.to₂
    (p := fun _ p => p.1.diff.bound * p.2.2) (by unfold Computable₂; fun_prop)
  exact h.of_eq (fun p => by induction p.1 <;> simp [lipBound, *])

lemma partrec_choosePrecision : Partrec (fun p : ℚ × ℚ => choosePrecision p.1 p.2) := by
  apply Partrec.rfindOpt
  unfold Computable₂
  fun_prop

abbrev NameArgs (d : ℕ) := Formula d × Code × ℚ
private def nameLip (p : NameArgs d × (Fin d → ℚ)) : ℚ :=
  p.1.1.lipBound (2 + ∑ i, |p.2 i|)
private lemma computable_nameLip : Computable (@nameLip d) := by
  have h := computable_fin_sum computable_rat_add (f := fun q : Fin d → ℚ => fun i => |q i|)
    (fun i => computable_rat_abs.comp (Computable.fin_app.comp Computable.id (Computable.const i)))
  have ht := computable_rat_add.comp ((Computable.const 2).pair h)
  have hR := ht.comp (show Computable (fun p : NameArgs d × (Fin d → ℚ) => p.2) by fun_prop)
  exact ((@computable_lipBound d).comp ((show Computable (fun p : NameArgs d × (Fin d → ℚ) => p.1.1) by fun_prop).pair hR)).of_eq (fun _ => rfl)

lemma partrec_evalName : Partrec (fun p : NameArgs d =>
    p.1.evalName (runTyped p.2.1) p.2.2) := by
  have h₀ := (partrec_runTyped (B := Fin d → ℚ)).comp
    (show Computable (fun p : NameArgs d => (p.2.1, (0 : ℕ))) by fun_prop)
  have hn := partrec_choosePrecision.comp
    (computable_nameLip.pair (show Computable (fun p : NameArgs d × (Fin d → ℚ) => p.1.2.2) by fun_prop))
  have hq := (partrec_runTyped (B := Fin d → ℚ)).comp
    (show Computable (fun p : (NameArgs d × (Fin d → ℚ)) × ℕ => (p.1.1.2.1, p.2)) by fun_prop)
  have hb := partrec_evalAt.comp (show Computable
    (fun p : ((NameArgs d × (Fin d → ℚ)) × ℕ) × (Fin d → ℚ) =>
       (p.1.1.1.1, p.2, p.1.1.1.2.2 / 2)) by fun_prop)
  have hf : Computable (fun p : (((NameArgs d × (Fin d → ℚ)) × ℕ) × (Fin d → ℚ)) × Ball =>
      (⟨p.2.center, p.2.radius + (1 / 2 : ℚ) ^ p.1.1.2 * nameLip p.1.1.1⟩ : Ball)) := by
    have hL := computable_nameLip.comp (show Computable (fun p :
      (((NameArgs d × (Fin d → ℚ)) × ℕ) × (Fin d → ℚ)) × Ball => p.1.1.1) by fun_prop)
    fun_prop (disch := assumption)
  exact (h₀.bind (hn.bind (hq.bind (hb.bind hf.partrec.to₂).to₂).to₂).to₂).of_eq (fun _ => rfl)

lemma partrec_readReal : Partrec (fun p : Program × ℕ => readReal p.1 p.2) := by
  exact (partrec_runTyped (B := ℚ)).of_eq (fun _ => by simp [runTyped, readReal])
lemma partrec_readPoint : Partrec (fun p : Program × ℕ => readPoint p.1 p.2) := by
  exact (partrec_runTyped (B := RationalPoint)).of_eq (fun _ => by simp [runTyped, readPoint])

lemma partrec_coordinateName : Partrec (fun p : (Program × Program) × ℕ =>
    coordinateName p.1.1 p.1.2 p.2) := by
  have hv := partrec_readReal.comp (show Computable (fun p : (Program × Program) × ℕ =>
    (p.1.1, p.2)) by fun_prop)
  have hq := partrec_readPoint.comp (show Computable (fun p : ((Program × Program) × ℕ) × ℚ =>
    (p.1.1.2, p.1.2)) by fun_prop)
  have h : Computable (fun p : (((Program × Program) × ℕ) × ℚ) × RationalPoint =>
      ![p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2, p.1.2]) := by
    apply computable_fin_lambda
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  exact (hv.bind (hq.bind h.partrec.to₂).to₂).of_eq (fun _ => rfl)

noncomputable def coordinateProgram (p : Program × Program) : Program :=
  (typedCode _ partrec_coordinateName).curry (encode p)

@[fun_prop] lemma computable_coordinateProgram : Computable coordinateProgram :=
  computable_specialize.comp ((Computable.const _).pair Computable.id)

lemma runTyped_coordinateProgram (p : Program × Program) (n : ℕ) :
    runTyped (coordinateProgram p) n = coordinateName p.1 p.2 n := by
  rw [coordinateProgram, runTyped_curry, runTyped_typedCode]

end RapidForcing.EffectiveProfile.Formula

end

end OAI
