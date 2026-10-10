import OAI.MathematicalPhysics.RapidForcing.ForceSyntax
import OAI.MathematicalPhysics.RapidForcing.FormulaPrograms

namespace OAI

section
open Encodable
open scoped BigOperators
namespace RapidForcing.EffectiveArithmetic
@[fun_prop] lemma computable_fin_eval {S : Type} [Primcodable S] {d : ℕ} (i : Fin d) :
    Computable (fun f : Fin d → S => f i) := Computable.fin_app.comp Computable.id (Computable.const i)
lemma computable_fin_apply {A S : Type} [Primcodable A] [Primcodable S] {d : ℕ}
    {f : A → Fin d → S} {g : A → Fin d} (hf : Computable f) (hg : Computable g) :
    Computable (fun a => f a (g a)) := Computable.fin_app.comp hf hg
lemma computable_list_map {A B C : Type} [Primcodable A] [Primcodable B] [Primcodable C]
    {f : A → List B} {g : A → B → C} (hf : Computable f) (hg : Computable₂ g) :
    Computable (fun a => (f a).map (g a)) := by
  have h := computable_list_foldr hf (Computable.const ([] : List C))
    (h := fun a p => g a p.1 :: p.2)
    ((Computable.list_cons.comp (hg.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)).to₂)
  exact h.of_eq (fun a => by induction f a <;> simp [*])
end RapidForcing.EffectiveArithmetic
namespace RapidForcing.EffectiveProfile.Formula
open EffectiveArithmetic
attribute [local irreducible] diff Expr.diff bound Expr.bound
variable {d : ℕ}
@[fun_prop] lemma computable_const : Computable (@Formula.const d) := primrec_const.to_comp
@[fun_prop] lemma computable_var : Computable (@Formula.var d) := primrec_var.to_comp
@[fun_prop] lemma computable_profile : Computable (fun p : Expr × Formula d => Formula.profile p.1 p.2) := primrec_profile.to_comp
@[fun_prop] lemma computable_add : Computable (fun p : Formula d × Formula d => Formula.add p.1 p.2) := primrec_add.to_comp
@[fun_prop] lemma computable_mul : Computable (fun p : Formula d × Formula d => Formula.mul p.1 p.2) := primrec_mul.to_comp
@[fun_prop] lemma computable_diff_comp {A : Type} [Primcodable A] {f : A → Formula d} {g : A → Fin d}
    (hf : Computable f) (hg : Computable g) : Computable (fun a => (f a).diff (g a)) :=
  computable_diff.comp (hf.pair hg)
@[fun_prop] lemma computable_spaceIndex : Computable spaceIndex :=
  (Primrec.dom_finite spaceIndex).to_comp
abbrev MovingArgs := (Fin 3 → ℚ) × (Fin 3 → ℚ) × ℚ × ℚ
@[fun_prop] lemma computable_neg : Computable (@Formula.neg d) := by unfold Formula.neg; fun_prop
@[fun_prop] lemma computable_sub : Computable (fun p : Formula d × Formula d => p.1.sub p.2) := by unfold Formula.sub; fun_prop
@[fun_prop] lemma computable_listSum : Computable (@listSum d) :=
  computable_list_foldr Computable.id (Computable.const _) (primrec_add.to_comp.comp Computable.snd).to₂
@[fun_prop] lemma computable_listProd : Computable (@listProd d) :=
  computable_list_foldr Computable.id (Computable.const _) (primrec_mul.to_comp.comp Computable.snd).to₂
@[fun_prop] lemma computable_switch : Computable (@switch d) := by unfold switch; fun_prop
@[fun_prop] lemma computable_theta : Computable (@theta d) := by unfold theta; fun_prop
@[fun_prop] lemma computable_thetaDot : Computable (@thetaDot d) := by unfold thetaDot; fun_prop
@[fun_prop] lemma computable_zeta : Computable (@zeta d) := by
  apply computable_listProd.comp
  exact computable_list_map (Computable.const _) (by unfold Computable₂; fun_prop)
@[fun_prop] lemma computable_crossF : Computable (fun p : (Fin 3 → Formula d) × (Fin 3 → Formula d) => crossF p.1 p.2) := by
  apply computable_fin_lambda
  intro i
  fin_cases i <;> dsimp [crossF] <;> fun_prop
@[fun_prop] lemma computable_curlF : Computable curlF := by
  apply computable_fin_lambda
  intro i
  fin_cases i <;> dsimp [curlF] <;> fun_prop
@[fun_prop] lemma computable_moving : Computable (fun p : (Fin 3 → ℚ) × (Fin 3 → ℚ) × ℚ × ℚ => moving p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hs : Computable (fun p : MovingArgs => (Formula.var 0 : Formula 5).sub (Formula.const p.2.2.2)) := by fun_prop
  let c (p : MovingArgs) := fun i => Formula.add (Formula.const (p.1 i)) (Formula.mul ((Formula.var 0 : Formula 5).sub (Formula.const p.2.2.2)).theta (Formula.const (p.2.1 i)))
  have hc : Computable c := by unfold c; apply computable_fin_lambda; intro i; fun_prop
  let y (p : MovingArgs) := fun i => (Formula.var (spaceIndex i) : Formula 5).sub (c p i)
  have hy : Computable y := by unfold y; apply computable_fin_lambda; intro i; fun_prop (disch := assumption)
  have hz : Computable (fun p : MovingArgs => zeta (fun i => Formula.mul (Formula.const p.2.2.1⁻¹) (y p i))) := by
    apply computable_zeta.comp
    apply computable_fin_lambda
    intro i
    fun_prop (disch := assumption)
  have hv : Computable (fun p : MovingArgs => fun i : Fin 3 => Formula.mul
      ((Formula.var 0 : Formula 5).sub (Formula.const p.2.2.2)).thetaDot (Formula.const (p.2.1 i))) := by
    apply computable_fin_lambda; intro i; fun_prop
  unfold moving
  change Computable (fun p : MovingArgs => curlF (fun i => Formula.mul
    (zeta (fun i => Formula.mul (Formula.const p.2.2.1⁻¹) (y p i)))
    (Formula.mul (Formula.const (1/2)) (crossF _ (y p) i))))
  apply computable_curlF.comp
  apply computable_fin_lambda
  intro i
  exact computable_mul.comp (hz.pair (computable_mul.comp
    ((Computable.const (Formula.const (1/2))).pair
      ((computable_fin_eval i).comp (computable_crossF.comp (hv.pair hy))))))

@[fun_prop] lemma computable_sumVector : Computable sumVector := by
  apply computable_fin_lambda
  intro i
  exact computable_listSum.comp (computable_list_map Computable.id
    (Computable.fin_app.comp Computable.snd (Computable.const i)).to₂)
@[fun_prop] lemma computable_residualFormula : Computable residualFormula := by
  apply computable_fin_lambda
  intro j
  have hA : Computable (fun a : Fin 3 → Formula 5 => listSum ((List.finRange 3).map fun i =>
      Formula.mul (a i) ((a j).diff (spaceIndex i)))) := by
    apply computable_listSum.comp
    apply computable_list_map (Computable.const _)
    unfold Computable₂
    have hi : Computable (fun p : (Fin 3 → Formula 5) × Fin 3 => spaceIndex p.2) :=
      computable_spaceIndex.comp Computable.snd
    fun_prop (disch := assumption)
  have hL : Computable (fun a : Fin 3 → Formula 5 => listSum ((List.finRange 3).map fun i =>
      ((a j).diff (spaceIndex i)).diff (spaceIndex i))) := by
    apply computable_listSum.comp
    apply computable_list_map (Computable.const _)
    unfold Computable₂
    have hi : Computable (fun p : (Fin 3 → Formula 5) × Fin 3 => spaceIndex p.2) :=
      computable_spaceIndex.comp Computable.snd
    fun_prop (disch := assumption)
  unfold residualFormula
  fun_prop (disch := assumption)

@[fun_prop] lemma computable_iterate_diff : Computable (fun p : Formula d × Fin d × ℕ => (diff p.2.1)^[p.2.2] p.1) :=
  computable_nat_iterate (Computable.snd.comp Computable.snd) Computable.fst
    (computable_diff.comp (Computable.snd.pair ((Computable.fst.comp Computable.snd).comp Computable.fst))).to₂
@[fun_prop] lemma computable_iterate_diff_comp {A : Type} [Primcodable A]
    {a : A → Formula d} {i : A → Fin d} {n : A → ℕ}
    (ha : Computable a) (hi : Computable i) (hn : Computable n) :
    Computable (fun p => (diff (i p))^[n p] (a p)) :=
  computable_iterate_diff.comp (ha.pair (hi.pair hn))
@[fun_prop] lemma computable_mixed : Computable (fun p : Formula 5 × ℕ × MultiIndex => p.1.mixed p.2.1 p.2.2) := by
  unfold mixed
  fun_prop
end RapidForcing.EffectiveProfile.Formula

end

end OAI
