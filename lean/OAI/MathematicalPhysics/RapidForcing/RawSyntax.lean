import OAI.MathematicalPhysics.RapidForcing.RawMachineCorrect
import OAI.MathematicalPhysics.RapidForcing.SyntaxComputable

namespace OAI

section
open Encodable
open scoped BigOperators
namespace RapidForcing
open EffectiveProfile EffectiveProfile.Formula EffectiveArithmetic
namespace RawMachine

def loadFormula (M : RawMachine) (w : List ℕ) : Fin 3 → Formula 5 :=
  moving (fun _ => 0) ![-1, (M.scaleData w).δQ 0 * M.initialDigit w, 0] 1 0

def addressFormula (M : RawMachine) (d : ScaleData) (n m : ℕ) : Fin 3 → Formula 5 :=
  moving ![-1, (m : ℚ) * d.δQ n, 0]
    ![-d.bQ n * (M.terminalDigit d (m % d.capacity n) : ℚ),
      d.δQ (n+1) * (M.nextDigit d n (m % d.capacity n) : ℚ), 0]
    (d.δQ n) (1 + (n : ℚ))

def stepFormula (M : RawMachine) (w : List ℕ) (n : ℕ) : Fin 3 → Formula 5 :=
  sumVector ((List.range ((M.scaleData w).D n + 1)).map
    (addressFormula M (M.scaleData w) n))

def velocityFormula (M : RawMachine) (w : List ℕ) (N : ℕ) : Fin 3 → Formula 5 :=
  sumVector (loadFormula M w :: (List.range N).map (stepFormula M w))

def forceFormula (M : RawMachine) (w : List ℕ) (N : ℕ) : Fin 3 → Formula 5 :=
  residualFormula (velocityFormula M w N)

@[simp] lemma description_loadFormula (M : Machine) (w : M.Input) :
    loadFormula M.description (w.map Fin.val) = Formula.loadFormula M w := by
  simp only [loadFormula, Formula.loadFormula, Machine.description_scaleData, Machine.description_initialDigit]
@[simp] lemma description_addressFormula (M : Machine) (d : ScaleData) (n m : ℕ) :
    addressFormula M.description d n m = Formula.addressFormula M d n m := by
  simp only [addressFormula, Formula.addressFormula, Machine.description_terminalDigit, Machine.description_nextDigit]
@[simp] lemma description_stepFormula (M : Machine) (w : M.Input) (n : ℕ) :
    stepFormula M.description (w.map Fin.val) n = Formula.stepFormula M w n := by
  simp only [stepFormula, Formula.stepFormula, Machine.description_scaleData]
  congr 1
  apply List.map_congr_left
  intro m _
  exact description_addressFormula M _ _ _
@[simp] lemma description_forceFormula (M : Machine) (w : M.Input) (N : ℕ) :
    forceFormula M.description (w.map Fin.val) N = Formula.forceFormula M w N := by
  simp only [forceFormula, Formula.forceFormula, velocityFormula, Formula.velocityFormula,
    description_loadFormula]
  congr 3
  apply List.map_congr_left
  intro n _
  exact description_stepFormula M w n

attribute [local irreducible] Formula.moving Formula.diff Expr.diff Formula.bound Expr.bound
  instruction nextDigit initialDigit scaleData ScaleData.A ScaleData.S ScaleData.P ScaleData.L
  ScaleData.C ScaleData.s ScaleData.D ScaleData.δQ ScaleData.bQ
@[fun_prop] lemma computable_loadFormula : Computable (fun p : RawInput => loadFormula p.1 p.2) := by
  unfold loadFormula
  apply computable_moving.comp (g := fun p : RawInput =>
    ((fun _ => 0), ![-1, (p.1.scaleData p.2).δQ 0 * p.1.initialDigit p.2, 0], 1, 0))
  apply Computable.pair (Computable.const _)
  apply Computable.pair _ (Computable.const _)
  apply computable_fin_lambda
  intro i
  fin_cases i <;> dsimp <;> fun_prop

@[fun_prop] lemma computable_addressFormula : Computable (fun p : RawMachine × ScaleData × ℕ × ℕ => addressFormula p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold addressFormula
  apply computable_moving.comp (g := fun p : RawMachine × ScaleData × ℕ × ℕ =>
    (![-1, (p.2.2.2 : ℚ) * p.2.1.δQ p.2.2.1, 0],
     ![-p.2.1.bQ p.2.2.1 * (p.1.terminalDigit p.2.1 (p.2.2.2 % p.2.1.capacity p.2.2.1) : ℚ),
       p.2.1.δQ (p.2.2.1+1) * (p.1.nextDigit p.2.1 p.2.2.1 (p.2.2.2 % p.2.1.capacity p.2.2.1) : ℚ), 0],
     p.2.1.δQ p.2.2.1, 1 + (p.2.2.1 : ℚ)))
  apply Computable.pair
  · apply computable_fin_lambda
    intro i
    fin_cases i <;> dsimp <;> fun_prop
  · apply Computable.pair
    · apply computable_fin_lambda
      intro i
      fin_cases i <;> dsimp <;> fun_prop
    · fun_prop

@[fun_prop] lemma computable_stepFormula : Computable (fun p : RawInput × ℕ => stepFormula p.1.1 p.1.2 p.2) := by
  unfold stepFormula
  apply computable_sumVector.comp
  apply computable_list_map (by fun_prop)
  unfold Computable₂
  fun_prop

attribute [local irreducible] loadFormula addressFormula stepFormula

lemma computable_stepFormula_family : Computable₂ (fun p : RawInput × ℕ => fun n : ℕ => stepFormula p.1.1 p.1.2 n) := by
  exact computable_stepFormula.comp (g := fun p : (RawInput × ℕ) × ℕ => (p.1.1, p.2))
    ((Computable.fst.comp Computable.fst).pair Computable.snd)

lemma computable_stepFormula_list : Computable (fun p : RawInput × ℕ => (List.range p.2).map (stepFormula p.1.1 p.1.2)) :=
  computable_list_map (Primrec.list_range.to_comp.comp Computable.snd) computable_stepFormula_family

@[fun_prop] lemma computable_velocityFormula : Computable (fun p : RawInput × ℕ => velocityFormula p.1.1 p.1.2 p.2) := by
  unfold velocityFormula
  exact computable_sumVector.comp
    (Computable.list_cons.comp (computable_loadFormula.comp Computable.fst) computable_stepFormula_list)

@[fun_prop] lemma computable_forceFormula : Computable (fun p : RawInput × ℕ => forceFormula p.1.1 p.1.2 p.2) :=
  computable_residualFormula.comp computable_velocityFormula

end RawMachine
end RapidForcing

end

end OAI
