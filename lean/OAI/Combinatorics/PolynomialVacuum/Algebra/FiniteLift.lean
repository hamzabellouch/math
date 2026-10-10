import OAI.Combinatorics.PolynomialVacuum.Algebra.CupPrescriptions
import OAI.Combinatorics.PolynomialVacuum.Algebra.NaturalCollision

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

noncomputable def liftPolyTensor {N m : ℕ} (W : PolynomialTensor N (Fin m))
    (X : ℕ → ℂ) : SpinTensor ℕ ℂ :=
  fun s => eval (fun j : Fin m => X j.val) (W (fun j : Fin N => s j.val))

noncomputable def liftState {n : ℕ} (ψ : State n) : NatSpectralTensor :=
  liftPolyTensor ψ

theorem replacePair_restrict {N : ℕ} (i j : Fin N) (s : ℕ → Spin) (ab : Pair) :
    (fun k : Fin N => replacePair s i.val j.val ab k.val) =
      Function.update (Function.update (fun k : Fin N => s k.val) i ab.1) j ab.2 := by
  funext k
  simp only [replacePair,Function.update_apply,Fin.ext_iff]

theorem liftPolyTensor_exchange {N m : ℕ} (i j : Fin N)
    (x y : MvPolynomial (Fin m) ℂ) (W : PolynomialTensor N (Fin m)) (X : ℕ → ℂ) :
    liftPolyTensor (tensorExchange i j x y W) X =
      pairAction i.val j.val (exchangeNumerator (eval (fun k : Fin m => X k.val) x)
        (eval (fun k : Fin m => X k.val) y)) (liftPolyTensor W X) := by
  funext s
  simp only [liftPolyTensor,tensorExchange,map_sum,map_mul,eval_polyExchangeNumerator,pairAction,
    replacePair_restrict]

theorem liftPolyTensor_initialCup {n : ℕ} (ψ : State n) (i : Fin (n+1)) (X : ℕ → ℂ) :
    liftPolyTensor (initialCup ψ i) X=cupLinear i.val (liftState ψ (skipOne i.val X)) := by
  funext s
  simp only [liftPolyTensor,initialCup,map_mul,eval_C,eval_rename,cupLinear,
    LinearMap.coe_mk,AddHom.coe_mk,liftState,pairLeft,pairRight]
  congr 2
  apply congrArg eval
  funext k
  simp only [Function.comp_apply,skipOne,Fin.succAbove,Fin.lt_def,Fin.val_castSucc]
  split_ifs <;> rfl

end PolynomialVacuumAlgebra

end OAI
