import OAI.Computability.MatchingCount.RawOptimizerRowsCompiler

namespace OAI

section

namespace BinaryMatching.Raw.Optimize.Compiler
open StackCode StackCode.Poly BinaryMatching.Raw.Compiler
local instance : Preorder ℤ := Int.instLinearOrder.toPreorder

@[fun_prop] theorem value_poly : Poly (fun z : Params×(Matrix ℤ×Row) => value z.1 z.2.1 z.2.2) := by
  have hs := upperSum_poly (fun z : Params×(Matrix ℤ×Row) => z.1.n)
    (fun z : ((Params×(Matrix ℤ×Row))×ℕ)×ℕ =>
      scaledPsi z.1.1.1 (get z.1.1.2.1 z.1.2 z.2)+
      get z.1.1.1.beta z.1.2 z.2*get z.1.1.2.1 z.1.2 z.2*(z.1.1.1.pow:ℤ))
    (by fun_prop) (by fun_prop)
  unfold value
  fun_prop
@[fun_prop] theorem gradient_poly : Poly (fun z : (Params×(Matrix ℤ×Row))×(ℕ×ℕ) =>
    gradient z.1.1 z.1.2.1 z.1.2.2 z.2.1 z.2.2) := by unfold gradient; fun_prop
@[fun_prop] theorem update_poly : Poly (fun z : Params×(Matrix ℤ×Row) => update z.1 z.2.1 z.2.2) := by
  have hg : Poly (fun z : ((Params×(Matrix ℤ×Row))×ℕ)×ℕ => gradient z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2) :=
    Poly.comp _ (fun z : ((Params×(Matrix ℤ×Row))×ℕ)×ℕ => (z.1.1,(z.1.2,z.2))) gradient_poly (by fun_prop)
  have h := Poly.rawMatrix (fun z : Params×(Matrix ℤ×Row) => z.1.n)
    (fun z : ((Params×(Matrix ℤ×Row))×ℕ)×ℕ => if decide (z.1.2<z.2) then
      min (z.1.1.1.D:ℤ) (max 0 (get z.1.1.2.1 z.1.2 z.2+gradient z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2)) else 0)
    (by fun_prop) (by fun_prop)
  exact h.congr (fun _ => by simp only [update,decide_eq_true_eq])
@[fun_prop] theorem step_poly : Poly step := by
  let r (z : Params×IntState) := selectedRow z.1.n z.1.D z.2.1
  let v (z : Params×IntState) := value z.1 z.2.1 (r z)
  have hr : Poly r := by dsimp [r]; fun_prop
  have hv : Poly v := by dsimp [v]; fun_prop
  have h := Poly.optionCasesWith (fun z : Params×IntState => z.2.2) v
    (fun z : (Params×IntState)×ℤ => max (v z.1) z.2) (by fun_prop) hv (by fun_prop)
  have hm : Poly (fun z : Params×IntState => match z.2.2 with | none => v z | Option.some w => max (v z) w) :=
    h.congr (fun z => by cases z.2.2 <;> rfl)
  have hh := Poly.pair (fun z : Params×IntState => z.1)
    (fun z : Params×IntState => (update z.1 z.2.1 (r z),Option.some (match z.2.2 with | none => v z | Option.some w => max (v z) w)))
    (by fun_prop) (Poly.pair _ _ (by fun_prop) (Poly.comp _ _ Poly.some hm))
  exact hh.congr (fun z => by unfold step; dsimp [r,v]; cases z.2.2 <;> rfl)
@[fun_prop] theorem initial_poly : Poly initial := by
  unfold initial
  have hh := Poly.rawMatrix Params.n (fun _ => (0:ℤ)) (by fun_prop) (by fun_prop)
  fun_prop
@[fun_prop] theorem operandBound_poly : Poly operandBound := by unfold operandBound; fun_prop
@[fun_prop] theorem budget_poly : Poly budget := by unfold budget; fun_prop
@[fun_prop] theorem run_poly : Poly run := by
  have h := Poly.comp _ (fun p : Params => (p.q*p.D,(budget p,initial p)))
    (Poly.guardedIterate step step_poly) (by fun_prop)
  exact Poly.second _ h
@[fun_prop] theorem result_poly : Poly result := by
  exact Poly.comp _ (fun p : Params => ((run p).2.getD 0,p.D*p.pow)) Poly.intDivNat (by fun_prop)
end BinaryMatching.Raw.Optimize.Compiler
end

end OAI
