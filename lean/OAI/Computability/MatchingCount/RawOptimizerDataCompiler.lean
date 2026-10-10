import OAI.Computability.MatchingCount.RawOptimizer

namespace OAI

section

namespace BinaryMatching.Raw.Optimize.Compiler
open StackCode StackCode.Poly
local instance : Preorder ℤ := Int.instLinearOrder.toPreorder

@[fun_prop] theorem paramsRepr_poly : Poly Params.repr :=
  (Poly.identity (α := ParamData)).reindex Params.repr Params.repr (fun _ => rfl) (fun _ => rfl)
@[fun_prop] theorem paramsOfData_poly : Poly Params.ofData :=
  (Poly.identity (α := ParamData)).reindex Params.ofData id (fun _ => rfl) (fun _ => rfl)
@[fun_prop] theorem params_n : Poly Params.n :=
  Poly.comp (fun z : ParamData => z.1) Params.repr (by fun_prop) paramsRepr_poly
@[fun_prop] theorem params_q : Poly Params.q :=
  Poly.comp (fun z : ParamData => z.2.1) Params.repr (by fun_prop) paramsRepr_poly
@[fun_prop] theorem params_k : Poly Params.k :=
  Poly.comp (fun z : ParamData => z.2.2.1) Params.repr (by fun_prop) paramsRepr_poly
@[fun_prop] theorem params_L : Poly Params.L :=
  Poly.comp (fun z : ParamData => z.2.2.2.1) Params.repr (by fun_prop) paramsRepr_poly
@[fun_prop] theorem params_D : Poly Params.D :=
  Poly.comp (fun z : ParamData => z.2.2.2.2.1) Params.repr (by fun_prop) paramsRepr_poly
@[fun_prop] theorem params_M : Poly Params.M :=
  Poly.comp (fun z : ParamData => z.2.2.2.2.2.1) Params.repr (by fun_prop) paramsRepr_poly
@[fun_prop] theorem params_pow : Poly Params.pow :=
  Poly.comp (fun z : ParamData => z.2.2.2.2.2.2.1) Params.repr (by fun_prop) paramsRepr_poly
@[fun_prop] theorem params_beta : Poly Params.beta :=
  Poly.comp (fun z : ParamData => z.2.2.2.2.2.2.2) Params.repr (by fun_prop) paramsRepr_poly

@[fun_prop] theorem doubleIntSum {α : Type} [Coding α] [Inhabited α]
    (n : α → ℕ) (f : (α×ℕ)×ℕ → ℤ) (hn : Poly n) (hf : Poly f) :
    Poly (fun a => (tab (n a) (fun i => (tab (n a) (fun j => f ((a,i),j))).sum)).sum) := by
  apply Poly.comp List.sum _ Poly.listIntSum
  apply Poly.rawTab n (fun z : α×ℕ => (tab (n z.1) (fun j => f (z,j))).sum) hn
  apply Poly.comp List.sum _ Poly.listIntSum
  exact Poly.rawTab (fun z : α×ℕ => n z.1) f (by fun_prop) hf

@[fun_prop] theorem upperSum_poly {α : Type} [Coding α] [Inhabited α]
    (n : α → ℕ) (f : (α×ℕ)×ℕ → ℤ) (hn : Poly n) (hf : Poly f) :
    Poly (fun a => upperSum (n a) (fun i j => f ((a,i),j))) := by
  have h := doubleIntSum n (fun z : (α×ℕ)×ℕ => if decide (z.1.2<z.2) then f z else 0) hn (by fun_prop)
  exact h.congr (fun a => by simp only [upperSum,decide_eq_true_eq])

@[fun_prop] theorem rowNumerator_poly : Poly (fun z : ℕ×(Matrix ℤ×Row) => rowNumerator z.1 z.2.1 z.2.2) := by
  have hh := upperSum_poly (fun z : ℕ×(Matrix ℤ×Row) => z.2.1.length)
    (fun z : ((ℕ×(Matrix ℤ×Row))×ℕ)×ℕ => get z.1.1.2.2.1 z.1.2 z.2*get z.1.1.2.1 z.1.2 z.2)
    (by fun_prop) (by fun_prop)
  unfold rowNumerator
  fun_prop

@[fun_prop] theorem indexedSlope_poly : Poly (fun z : ℕ×ℕ => indexedSlope z.1 z.2) := by
  have h : Poly (fun z : ℕ×ℕ => if decide (z.2<z.1) then (z.2:ℤ)-1 else (z.1:ℤ)) := by fun_prop
  exact h.congr (fun _ => by simp only [indexedSlope,decide_eq_true_eq])

@[fun_prop] theorem pieceNumerator_poly : Poly (fun z : (ℕ×(ℕ×ℕ))×(ℤ×ℕ) =>
    pieceNumerator z.1.1 z.1.2.1 z.1.2.2 z.2.1 z.2.2) := by
  have h : Poly (fun z : (ℕ×(ℕ×ℕ))×(ℤ×ℕ) => indexedSlope z.1.1 z.2.2*z.2.1*(z.1.2.2:ℤ)+
      if decide (z.2.2<z.1.1) then (z.1.2.1:ℤ)*(cappedPow2 z.1.2.2 (z.1.1-z.2.2):ℤ) else 0) := by fun_prop
  exact h.congr (fun _ => by simp only [pieceNumerator,decide_eq_true_eq])

@[fun_prop] theorem selectedIndex_poly : Poly (fun z : (ℕ×(ℕ×ℕ))×ℤ => selectedIndex z.1.1 z.1.2.1 z.1.2.2 z.2) := by
  let arg (z : (ℕ×(ℕ×ℕ))×ℤ) := (List.range (z.1.1+1)).argmin (pieceNumerator z.1.1 z.1.2.1 z.1.2.2 z.2)
  have ha : Poly arg := by
    apply Poly.comp _ (fun z : (ℕ×(ℕ×ℕ))×ℤ => (z,List.range (z.1.1+1)))
      (Poly.listArgminParam Poly.intLT (fun z : ((ℕ×(ℕ×ℕ))×ℤ)×ℕ => pieceNumerator z.1.1.1 z.1.1.2.1 z.1.1.2.2 z.1.2 z.2)
        (Poly.comp _ (fun z : ((ℕ×(ℕ×ℕ))×ℤ)×ℕ => (z.1.1,(z.1.2,z.2))) pieceNumerator_poly (by fun_prop)))
      (by fun_prop)
  have h : Poly (fun z : (ℕ×(ℕ×ℕ))×ℤ => if (arg z).isSome then (arg z).getD 0 else z.1.1) := by fun_prop
  exact h.congr (fun z => by change _=(arg z).getD _; cases arg z <;> rfl)

@[fun_prop] theorem selectedIndex_params_poly : Poly (fun z : Params×ℤ => selectedIndex z.1.k z.1.D z.1.pow z.2) :=
  Poly.comp _ (fun z : Params×ℤ => ((z.1.k,(z.1.D,z.1.pow)),z.2)) selectedIndex_poly (by fun_prop)
@[fun_prop] theorem scaledPsi_poly : Poly (fun z : Params×ℤ => scaledPsi z.1 z.2) :=
  Poly.comp _ (fun z : Params×ℤ => ((z.1.k,(z.1.D,z.1.pow)),(z.2,selectedIndex z.1.k z.1.D z.1.pow z.2)))
    pieceNumerator_poly (by fun_prop)
@[fun_prop] theorem scaledSlope_poly : Poly (fun z : Params×ℤ => scaledSlope z.1 z.2) :=
  Poly.comp _ (fun z : Params×ℤ => (z.1.k,selectedIndex z.1.k z.1.D z.1.pow z.2)) indexedSlope_poly (by fun_prop)
end BinaryMatching.Raw.Optimize.Compiler
end

end OAI
