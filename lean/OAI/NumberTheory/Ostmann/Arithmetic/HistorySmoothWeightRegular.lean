import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightState

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicState
open Construction Characters.RationalHistory HistorySymbolicSlots HistorySymbolicStep
variable {ι : Type*}

theorem append_forall {xs ys : List SmallSlot} (P : Expr ι → Prop)
    (f : Fin xs.length → Expr ι) (g : Fin ys.length → Expr ι)
    (hf : ∀ i, P (f i)) (hg : ∀ i, P (g i)) : ∀ i, P (append f g i) := by
  intro i
  change P (Fin.append f g _)
  refine Fin.addCases (motive := fun j : Fin (xs.length+ys.length) => P (Fin.append f g j)) ?_ ?_ _
  · intro j
    simpa only [Fin.append_left] using hf j
  · intro j
    simpa only [Fin.append_right] using hg j

theorem product_realRegular (es : List (Expr ι)) (x : ι → ℝ)
    (h : ∀ e ∈ es, e.RealRegularAt x) : (product es).RealRegularAt x := by
  induction es with
  | nil => trivial
  | cons e es ih => exact ⟨h e (by simp),ih (fun z hz => h z (by simp [hz]))⟩

theorem product_ofFn_realRegular {n : ℕ} (f : Fin n → Expr ι) (x : ι → ℝ)
    (h : ∀ i, (f i).RealRegularAt x) : (product (List.ofFn f)).RealRegularAt x := by
  apply product_realRegular
  intro e he
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
  exact h i

theorem product_ofFn_realEval_pos {n : ℕ} (f : Fin n → Expr ι) (x : ι → ℝ)
    (h : ∀ i, 0 < (f i).realEval x) : 0 < (product (List.ofFn f)).realEval x := by
  simp only [product_realEval,List.map_ofFn,List.prod_ofFn,Function.comp_def]
  exact Finset.prod_pos (fun i _ => h i)

theorem children_realRegular {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (comp : Fin u.length → Expr ι) (x : ι → ℝ)
    (he : e.RealRegular x) (hsmall : ∀ i, 0 < (e.small i).realEval x)
    (hc : ∀ i, (comp i).RealRegularAt x) (hcp : ∀ i, 0 < (comp i).realEval x) :
    (leftState hs e comp).RealRegular x ∧ (rightState hs e comp).RealRegular x ∧
      (∀ i, 0 < ((leftState hs e comp).small i).realEval x) ∧
      (∀ i, 0 < ((rightState hs e comp).small i).realEval x) := by
  have hleft : ∀ i, (leftPart (splitSlots hs e) i).RealRegularAt x := fun i => he.2.2 _
  have hright : ∀ i, (rightPart (splitSlots hs e) i).RealRegularAt x := fun i => he.2.2 _
  have hpivot : (pivotExpr hs e comp).RealRegularAt x := by
    have hs0 : (a.frequency:ℝ) ≠ 0 := by exact_mod_cast History.supported_root_frequency_ne_zero hs
    refine ⟨⟨⟨trivial,he.2.1,product_ofFn_realRegular _ x hright⟩,
      ⟨trivial,he.1,product_ofFn_realRegular _ x hleft⟩⟩,
      ⟨trivial,product_ofFn_realRegular comp x hc⟩,?_⟩
    exact mul_ne_zero hs0 (product_ofFn_realEval_pos comp x hcp).ne'
  have hlreg := append_forall (fun z => z.RealRegularAt x) comp _ hc hleft
  have hrreg := append_forall (fun z => z.RealRegularAt x) comp _ hc hright
  have hlpos := append_forall (fun z => 0 < z.realEval x) comp (leftPart (splitSlots hs e)) hcp (fun i => hsmall _)
  have hrpos := append_forall (fun z => 0 < z.realEval x) comp (rightPart (splitSlots hs e)) hcp (fun i => hsmall _)
  exact ⟨⟨hpivot,he.1,fun i => hlreg _⟩,⟨hpivot,he.2.1,fun i => hrreg _⟩,
    (fun i => hlpos _),(fun i => hrpos _)⟩

theorem StateExpr.realPeriod_pos {a : State} (e : StateExpr a ι) (outside : List ℕ)
    (x : ι → ℝ) (hp : 0 < e.plus.realEval x) (hm : 0 < e.minus.realEval x)
    (hsmall : ∀ i, 0 < (e.small i).realEval x) (houtside : ∀ q ∈ outside, 0 < q) :
    0 < e.realPeriod outside x := by
  have hd : 0 < (outsideProduct outside:ℝ) := by
    exact_mod_cast List.prod_pos houtside
  exact mul_pos hd (mul_pos hp (mul_pos hm (product_ofFn_realEval_pos e.small x hsmall)))

end Ostmann.Arithmetic.HistorySymbolicState

end

end OAI
