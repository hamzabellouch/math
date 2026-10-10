import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightExtension
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightRegular
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightTree

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic
open Set Filter
open scoped ContDiff Topology

theorem giantCell_mul_contDiffAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : ℝ) (p : E → ℝ) (f : E → ℂ) (x : E) (hp : ContDiffAt ℝ ∞ p x)
    (hf : 0 < p x → ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ ∞ (fun y => (giantCell G (p y):ℂ) * f y) x := by
  by_cases hx : 0 < p x
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x
      ((giantCell_contDiff G).contDiffAt.comp x hp)).mul (hf hx)
  · have hlt : p x < Real.exp (G-1) := (le_of_not_gt hx).trans_lt (Real.exp_pos _)
    apply (show ContDiffAt ℝ ∞ (fun _ : E => (0:ℂ)) x from contDiffAt_const).congr_of_eventuallyEq
    filter_upwards [hp.continuousAt.eventually (eventually_lt_nhds hlt)] with y hy
    simp only [giantCell_zero_of_le_lower G hy.le,Complex.ofReal_zero,zero_mul]

namespace HistorySymbolicEncoding
open Construction Characters.RationalHistory HistorySymbolicState HistoryOccurrenceVariables
variable {ι : Type*}

theorem treeRoot_encode {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (e : StateExpr h.root ι)
    (comp : InternalKey h → Expr ι) : treeRoot h (encode V outside h hs e comp) = e := by
  cases h <;> rfl

theorem encode_realHistoryScalar_contDiffAt [Fintype ι] (b s : ℕ) (X tb td G : ℝ)
    (hX : 0 < X) (outside : List ℕ) (houtside : ∀ q ∈ outside, 0 < q)
    {l : ℕ} {V : ℕ → ℕ} (h : History l) (hs : h.Supported V outside)
    (e : StateExpr h.root ι) (comp : InternalKey h → Expr ι) (x : ι → ℝ)
    (he : e.RealRegular x) (hsmall : ∀ i, 0 < (e.small i).realEval x)
    (hplus : 0 < e.plus.realEval x) (hminus : 0 < e.minus.realEval x)
    (hc : ∀ i, (comp i).RealRegularAt x) (hcp : ∀ i, 0 < (comp i).realEval x) :
    ContDiffAt ℝ ∞ (fun y => realHistoryScalar b s X tb td G outside y h
      (encode V outside h hs e comp)) x := by
  induction h with
  | leaf a =>
    exact e.realScalar_contDiffAt b s X tb td outside x he hX
      (e.realPeriod_pos outside x hplus hminus hsmall houtside) hsmall houtside
  | @node l a p u hp hm left right ihl ihr =>
    have hu := children_realRegular hs e (fun i => comp (Sum.inl i)) x he hsmall
      (fun i => hc (Sum.inl i)) (fun i => hcp (Sum.inl i))
    have hpivot : ContDiffAt ℝ ∞ (fun y => (pivotExpr hs e (fun i => comp (Sum.inl i))).realEval y) x :=
      Expr.contDiffAt_realEval _ x hu.1.1
    simp only [encode,realHistoryScalar,treeRoot_encode,leftState]
    simp only [mul_assoc]
    apply giantCell_mul_contDiffAt G _ _ x hpivot
    intro hpos
    apply ContDiffAt.mul
    · exact ihl (History.supported_left hs) _ _ hu.1 hu.2.2.1 hpos hplus
        (fun i => hc (Sum.inr (Sum.inl i))) (fun i => hcp (Sum.inr (Sum.inl i)))
    · exact Complex.conjCLE.contDiff.contDiffAt.comp x (ihr (History.supported_right hs) _ _ hu.2.1 hu.2.2.2 hpos hminus
        (fun i => hc (Sum.inr (Sum.inr i))) (fun i => hcp (Sum.inr (Sum.inr i))))

theorem actualRealHistoryScalar_contDiffAt (b s : ℕ) (X tb td G : ℝ)
    (hX : 0 < X) (outside : List ℕ) (houtside : ∀ q ∈ outside, 0 < q)
    {l : ℕ} {V : ℕ → ℕ} (h : History l) (hs : h.Supported V outside)
    (x : Key h → ℝ) (hx : ∀ i, 0 < x i) :
    ContDiffAt ℝ ∞ (actualRealHistoryScalar b s X tb td G outside h hs) x := by
  apply encode_realHistoryScalar_contDiffAt b s X tb td G hX outside houtside h hs
    (rootExpr h) (compensationExpr h) x
  · exact ⟨trivial,trivial,fun _ => trivial⟩
  · exact fun i => hx _
  · exact hx _
  · exact hx _
  · exact fun _ => trivial
  · exact fun i => hx _

theorem actualRealHistoryScalar_log_contDiff (b s : ℕ) (X tb td G : ℝ)
    (hX : 0 < X) (outside : List ℕ) (houtside : ∀ q ∈ outside, 0 < q)
    {l : ℕ} {V : ℕ → ℕ} (h : History l) (hs : h.Supported V outside) :
    ContDiff ℝ ∞ (fun y : Key h → ℝ =>
      actualRealHistoryScalar b s X tb td G outside h hs (fun i => Real.exp (y i))) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  have hexp : ContDiffAt ℝ ∞ (fun z : Key h → ℝ => fun i => Real.exp (z i)) y := by fun_prop
  exact (actualRealHistoryScalar_contDiffAt b s X tb td G hX outside houtside h hs
    (fun i => Real.exp (y i)) (fun i => Real.exp_pos _)).comp y hexp

end HistorySymbolicEncoding
end Ostmann.Arithmetic

end

end OAI
