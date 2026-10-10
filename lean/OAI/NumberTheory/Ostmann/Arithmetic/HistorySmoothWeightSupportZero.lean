import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightSourceBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightSupport

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic
open scoped ContDiff Topology
open Filter

theorem deriv_giantCell_mul_zero (G : ℝ) (p : ℝ → ℝ) (f : ℝ → ℂ)
    (hp : DifferentiableAt ℝ p 0) (hf : 0 < p 0 → DifferentiableAt ℝ f 0)
    (hz : giantCell G (p 0) = 0) :
    deriv (fun t => (giantCell G (p t):ℂ) * f t) 0 = 0 := by
  by_cases hpos : 0 < p 0
  · have hg : DifferentiableAt ℝ (fun t => giantCell G (p t)) 0 :=
      ((giantCell_contDiff G).differentiable (by simp) (p 0)).comp 0 hp
    have hgc : DifferentiableAt ℝ (fun t => (giantCell G (p t):ℂ)) 0 :=
      Complex.ofRealCLM.differentiableAt.comp 0 hg
    have hd : deriv (fun t => giantCell G (p t)) 0 = 0 :=
      deriv_eq_zero_of_nonneg_of_eq_zero _ 0 (fun t => (giantCell_bounds G (p t)).1) hz
    rw [deriv_fun_mul hgc (hf hpos),hg.hasDerivAt.ofReal_comp.deriv,hd,hz]
    simp only [Complex.ofReal_zero,zero_mul,add_zero]
  · have hlt : p 0 < Real.exp (G-1) := (le_of_not_gt hpos).trans_lt (Real.exp_pos _)
    have heq : (fun t => (giantCell G (p t):ℂ) * f t) =ᶠ[𝓝 0] (fun _ => (0:ℂ)) := by
      filter_upwards [hp.continuousAt.eventually (eventually_lt_nhds hlt)] with t ht
      simp only [giantCell_zero_of_le_lower G ht.le,Complex.ofReal_zero,zero_mul]
    rw [heq.deriv_eq,deriv_const]

namespace HistorySymbolicEncoding
open Construction Characters.RationalHistory HistorySymbolicState HistoryOccurrenceVariables
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem encode_deriv_zero_of_support_zero (b s : ℕ) (X tb td G : ℝ) (hX : 0 < X)
    (outside : List ℕ) (houtside : ∀ q ∈ outside, 0 < q)
    {l : ℕ} {V : ℕ → ℕ} (h : History l) (hs : h.Supported V outside)
    (e : StateExpr h.root ι) (comp : InternalKey h → Expr ι) (x : ι → ℝ) (i : ι)
    (hx : ∀ j, 0 < x j) (he : e.RealRegular x) (hatoms : StateSmallAtoms e)
    (hp : 0 < e.plus.realEval x) (hm : 0 < e.minus.realEval x)
    (hc : ∀ j, ∃ r, comp j = .atom r)
    (hz : realHistorySupportWeight b s tb td G outside x h (encode V outside h hs e comp) = 0) :
    deriv (fun t => realHistoryScalar b s X tb td G outside (Expr.logCurve x i t)
      h (encode V outside h hs e comp)) 0 = 0 := by
  have hsmall : ∀ j, 0 < (e.small j).realEval x := by
    intro j; obtain ⟨r,hr⟩ := hatoms j; rw [hr]; exact hx r
  have hcreg : ∀ j, (comp j).RealRegularAt x := by
    intro j; obtain ⟨r,hr⟩ := hc j; rw [hr]; trivial
  have hcpos : ∀ j, 0 < (comp j).realEval x := by
    intro j; obtain ⟨r,hr⟩ := hc j; rw [hr]; exact hx r
  induction h with
  | leaf a =>
    have hreg : (e.periodExpr outside).RealRegularAt x :=
      ⟨trivial,he.1,he.2.1,product_ofFn_realRegular e.small x he.2.2⟩
    exact e.realScalar_logCurve_deriv_zero_of_bins_zero b s X tb td outside x i hX hx houtside
      (e.realPeriod_pos outside x hp hm hsmall houtside) hreg hatoms hz
  | @node l a p u hplus hminus left right il ir =>
    let c := fun j => comp (Sum.inl j)
    let el := leftState hs e c
    let er := rightState hs e c
    let cl := fun j => comp (Sum.inr (Sum.inl j))
    let cr := fun j => comp (Sum.inr (Sum.inr j))
    let P (t : ℝ) := (pivotExpr hs e c).realEval (Expr.logCurve x i t)
    let L (t : ℝ) := realHistoryScalar b s X tb td G outside (Expr.logCurve x i t) left
      (encode V outside left (History.supported_left hs) el cl)
    let R (t : ℝ) := realHistoryScalar b s X tb td G outside (Expr.logCurve x i t) right
      (encode V outside right (History.supported_right hs) er cr)
    have hreg := children_realRegular hs e c x he hsmall
      (fun j => hcreg (Sum.inl j)) (fun j => hcpos (Sum.inl j))
    have hat := children_smallAtoms hs e c hatoms (fun j => hc (Sum.inl j))
    have hdP : DifferentiableAt ℝ P 0 :=
      ((pivotExpr hs e c).hasDerivAt_logCurve x i hreg.1.1).differentiableAt
    have hdL (hpos : 0 < P 0) : DifferentiableAt ℝ L 0 :=
      encode_realHistoryScalar_logCurve_differentiableAt b s X tb td G hX outside houtside left
        (History.supported_left hs) el cl x i hreg.1 hreg.2.2.1
        (by simpa only [P,Expr.logCurve_zero,el,er,leftState,rightState] using hpos) hp
        (fun j => hcreg (Sum.inr (Sum.inl j))) (fun j => hcpos (Sum.inr (Sum.inl j)))
    have hdR (hpos : 0 < P 0) : DifferentiableAt ℝ R 0 :=
      encode_realHistoryScalar_logCurve_differentiableAt b s X tb td G hX outside houtside right
        (History.supported_right hs) er cr x i hreg.2.1 hreg.2.2.2
        (by simpa only [P,Expr.logCurve_zero,el,er,leftState,rightState] using hpos) hm
        (fun j => hcreg (Sum.inr (Sum.inr j))) (fun j => hcpos (Sum.inr (Sum.inr j)))
    have heq : (fun t => realHistoryScalar b s X tb td G outside (Expr.logCurve x i t)
        (.node a p u hplus hminus left right) (encode V outside _ hs e comp)) =
        (fun t => (giantCell G (P t):ℂ) * (L t * star (R t))) := by
      funext t
      simp only [encode,realHistoryScalar,treeRoot_encode,leftState,P,L,R,el,er,c,cl,cr,mul_assoc]
    rw [heq]
    by_cases hcut : giantCell G (P 0) = 0
    · exact deriv_giantCell_mul_zero G P (fun t => L t * star (R t)) hdP
        (fun hpos => (hdL hpos).mul (hdR hpos).star) hcut
    · have hpos : 0 < P 0 := (giantCell_ne_zero_support G (P 0) hcut).1
      have hL := hdL hpos
      have hR := hdR hpos
      have hC : DifferentiableAt ℝ (fun t => (giantCell G (P t):ℂ)) 0 :=
        Complex.ofRealCLM.differentiableAt.comp 0
          (((giantCell_contDiff G).differentiable (by simp) (P 0)).comp 0 hdP)
      have hchild :
          realHistorySupportWeight b s tb td G outside x left (encode V outside left (History.supported_left hs) el cl) = 0 ∨
          realHistorySupportWeight b s tb td G outside x right (encode V outside right (History.supported_right hs) er cr) = 0 := by
        simp only [encode,realHistorySupportWeight,treeRoot_encode,leftState] at hz
        have hcut' : giantCell G ((pivotExpr hs e c).realEval x) ≠ 0 := by
          simpa only [P,Expr.logCurve_zero] using hcut
        rcases mul_eq_zero.mp hz with hc | hr
        · exact Or.inl ((mul_eq_zero.mp hc).resolve_left hcut')
        · exact Or.inr hr
      rcases hchild with hl | hr
      · have hL0 : L 0 = 0 := by
          simpa only [L,Expr.logCurve_zero] using
            realHistoryScalar_eq_zero_of_support_zero b s X tb td G outside x left _ hl
        have hdL0 : deriv L 0 = 0 := il (History.supported_left hs) el cl hreg.1 hat.1
          (by simpa only [P,Expr.logCurve_zero,el,er,leftState,rightState] using hpos) hp (fun j => hc (Sum.inr (Sum.inl j))) hl
          hreg.2.2.1 (fun j => hcreg (Sum.inr (Sum.inl j))) (fun j => hcpos (Sum.inr (Sum.inl j)))
        rw [(hC.hasDerivAt.fun_mul (hL.hasDerivAt.fun_mul hR.hasDerivAt.star)).deriv,hdL0,hL0]
        simp only [zero_mul,add_zero,mul_zero]
      · have hR0 : R 0 = 0 := by
          simpa only [R,Expr.logCurve_zero] using
            realHistoryScalar_eq_zero_of_support_zero b s X tb td G outside x right _ hr
        have hdR0 : deriv R 0 = 0 := ir (History.supported_right hs) er cr hreg.2.1 hat.2
          (by simpa only [P,Expr.logCurve_zero,el,er,leftState,rightState] using hpos) hm (fun j => hc (Sum.inr (Sum.inr j))) hr
          hreg.2.2.2 (fun j => hcreg (Sum.inr (Sum.inr j))) (fun j => hcpos (Sum.inr (Sum.inr j)))
        rw [(hC.hasDerivAt.fun_mul (hL.hasDerivAt.fun_mul hR.hasDerivAt.star)).deriv,hdR0,hR0]
        simp only [star_zero,add_zero,mul_zero]

end HistorySymbolicEncoding
end Ostmann.Arithmetic

end

end OAI
