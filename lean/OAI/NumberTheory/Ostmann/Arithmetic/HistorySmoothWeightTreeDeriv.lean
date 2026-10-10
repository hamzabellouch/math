import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightDerivConstants
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightSourceTree

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicEncoding
open Construction Characters.RationalHistory HistorySymbolicState HistoryOccurrenceVariables
open InitialCoordinatesTemplate
open scoped FourierTransform SchwartzMap
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem encode_deriv_le_on_source_support (b s k : ℕ) (X tb td G Δ E K B : ℝ)
    (center : ℕ → ℝ) (outside : List ℕ) (slot : ι → Option SmallSlot) (x : ι → ℝ) (i : ι)
    (hX : 0 < X) (hx : ∀ j, 0 < x j) (houtside : ∀ q ∈ outside, 0 < q)
    (hout : outside.length=2*s) (hsource : IndependentSourceCells slot center x)
    (hK : 1 ≤ K) (hB : 0 ≤ B)
    (hcenter : Real.log X+Δ-E ≤ 2*G+2*tb+2*td+
      (∑ h,∑ j,topCenters b center h j)+
      (∑ h,∑ j : Fin k,∑ r,compensationCenters b center h j r))
    {l : ℕ} {V : ℕ → ℕ} (h : History l) (hs : h.Supported V outside)
    (hleaf : ∀ a ∈ h.leafStates, Template.Matches (Template.initial (2*b) k) a.small)
    (e : StateExpr h.root ι) (comp : InternalKey h → Expr ι)
    (he : StateAtomSlots slot e) (hreg : e.RealRegular x)
    (hc : ∀ j, ∃ r, comp j = .atom r ∧ slot r = some (internalSlot h j))
    (hp : 0 < e.plus.realEval x) (hm : 0 < e.minus.realEval x)
    (hgp : |Real.log (e.plus.realEval x)-G| ≤ 1)
    (hgm : |Real.log (e.minus.realEval x)-G| ≤ 1)
    (hbudget : TreeDerivativeBudget outside x K B h (encode V outside h hs e comp))
    (hsupport : realHistorySupportWeight b s tb td G outside x h (encode V outside h hs e comp) ≠ 0) :
    ‖deriv (fun t => realHistoryScalar b s X tb td G outside (Expr.logCurve x i t)
      h (encode V outside h hs e comp)) 0‖ ≤
      (sourceLeafAmplitude k Δ E)^(2^l) * historyDerivativeCount l * actualSourceDerivativeRate B := by
  induction h with
  | leaf a =>
    have hd := e.realScalar_logCurve_deriv_le_sourceRanges b s k X tb td G Δ E K
      partitionDerivativeConstant center outside slot x i hX hx houtside hout
      (hleaf a (by simp only [History.leafStates,List.mem_singleton])) he hsource hp hm hgp hgm
      hcenter hK hbudget.1 partitionDerivativeConstant_pos.le partition_deriv_le_constant
    have hr := leaf_source_derivative_rate k Δ E B partitionDerivativeConstant cellDerivativeConstant
      ((e.periodExpr outside).logBudget K) a.small.length hB partitionDerivativeConstant_pos.le
      cellDerivativeConstant_pos.le ((e.periodExpr outside).logBudget_nonneg (zero_le_one.trans hK))
      hbudget.2.1 (Nat.cast_nonneg _) hbudget.2.2
    change ‖deriv (fun t => e.realScalar b s X tb td outside (Expr.logCurve x i t)) 0‖ ≤
      (sourceLeafAmplitude k Δ E)^(2^0) * historyDerivativeCount 0 * actualSourceDerivativeRate B
    rw [pow_zero, pow_one, historyDerivativeCount_zero, mul_one]
    simp only [actualSourceDerivativeRate]
    exact hd.trans hr
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
    have hu : AtomSlotsCorrect slot u c := by
      intro j; simpa only [internalSlot,Sum.elim_inl,c] using hc (Sum.inl j)
    have hat := children_atomSlots slot hs e c he hu
    have hcl : ∀ j, ∃ r, cl j = .atom r ∧ slot r = some (internalSlot left j) := by
      intro j; simpa only [cl,internalSlot,Sum.elim_inr,Sum.elim_inl] using hc (Sum.inr (Sum.inl j))
    have hcr : ∀ j, ∃ r, cr j = .atom r ∧ slot r = some (internalSlot right j) := by
      intro j; simpa only [cr,internalSlot,Sum.elim_inr] using hc (Sum.inr (Sum.inr j))
    have hcleaf : ∀ a ∈ left.leafStates, Template.Matches (Template.initial (2*b) k) a.small :=
      fun a ha => hleaf a (by simp only [History.leafStates,List.mem_append]; exact Or.inl ha)
    have hcrleaf : ∀ a ∈ right.leafStates, Template.Matches (Template.initial (2*b) k) a.small :=
      fun a ha => hleaf a (by simp only [History.leafStates,List.mem_append]; exact Or.inr ha)
    have hcreg : ∀ j, (comp j).RealRegularAt x := by
      intro j; obtain ⟨r,hr,_⟩ := hc j; rw [hr]; trivial
    have hcpos : ∀ j, 0 < (comp j).realEval x := by
      intro j; obtain ⟨r,hr,_⟩ := hc j; rw [hr]; exact hx r
    have hchildren := children_realRegular hs e c x hreg (StateAtomSlots.small_positive e he x hx)
      (fun j => hcreg (Sum.inl j)) (fun j => hcpos (Sum.inl j))
    have hcut : giantCell G ((pivotExpr hs e c).realEval x) ≠ 0 := by
      intro hz
      apply hsupport
      dsimp only [c] at hz
      simp only [encode,realHistorySupportWeight,treeRoot_encode,leftState,hz,zero_mul]
    obtain ⟨hpos,hcell⟩ := giantCell_ne_zero_support G _ hcut
    have hsl : realHistorySupportWeight b s tb td G outside x left
        (encode V outside left (History.supported_left hs) el cl) ≠ 0 := by
      intro hz
      apply hsupport
      simp only [encode,realHistorySupportWeight,treeRoot_encode]
      change _ * realHistorySupportWeight b s tb td G outside x left
        (encode V outside left (History.supported_left hs) el cl) * _ = 0
      rw [hz,mul_zero,zero_mul]
    have hsr : realHistorySupportWeight b s tb td G outside x right
        (encode V outside right (History.supported_right hs) er cr) ≠ 0 := by
      intro hz
      apply hsupport
      simp only [encode,realHistorySupportWeight,treeRoot_encode]
      change _ * realHistorySupportWeight b s tb td G outside x right
        (encode V outside right (History.supported_right hs) er cr) = 0
      rw [hz,mul_zero]
    have hb : (pivotExpr hs e c).RelativeControl x K ∧ (pivotExpr hs e c).logBudget K ≤ B ∧
        TreeDerivativeBudget outside x K B left (encode V outside left (History.supported_left hs) el cl) ∧
        TreeDerivativeBudget outside x K B right (encode V outside right (History.supported_right hs) er cr) := by
      simpa only [TreeDerivativeBudget,encode,treeRoot_encode,leftState,el,er,c,cl,cr] using hbudget
    have hdL : DifferentiableAt ℝ L 0 :=
      encode_realHistoryScalar_logCurve_differentiableAt b s X tb td G hX outside houtside left
        (History.supported_left hs) el cl x i hchildren.1 hchildren.2.2.1
        (by simpa only [el,leftState] using hpos) hp
        (fun j => hcreg (Sum.inr (Sum.inl j))) (fun j => hcpos (Sum.inr (Sum.inl j)))
    have hdR : DifferentiableAt ℝ R 0 :=
      encode_realHistoryScalar_logCurve_differentiableAt b s X tb td G hX outside houtside right
        (History.supported_right hs) er cr x i hchildren.2.1 hchildren.2.2.2
        (by simpa only [er,rightState] using hpos) hm
        (fun j => hcreg (Sum.inr (Sum.inr j))) (fun j => hcpos (Sum.inr (Sum.inr j)))
    have hdP := ((pivotExpr hs e c).hasDerivAt_logCurve x i (Expr.RelativeControl.regular _ x K hb.1)).differentiableAt
    have hdC : DifferentiableAt ℝ (fun t => giantCell G (P t)) 0 :=
      ((giantCell_contDiff G).differentiable (by simp) (P 0)).comp 0 hdP
    have hCD : |deriv (fun t => giantCell G (P t)) 0| ≤ actualSourceDerivativeRate B :=
      (cell_deriv_le_constant _ x i G K hK hb.1).trans
        ((mul_le_mul_of_nonneg_left hb.2.1 cellDerivativeConstant_pos.le).trans (cellDerivativeConstant_mul_le_rate hB))
    have hLn : ‖L 0‖ ≤ (sourceLeafAmplitude k Δ E)^(2^l) := by
      simpa only [L,Expr.logCurve_zero] using
        encode_norm_le_sourceRanges b s k X tb td G Δ E center outside slot x hX hx houtside hout hsource hcenter
          left (History.supported_left hs) hcleaf el cl hat.1 hcl
          (by simpa only [el,leftState] using hpos) hp (by simpa only [el,leftState] using hcell) hgp
    have hRn : ‖R 0‖ ≤ (sourceLeafAmplitude k Δ E)^(2^l) := by
      simpa only [R,Expr.logCurve_zero] using
        encode_norm_le_sourceRanges b s k X tb td G Δ E center outside slot x hX hx houtside hout hsource hcenter
          right (History.supported_right hs) hcrleaf er cr hat.2 hcr
          (by simpa only [er,rightState] using hpos) hm (by simpa only [er,rightState] using hcell) hgm
    have hLd := il (History.supported_left hs) hcleaf el cl hat.1 hchildren.1 hcl
      (by simpa only [el,leftState] using hpos) hp (by simpa only [el,leftState] using hcell) hgp hb.2.2.1 hsl
    have hRd := ir (History.supported_right hs) hcrleaf er cr hat.2 hchildren.2.1 hcr
      (by simpa only [er,rightState] using hpos) hm (by simpa only [er,rightState] using hcell) hgm hb.2.2.2 hsr
    have heq : (fun t => realHistoryScalar b s X tb td G outside (Expr.logCurve x i t)
        (.node a p u hplus hminus left right) (encode V outside _ hs e comp)) =
        (fun t => (giantCell G (P t):ℂ) * (L t * star (R t))) := by
      funext t
      simp only [encode,realHistoryScalar,treeRoot_encode,leftState,P,L,R,el,er,c,cl,cr,mul_assoc]
    rw [heq]
    have hprod := norm_deriv_cell_mul_conj_le (fun t => giantCell G (P t)) L R hdC hdL hdR
      ((sourceLeafAmplitude k Δ E)^(2^l)) (actualSourceDerivativeRate B) (historyDerivativeCount l)
      (pow_nonneg (sourceLeafAmplitude_pos k Δ E).le _) (actualSourceDerivativeRate_nonneg hB)
      (historyDerivativeCount_nonneg l)
      (by rw [abs_of_nonneg (giantCell_bounds _ _).1]; exact (giantCell_bounds _ _).2)
      hCD hLn hRn hLd hRd
    convert hprod using 1
    rw [← pow_mul,historyDerivativeCount_succ,pow_succ]

end Ostmann.Arithmetic.HistorySymbolicEncoding

end

end OAI
