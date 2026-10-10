import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightRelativeNode

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicEncoding
open Construction Characters.RationalHistory HistorySymbolicState HistorySymbolicSlots
open HistoryOccurrenceVariables
variable {ι : Type*}

theorem encode_source_relativeControl (b s k : ℕ) (tb td G K : ℝ)
    (center : ℕ → ℝ) (slot : ι → Option SmallSlot) (x : ι → ℝ)
    (hx : ∀ i, 0 < x i) (hsource : IndependentSourceCells slot center x)
    {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside)
    (hlabels : TreeSourceLabels (Template.initial (2*b) k) h)
    (e : StateExpr h.root ι) (comp : InternalKey h → Expr ι)
    (he : StateAtomSlots slot e)
    (hc : ∀ i, ∃ j, comp i = .atom j ∧ slot j = some (internalSlot h i))
    (her : e.plus.RelativeControl x K ∧ e.minus.RelativeControl x K)
    (hp : 0 < e.plus.realEval x) (hm : 0 < e.minus.realEval x)
    (hgp : |Real.log (e.plus.realEval x)-G| ≤ 1)
    (hgm : |Real.log (e.minus.realEval x)-G| ≤ 1)
    (hsupport : realHistorySupportWeight b s tb td G outside x h
      (encode V outside h hs e comp) ≠ 0)
    (hlevel : ∀ j < l, Real.exp (sourceCancellationExponent V b k tb center j) ≤ K) :
    TreeRelativeControl x K h (encode V outside h hs e comp) := by
  induction h with
  | leaf a => exact her
  | @node l a p u hplus hminus left right ihl ihr =>
    let c := fun i => comp (Sum.inl i)
    have hu : AtomSlotsCorrect slot u c := by
      intro i
      simpa only [internalSlot,Sum.elim_inl,c] using hc (Sum.inl i)
    have hchildren := children_atomSlots slot hs e c he hu
    have hcl : ∀ i, ∃ j, comp (Sum.inr (Sum.inl i)) = .atom j ∧
        slot j = some (internalSlot left i) := by
      intro i
      simpa only [internalSlot,Sum.elim_inr,Sum.elim_inl] using hc (Sum.inr (Sum.inl i))
    have hcr : ∀ i, ∃ j, comp (Sum.inr (Sum.inr i)) = .atom j ∧
        slot j = some (internalSlot right i) := by
      intro i
      simpa only [internalSlot,Sum.elim_inr] using hc (Sum.inr (Sum.inr i))
    have hpivot := source_node_relativeControl b s k tb td G K center slot x hx hsource
      hs hlabels e comp he hc her hp hm hgp hgm hsupport (hlevel l (by omega))
    have hleftsupport : realHistorySupportWeight b s tb td G outside x left
        (encode V outside left (History.supported_left hs) (leftState hs e c)
          (fun i => comp (Sum.inr (Sum.inl i)))) ≠ 0 := by
      intro hz
      apply hsupport
      simp only [encode,realHistorySupportWeight]
      change _ * realHistorySupportWeight b s tb td G outside x left
        (encode V outside left (History.supported_left hs) (leftState hs e c)
          (fun i => comp (Sum.inr (Sum.inl i)))) * _ = 0
      rw [hz,mul_zero,zero_mul]
    have hrightsupport : realHistorySupportWeight b s tb td G outside x right
        (encode V outside right (History.supported_right hs) (rightState hs e c)
          (fun i => comp (Sum.inr (Sum.inr i)))) ≠ 0 := by
      intro hz
      apply hsupport
      simp only [encode,realHistorySupportWeight]
      change _ * _ * realHistorySupportWeight b s tb td G outside x right
        (encode V outside right (History.supported_right hs) (rightState hs e c)
          (fun i => comp (Sum.inr (Sum.inr i)))) = 0
      rw [hz,mul_zero]
    have hlevel' : ∀ j < l, Real.exp (sourceCancellationExponent V b k tb center j) ≤ K :=
      fun j hj => hlevel j (by omega)
    exact ⟨her,
      ihl (History.supported_left hs) hlabels.2.2.2.2.1 (leftState hs e c) _
        hchildren.1 hcl ⟨hpivot.1,her.1⟩ hpivot.2.1 hp hpivot.2.2 hgp hleftsupport hlevel',
      ihr (History.supported_right hs) hlabels.2.2.2.2.2 (rightState hs e c) _
        hchildren.2 hcr ⟨hpivot.1,her.2⟩ hpivot.2.1 hm hpivot.2.2 hgm hrightsupport hlevel'⟩

theorem symbolicHistory_source_relativeControl (b s k : ℕ) (tb td G : ℝ)
    (center : ℕ → ℝ) {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside)
    (hlabels : TreeSourceLabels (Template.initial (2*b) k) h)
    (x : Key h → ℝ) (hx : ∀ i, 0 < x i)
    (hsource : IndependentSourceCells (independentSlot h) center x)
    (hgiant : ∀ j : Bool, |Real.log (x (Sum.inl j))-G| ≤ 1)
    (hsupport : realHistorySupportWeight b s tb td G outside x h (symbolicHistory h hs) ≠ 0) :
    TreeRelativeControl x (sourceCancellationBound V b k tb center l) h (symbolicHistory h hs) :=
  encode_source_relativeControl b s k tb td G _ center (independentSlot h) x hx hsource h hs hlabels
    (rootExpr h) (compensationExpr h)
    (fun i => ⟨Sum.inr (Sum.inl i),rfl,rfl⟩) (fun i => ⟨Sum.inr (Sum.inr i),rfl,rfl⟩)
    ⟨(hx _).ne',(hx _).ne'⟩ (hx _) (hx _) (hgiant false) (hgiant true) hsupport
    (fun j hj => sourceCancellationExponent_exp_le V b k tb center (j := j) hj)

theorem symbolicHistory_source_derivativeBudget (b s k : ℕ) (tb td G : ℝ)
    (center : ℕ → ℝ) {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside)
    (hlabels : TreeSourceLabels (Template.initial (2*b) k) h)
    (x : Key h → ℝ) (hx : ∀ i, 0 < x i)
    (houtside : ∀ q ∈ outside, 0 < q)
    (hsource : IndependentSourceCells (independentSlot h) center x)
    (hgiant : ∀ j : Bool, |Real.log (x (Sum.inl j))-G| ≤ 1)
    (hsupport : realHistorySupportWeight b s tb td G outside x h (symbolicHistory h hs) ≠ 0) :
    let K := sourceCancellationBound V b k tb center l
    TreeDerivativeBudget outside x K
      ((2^l*(2+h.root.small.length+2*h.internalOccurrences.length):ℕ)*K^l)
      h (symbolicHistory h hs) := by
  apply symbolicHistory_derivativeBudget _ (sourceCancellationBound_one_le V b k tb center l)
    h hs x hx houtside
  exact symbolicHistory_source_relativeControl b s k tb td G center h hs hlabels x hx hsource hgiant hsupport

end Ostmann.Arithmetic.HistorySymbolicEncoding

end

end OAI
