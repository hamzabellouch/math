import OAI.NumberTheory.Ostmann.Arithmetic.HistoryProductWindowsBulk
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightTree

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryProductWindows
open Construction Characters.RationalHistory HistorySymbolicSlots HistorySymbolicState
open HistorySymbolicEncoding HistoryOccurrenceVariables
variable {ι : Type*}

theorem leafBins_of_scalar_ne_zero (b s k : ℕ) (X tb td G : ℝ)
    (outside : List ℕ) (x : ι → ℝ) {l : ℕ} (h : History l) (e : TreeExpr ι h)
    (hm : ∀a∈h.leafStates,Template.Matches (Template.initial (2*b) k) a.small)
    (hne : realHistoryScalar b s X tb td G outside x h e ≠ 0) :
    LeafBins b s k tb td outside x h e := by
  induction h with
  | leaf a =>
    refine ⟨hm a (by simp [History.leafStates]),?_⟩
    intro hb
    apply hne
    simp only [realHistoryScalar, StateExpr.realScalar, hb, Complex.ofReal_zero, mul_zero]
  | @node l a p u hp hm' left right ihl ihr =>
    have hl : realHistoryScalar b s X tb td G outside x left e.2.1 ≠ 0 := by
      intro hz
      apply hne
      simp only [realHistoryScalar,hz,mul_zero,zero_mul]
    have hr : realHistoryScalar b s X tb td G outside x right e.2.2 ≠ 0 := by
      intro hz
      apply hne
      simp only [realHistoryScalar,hz,star_zero,mul_zero]
    exact ⟨ihl e.2.1 (fun a ha => hm a (by simpa only [History.leafStates,List.mem_append] using Or.inl ha)) hl,
      ihr e.2.2 (fun a ha => hm a (by simpa only [History.leafStates,List.mem_append] using Or.inr ha)) hr⟩

theorem inherited_bulkLog_of_scalar (b s k : ℕ) (X tb td G : ℝ) (x : ι → ℝ)
    {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (e : StateExpr h.root ι)
    (comp : InternalKey h → Expr ι)
    (hm : ∀a∈h.leafStates,Template.Matches (Template.initial (2*b) k) a.small)
    (hne : realHistoryScalar b s X tb td G outside x h (encode V outside h hs e comp) ≠ 0) :
    |bulkLog h.root.small e.small x - (2:ℝ)^l*(2*tb)| ≤ (2:ℝ)^l*2 :=
  inherited_bulkLog_bound b s k tb td x h hs e comp
    (leafBins_of_scalar_ne_zero b s k X tb td G outside x h _ hm hne)

end Ostmann.Arithmetic.HistoryProductWindows

end

end OAI
