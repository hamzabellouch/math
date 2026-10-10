import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightLabels
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportScalarState
import OAI.NumberTheory.Ostmann.Construction.CanonicalOccurrenceTransportScalarTreeBasic

namespace OAI

noncomputable section
namespace Ostmann.Construction.CanonicalOccurrenceTransport
open Arithmetic.HistorySymbolicEncoding Arithmetic.HistorySymbolicState

theorem realHistoryScalar_eq_of_code_plan {ι : Type} (seed : List SourceSlot)
    {l : ℕ} {V W : ℕ → ℕ} {outside : List ℕ}
    (h g : History l) (hs : h.Supported V outside) (gs : g.Supported W outside)
    (e : TreeExpr ι h) (f : TreeExpr ι g)
    (hh : TreeSourceLabels seed h) (hg : TreeSourceLabels seed g)
    (hc : treeCode h e=treeCode g f) (hp : plan h hs=plan g gs)
    (b s : ℕ) (X tb td G : ℝ) (x : ι → ℝ) :
    realHistoryScalar b s X tb td G outside x h e=
      realHistoryScalar b s X tb td G outside x g f := by
  induction h with
  | leaf a =>
    cases g with
    | leaf a' =>
      have hf : a.frequency=a'.frequency := by
        simpa only [plan_rootFrequency,History.root] using congrArg Plan.rootFrequency hp
      exact realScalar_eq_of_stateCode e f hc seed hh hg hf b s X tb td outside x
  | @node l a p u hl hr left right ihl ihr =>
    cases g with
    | node a' p' u' hl' hr' left' right' =>
      have hcl : treeCode left e.2.1=treeCode left' f.2.1 := congrArg (fun t => t.2.1) hc
      have hcr : treeCode right e.2.2=treeCode right' f.2.2 := congrArg (fun t => t.2.2) hc
      have hpl : plan left (History.supported_left hs)=
          plan left' (History.supported_left gs) := congrArg Plan.leftPlan hp
      have hpr : plan right (History.supported_right hs)=
          plan right' (History.supported_right gs) := congrArg Plan.rightPlan hp
      have hroot := treeRoot_plus_eq_of_code e.2.1 f.2.1 hcl
      simp only [realHistoryScalar,hroot,
        ihl left' (History.supported_left hs) (History.supported_left gs) e.2.1 f.2.1
          hh.2.2.2.2.1 hg.2.2.2.2.1 hcl hpl,
        ihr right' (History.supported_right hs) (History.supported_right gs) e.2.2 f.2.2
          hh.2.2.2.2.2 hg.2.2.2.2.2 hcr hpr]

end Ostmann.Construction.CanonicalOccurrenceTransport

end

end OAI
