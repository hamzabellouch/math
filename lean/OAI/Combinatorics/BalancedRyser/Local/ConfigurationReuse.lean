import OAI.Combinatorics.BalancedRyser.Local.Local
import OAI.Combinatorics.BalancedRyser.Probability.ConfigurationStructure
import OAI.Combinatorics.BalancedRyser.Probability.TupleExposure

namespace OAI

namespace Balanced
open scoped _root_.Balanced

noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem Configuration.exists_pencil_reuse_witness (C : Configuration F)
    (hvalid : C.Valid) (hcompatible : C.Compatible) (p : Point F)
    (hreuse : 3 ≤ Local.reuseCount C p) :
    ∃ l : List (Slot F), l.Nodup ∧
      (∀ s ∈ l, OnLine p (C.choice s).line) ∧ l.length ≤ 6 ∧
      3 ≤ reuseExposureScore (fun s => generatorSet (C.choice s).tuple) l := by
  have hcount := ConfigurationStructure.split_multiplicity_eq_slots C hvalid hcompatible p
  have hreuse' : 3 ≤
      4 * (Finset.univ.filter (fun s : Slot F => OnLine p (C.choice s).line)).card -
      ((Finset.univ.filter (fun s : Slot F => OnLine p (C.choice s).line)).biUnion
        (fun s => generatorSet (C.choice s).tuple)).card := by
    simpa only [Local.reuseCount, Local.generatorUnionAt, hcount] using hreuse
  obtain ⟨l, hnodup, hsub, hlength, hscore⟩ :=
    C.exists_six_tuple_reuse_order hvalid hcompatible _ hreuse'
  refine ⟨l, hnodup, ?_, hlength, hscore⟩
  intro s hs
  exact (Finset.mem_filter.mp (hsub (List.mem_toFinset.mpr hs))).2

theorem Configuration.tuplePoint_ne_pencil_center (C : Configuration F)
    (hcompatible : C.Compatible) (p : Point F)
    (hmultiplicity : 2 ≤ C.splitMultiplicity p) (s : Slot F) (i : Fin 4) :
    tuplePoint C.merged (C.choice s).tuple i ≠ p := by
  intro heq
  have hp : p ∈ designated C.merged (C.choice s) := by
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, heq⟩
  exact ConfigurationStructure.center_not_designated C hcompatible hmultiplicity s hp

end
end Balanced

end OAI
