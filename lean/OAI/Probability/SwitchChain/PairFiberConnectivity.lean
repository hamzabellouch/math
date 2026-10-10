import OAI.Probability.SwitchChain.HavelConnectivity
import OAI.Probability.SwitchChain.PairFiberRedundancy

namespace OAI

noncomputable section

namespace Problem315.PairResampling

attribute [local instance] Classical.propDecidable

theorem fourVertexState_sameFiber {n : Nat} {d : Fin n → Nat}
    (G : GraphState n d) (a b c e : Fin n) (h : FourDistinct a b c e)
    (hab : G.val.Adj a b) (hce : G.val.Adj c e)
    (hac : ¬ G.val.Adj a c) (hbe : ¬ G.val.Adj b e) :
    SameFiber {a, e} G.val (fourVertexState G a b c e h).val := by
  apply (sameFiber_iff_outside_inside {a, e} G _).mpr
  constructor
  · intro u hu v hv
    have hua : u ≠ a := fun h' => hu (by simp [h'])
    have hue : u ≠ e := fun h' => hu (by simp [h'])
    have hva : v ≠ a := fun h' => hv (by simp [h'])
    have hve : v ≠ e := fun h' => hv (by simp [h'])
    change G.val.Adj u v ↔
      (proposalResult G.val (fourVertexProposal a b c e h)).Adj u v
    rw [proposalResult_fourVertex_adj G.val a b c e h hab hce hac hbe]
    simp [hua, hue, hva, hve]
  · intro u hu v hv
    have hub : u ≠ b := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact h.1
      · exact h.2.2.2.2.1.symm
    have huc : u ≠ c := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact h.2.1
      · exact h.2.2.2.2.2.symm
    have hvb : v ≠ b := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact h.1
      · exact h.2.2.2.2.1.symm
    have hvc : v ≠ c := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact h.2.1
      · exact h.2.2.2.2.2.symm
    change G.val.Adj u v ↔
      (proposalResult G.val (fourVertexProposal a b c e h)).Adj u v
    rw [proposalResult_fourVertex_adj G.val a b c e h hab hce hac hbe]
    simp [hub, huc, hvb, hvc]

def FiberMove (n : Nat) (d : Fin n → Nat) (G H : GraphState n d) : Prop :=
  ∃ a ∈ pairs n, SameFiber a G.val H.val

theorem fiberMove_connectivity (n : Nat) (d : Fin n → Nat) (G H : GraphState n d) :
    Relation.ReflTransGen (FiberMove n d) G H := by
  apply connectivity_of_fourVertex_moves n d (FiberMove n d) _ _ G H
  · intro K L h
    obtain ⟨a, ha, hfiber⟩ := h
    exact ⟨a, ha, hfiber.symm⟩
  · intro K a b c e h hab hce hac hbe
    refine ⟨{a, e}, ?_, fourVertexState_sameFiber K a b c e h hab hce hac hbe⟩
    simp [pairs, Finset.mem_powersetCard, h.2.2.1]

theorem generator_eq_zero_iff_constant {n : Nat} {d : Fin n → Nat}
    (f : StateSpace n d) :
    generator n d f = 0 ↔ ∀ G H : GraphState n d, f G = f H := by
  constructor
  · intro hf G H
    have hconst := (generator_eq_zero_iff f).mp hf
    have hpath := fiberMove_connectivity n d G H
    induction hpath with
    | refl => rfl
    | @tail K L hGK hKL ih =>
      obtain ⟨a, ha, hsame⟩ := hKL
      exact ih.trans (hconst a ha K L hsame)
  · intro hf
    apply (generator_eq_zero_iff f).mpr
    intro a ha G H _
    exact hf G H

end Problem315.PairResampling

end

end OAI
