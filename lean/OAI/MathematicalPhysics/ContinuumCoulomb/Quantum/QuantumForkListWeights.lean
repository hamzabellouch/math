import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListEnvelope
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListSize

namespace OAI

/-! Coefficient bounds for the actual ordered lists, including every active
port and the scalar offset. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

structure CoefficientBound (s : State) (L : ℝ) : Prop where
  scalar : |(s.2.2.1:ℝ)| ≤ L
  ordinary : ∀ b ∈ s.2.1, |(b.2.2:ℝ)| ≤ L
  active : ∀ ps ∈ s.2.2.2, ∀ p ∈ ps, |(p.2:ℝ)| ≤ L

theorem groupAt_mem (gs : Groups) (i : ℕ) (hi : i<gs.length) : groupAt gs i ∈ gs := by
  rw [groupAt,List.headD_eq_head?_getD,List.head?_drop,
    List.getElem?_eq_getElem hi,Option.getD_some]
  exact List.getElem_mem hi

theorem CoefficientBound.port (s : State) {L : ℝ} (h : CoefficientBound s L)
    (i : Fin s.2.2.2.length) (j : Fin (groupAt s.2.2.2 i.val).length) :
    |((portAt (groupAt s.2.2.2 i.val) j.val).2:ℝ)| ≤ L := by
  rw [portAt_eq_getElem _ _ j.isLt]
  exact h.active _ (groupAt_mem _ _ i.isLt) _ (List.getElem_mem j.isLt)

theorem CoefficientBound.actualJ (s : State) {L : ℝ} (h : CoefficientBound s L)
    (e : Fin (pairCount s.2.2.2)) : |(actualJ s.2.2.2 e:ℝ)| ≤ L :=
  h.port s (localPair s.2.2.2 e).1 (localFirst s.2.2.2 e)

theorem CoefficientBound.actualK (s : State) {L : ℝ} (h : CoefficientBound s L)
    (e : Fin (pairCount s.2.2.2)) : |(actualK s.2.2.2 e:ℝ)| ≤ L :=
  h.port s (localPair s.2.2.2 e).1 (localSecond s.2.2.2 e)

theorem unpairedBonds_length_le (gs : Groups) :
    (unpairedBonds gs).length ≤ portMass gs := by
  simp only [unpairedBonds,List.length_flatten,List.map_map,Function.comp_def,
    starBonds,List.length_map,unpaired_length,range_sum,portMass_sum]
  exact Finset.sum_le_sum (fun i _ => Nat.mod_le _ _)

theorem CoefficientBound.background (s : State) {L : ℝ} (h : CoefficientBound s L)
    (b : Bond) (hb : b ∈ background s) : |(b.2.2:ℝ)| ≤ L := by
  rcases List.mem_append.mp hb with hold | hnew
  · exact h.ordinary b hold
  obtain ⟨bs,hbs,hb⟩ := List.mem_flatten.mp hnew
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hbs
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hb
  exact h.active _ (groupAt_mem _ _ (List.mem_range.mp hi)) _ (List.mem_of_mem_drop hp)

theorem scale_abs_bound (s : State)
    (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) (N : ℚ) (hN : 0 ≤ N)
    {M L T : ℝ} (hM : (s.2.1.length+portMass s.2.2.2:ℕ) ≤ M)
    (hL : 1 ≤ L) (hT : |(N:ℝ)| ≤ T) (hc : CoefficientBound s L) :
    |(scale N s:ℝ)| ≤ forkRadius M L T := by
  have hm : ((background s).length:ℝ) ≤ M := by
    refine le_trans ?_ hM
    exact_mod_cast (show (background s).length ≤ s.2.1.length+portMass s.2.2.2 by
      simpa only [background,List.length_append] using
        Nat.add_le_add_left (unpairedBonds_length_le s.2.2.2) s.2.1.length)
  have hr : (pairCount s.2.2.2:ℝ) ≤ M := by
    refine le_trans ?_ hM
    exact_mod_cast (show pairCount s.2.2.2 ≤ s.2.1.length+portMass s.2.2.2 by
      have := pairCount_le_portMass s.2.2.2
      omega)
  rw [scale_eq_graphScale s hb hn N]
  exact graphScale_abs_bound _ _ _ _ _ hN hm hr hL hT hc.scalar
    (fun e => hc.background s _ (List.get_mem _ _)) (hc.actualJ s) (hc.actualK s)

end ContinuumCoulomb.QuantumForkList

end

end OAI
