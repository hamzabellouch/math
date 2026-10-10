import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListFinalDegree

namespace OAI

/-! Polynomial size bounds for the actual finite lists. A fixed number of
rounds grows the spin and bond counts linearly in the initial active-port mass. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram
open scoped BigOperators Classical

def portMass (gs : Groups) : ℕ := (gs.map List.length).sum

theorem portMass_sum (gs : Groups) :
    portMass gs=∑ i : Fin gs.length, (groupAt gs i.val).length := by
  have h := congrArg List.sum
    (ExactQuantumFactoring.BitStackProgram.map_range_getD gs [] List.length)
  simpa only [portMass,groupAt,range_sum] using h.symm

theorem pairCount_le_portMass (gs : Groups) : pairCount gs ≤ portMass gs := by
  have he : pairCount gs=∑ i : Fin gs.length, (groupAt gs i.val).length/2 := by
    simpa only [LocalPair,Fintype.card_sigma,Fintype.card_fin] using (localPair_card gs).symm
  rw [he,portMass_sum]
  exact Finset.sum_le_sum (fun i _ => Nat.div_le_self _ _)

theorem next_portMass_le (N : ℚ) (s : State) : portMass (next N s).2.2.2 ≤ portMass s.2.2.2 := by
  change (((List.range s.2.2.2.length).map (nextGroup s.1 (scale N s) s.2.2.2)).map List.length).sum ≤ _
  simp only [List.map_map,Function.comp_def,nextGroup_length,range_sum]
  rw [portMass_sum]
  exact Finset.sum_le_sum (fun i _ => by omega)

theorem iterate_portMass_le (N : ℚ) (s : State) (k : ℕ) :
    portMass (iterate N k s).2.2.2 ≤ portMass s.2.2.2 := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (next_portMass_le N (iterate N k s)).trans ih

theorem iterate_count_le (N : ℚ) (s : State) (k : ℕ) :
    (iterate N k s).1 ≤ s.1+2*k*portMass s.2.2.2 := by
  induction k with
  | zero => simp [iterate]
  | succ k ih =>
    have hp := (pairCount_le_portMass (iterate N k s).2.2.2).trans (iterate_portMass_le N s k)
    change (iterate N k s).1+2*pairCount (iterate N k s).2.2.2 ≤ _
    calc
      _ ≤ (s.1+2*k*portMass s.2.2.2)+2*portMass s.2.2.2 := by omega
      _ = s.1+2*(k+1)*portMass s.2.2.2 := by ring

theorem iterate_bonds_le (N : ℚ) (s : State) (k : ℕ) :
    (iterate N k s).2.1.length ≤ s.2.1.length+4*k*portMass s.2.2.2 := by
  induction k with
  | zero => simp [iterate]
  | succ k ih =>
    have hp := (pairCount_le_portMass (iterate N k s).2.2.2).trans (iterate_portMass_le N s k)
    rw [iterate,next_bonds_length]
    calc
      _ ≤ (s.2.1.length+4*k*portMass s.2.2.2)+4*portMass s.2.2.2 := by omega
      _ = s.2.1.length+4*(k+1)*portMass s.2.2.2 := by ring

theorem sum_ones {α : Type*} (xs : List α) : (xs.map (fun _ => (1:ℕ))).sum=xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,ih]
    omega

theorem activeBonds_length (gs : Groups) : (activeBonds gs).length=portMass gs := by
  simp only [activeBonds,List.length_flatten,List.map_map,Function.comp_def,starBonds,List.length_map,
    range_sum,portMass_sum]

theorem initial_portMass (n : ℕ) (bs : List Bond) (hb : SourceBondLists.bounded n bs)
    (c N : ℚ) : portMass (initial n bs c N).2.2.2=2*bs.length := by
  have h := initial_group_sum n bs hb (initialScale N bs c) (fun _ _ => (1:ℕ))
  simp only [sum_ones,List.length_range] at h
  change (((List.range n).map (initialGroup n bs (initialScale N bs c))).map List.length).sum = _
  simpa only [List.map_map,Function.comp_def] using h

theorem initial_iterate_count_le (n : ℕ) (bs : List Bond) (hb : SourceBondLists.bounded n bs)
    (c N : ℚ) (k : ℕ) :
    (iterate N k (initial n bs c N)).1 ≤ n+2*bs.length+4*k*bs.length := by
  have h := iterate_count_le N (initial n bs c N) k
  rw [initial_portMass n bs hb c N] at h
  change (iterate N k (initial n bs c N)).1 ≤ n+2*bs.length+2*k*(2*bs.length) at h
  convert h using 1
  ring

theorem initial_iterate_bonds_le (n : ℕ) (bs : List Bond) (hb : SourceBondLists.bounded n bs)
    (c N : ℚ) (k : ℕ) :
    ((iterate N k (initial n bs c N)).2.1++
      activeBonds (iterate N k (initial n bs c N)).2.2.2).length ≤
        3*bs.length+8*k*bs.length := by
  have h := iterate_bonds_le N (initial n bs c N) k
  rw [initial_portMass n bs hb c N] at h
  have hm := iterate_portMass_le N (initial n bs c N) k
  rw [initial_portMass n bs hb c N] at hm
  have hi : (initial n bs c N).2.1.length=bs.length := by
    simp only [initial,List.length_map,List.length_range]
  rw [hi] at h
  rw [List.length_append,activeBonds_length]
  calc
    _ ≤ (bs.length+4*k*(2*bs.length))+2*bs.length := Nat.add_le_add h hm
    _ = _ := by ring

end ContinuumCoulomb.QuantumForkList

end

end OAI
