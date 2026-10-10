import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListRealization

namespace OAI

/-! Full-space error for one actual literal fork round. Both sides are the
matrices defined by the emitted bond/port lists, with their scalar offsets. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorGraph QuantumRawExchange QuantumAxisSample
open scoped BigOperators Classical

theorem catalog_index_sum {M : Type} [AddCommMonoid M] (gs : Groups)
    (f : TaggedPair → M) : ((catalog gs).map f).sum =
      ∑ e : Fin (pairCount gs), f (((catalog gs).drop e.val).headD (0,((0,0),(0,0)))) := by
  rw [← ExactQuantumFactoring.BitStackProgram.map_range_getD (catalog gs)
    (0,((0,0),(0,0))) f,catalog_length,range_sum]

theorem rawBondMatrix_fin {n : ℕ} (a b : Fin n) (J : ℚ) :
    rawBondMatrix n (a.val,b.val,J)=(J:ℂ) • sourceHeisenbergMatrix n a b :=
  rawBondMatrix_erase (a,b,J)

theorem paired_matrix {n : ℕ} {gs : Groups} (hs : ValidPorts n gs) :
    ((pairedBonds gs).map (rawBondMatrix n)).sum =
      ∑ e : Fin (pairCount gs),
        ((actualJ gs e:ℂ) • sourceHeisenbergMatrix n (actualSite hs e 0) (actualSite hs e 1) +
         (actualK gs e:ℂ) • sourceHeisenbergMatrix n (actualSite hs e 0) (actualSite hs e 2)) := by
  simp only [pairedBonds,List.flatMap_def,List.map_flatten,List.sum_flatten,List.map_map,
    Function.comp_def,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  rw [catalog_index_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [catalog_actualSite hs e]
  simp only [rawBondMatrix_fin]

theorem input_matrix_graph (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) :
    matrix s = qmaExchangeMatrix (n := s.1) (backgroundGraph s hb hn).left (backgroundGraph s hb hn).right
      (fun e => ((backgroundGraph s hb hn).weight e:ℝ)) (s.2.2.1:ℝ) +
      ∑ e : Fin (pairCount s.2.2.2),
        ((actualJ s.2.2.2 e:ℂ) • sourceHeisenbergMatrix s.1 (actualSite hs e 0) (actualSite hs e 1) +
         (actualK s.2.2.2 e:ℂ) • sourceHeisenbergMatrix s.1 (actualSite hs e 0) (actualSite hs e 2)) := by
  have h := matrix_pairing s
  change matrix s=rawMatrix s.1 (background s,s.2.2.1)+_ at h
  rw [← background_matrix s hb hn,paired_matrix hs] at h
  exact h

theorem next_accuracy (s : State) (hs : ValidPorts s.1 s.2.2.2)
    (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) (N : ℚ) (hN : 0 < N) :
    |normalizedBottom (matrix (next N s))-normalizedBottom (matrix s)| ≤ 1/(N:ℝ) := by
  let left : Fin (background s).length → Fin s.1 := (backgroundGraph s hb hn).left
  let right : Fin (background s).length → Fin s.1 := (backgroundGraph s hb hn).right
  let w : Fin (background s).length → ℚ := (backgroundGraph s hb hn).weight
  have hneq : ∀ a, left a ≠ right a := (backgroundGraph s hb hn).distinct
  have h := graph_accuracy left right hneq w
    (actualSite hs) (actualSite_injective hs) (actualJ s.2.2.2) (actualK s.2.2.2) s.2.2.1 N hN
  dsimp only at h
  have hscale : graphScale w (actualJ s.2.2.2) (actualK s.2.2.2) s.2.2.1 N=scale N s :=
    (scale_eq_graphScale s hb hn N).symm
  rw [graph_matrix,hscale] at h
  change |normalizedBottom _-normalizedBottom _| ≤ 1/(N:ℝ) at h
  have hout : normalizedBottom (matrix (next N s)) =
      normalizedBottom (qmaForksGraph left right (fun e => (w e:ℝ)) (s.2.2.1:ℝ)
        (scale N s:ℝ) (actualSite hs) (fun e => (actualJ s.2.2.2 e:ℝ))
          (fun e => (actualK s.2.2.2 e:ℝ))) := next_bottom_graph s hs hb hn N
  have hin : matrix s = qmaExchangeMatrix left right (fun e => (w e:ℝ)) (s.2.2.1:ℝ)+
      ∑ e, ((actualJ s.2.2.2 e:ℂ) • sourceHeisenbergMatrix s.1 (actualSite hs e 0) (actualSite hs e 1)+
        (actualK s.2.2.2 e:ℂ) • sourceHeisenbergMatrix s.1 (actualSite hs e 0) (actualSite hs e 2)) :=
    input_matrix_graph s hs hb hn
  rw [← hout,← hin] at h
  exact h

end ContinuumCoulomb.QuantumForkList

end

end OAI
