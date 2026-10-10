import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListSites
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListSum
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListBackground

namespace OAI

/-! The literal rational scale is exactly the scale appearing in the checked
parallel-fork theorem, including all retained odd-port coefficients. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open scoped BigOperators Classical

theorem catalog_weights_sum (gs : Groups) (f : ℚ → ℚ → ℚ) :
    (((catalog gs).map Prod.snd).map (fun p => f p.1.2 p.2.2)).sum =
      ∑ e : Fin (pairCount gs), f (actualJ gs e) (actualK gs e) := by
  rw [List.map_map]
  change ((catalog gs).map (fun p => f p.2.1.2 p.2.2.2)).sum=_
  rw [← ExactQuantumFactoring.BitStackProgram.map_range_getD (catalog gs)
    (0,((0,0),(0,0))) (fun p => f p.2.1.2 p.2.2.2),catalog_length,range_sum]
  apply Finset.sum_congr rfl
  intro e _
  have hc := catalog_pairEquiv gs (localPair gs e)
  rw [show pairEquiv gs (localPair gs e)=e from (pairEquiv gs).apply_symm_apply e] at hc
  rw [hc]
  rfl

theorem scale_eq_graphScale (s : State)
    (hb : SourceBondLists.bounded s.1 (background s))
    (hn : ∀ b ∈ background s, b.1 ≠ b.2.1) (N : ℚ) :
    scale N s = graphScale (backgroundGraph s hb hn).weight
      (actualJ s.2.2.2) (actualK s.2.2.2) s.2.2.1 N := by
  have hL : (((catalog s.2.2.2).map Prod.snd).map pairLinear).sum =
      ∑ e, (1+2*|actualJ s.2.2.2 e|+2*|actualK s.2.2.2 e|) :=
    catalog_weights_sum s.2.2.2 (fun J K => 1+2*|J|+2*|K|)
  have hS : (((catalog s.2.2.2).map Prod.snd).map pairSquare).sum =
      ∑ e, (1+|actualJ s.2.2.2 e|+|actualK s.2.2.2 e|)^2 :=
    catalog_weights_sum s.2.2.2 (fun J K => (1+|J|+|K|)^2)
  have hw : (∑ e : Fin (background s).length, |((background s).get e).2.2|) =
      ((retained s).map abs).sum := background_sum s hb hn abs
  change scale N s = graphScale (fun e : Fin (background s).length => ((background s).get e).2.2)
    (actualJ s.2.2.2) (actualK s.2.2.2) s.2.2.1 N
  dsimp only [scale,graphScale]
  rw [hL,hS,hw]

end ContinuumCoulomb.QuantumForkList

end

end OAI
