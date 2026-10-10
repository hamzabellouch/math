import Mathlib
import OAI.Computability.QuantumFactoring.VerifiedTreeBounds
import OAI.Computability.QuantumFactoring.TableFavorableCount
import OAI.Computability.QuantumFactoring.RetainedTable

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NodeMachine
variable {n c : ℕ} (M : NodeMachine n c)

def retainedFavorableCount (t : ℕ) (m : BooleanNetwork (M.width t) n) :
    BooleanNetwork (M.width t) n := tableFavorableCountNet m (tableNets (M.fieldRows t))

lemma retainedFavorableCount_exact {N P d : ℕ} (hn : 2 ≤ n) (t : ℕ)
    (m : BooleanNetwork (M.width t) n) (x : Basis c) (r : Trace n t)
    (hc : PhysicalTree.CompleteLog n N (M.dataLog x t r))
    (hP : P∈(M.dataLog x t r).map Prod.fst) (hP0 : P≠0)
    (hd : 2 ≤ d) (hdiv : d∣P) (ho : Odd d)
    (hm : (bitsValue (m.eval (M.encoded x t r))).toNat=d) :
    (bitsValue ((M.retainedFavorableCount t m).eval (M.encoded x t r))).toNat=
      dataFavorable (trueData P) d n := by
  rw [dataFavorable_correct (by omega) (by omega) hdiv]
  have hval:=tableNets_values hn (M.fieldRows t) (M.encoded x t r)
  rw [M.fieldRows_values] at hval
  have hh:=tableFavorableCountNet_value hn m (tableNets (M.fieldRows t)) (M.encoded x t r)
    (hm ▸ hd) (hm ▸ ho) (by
      intro p hp
      apply PhysicalTree.tableFactors_prime hc
      rw [←hval]
      exact List.mem_map.mpr ⟨p,hp,rfl⟩) (by
      rw [hm,hval]
      exact PhysicalTree.tableFactors_cover hc hP hP0 (by omega) hdiv)
  simpa only [retainedFavorableCount,hm] using hh

lemma retainedFavorableCount_count {b : ℕ} (t : ℕ) (m : BooleanNetwork (M.width t) n)
    (hm : m.net.count ≤ b) (hq : M.query.net.count ≤ b) (hr : PhysicalNode.resultBound n ≤ b) :
    (M.retainedFavorableCount t m).net.count ≤
      tableFavorableCountBound n (t*n) (3*b+220*n+50) := by
  have hp:=tableNets_counts (M.fieldRows t) (c:=b) (by
    intro r hh
    have H:=M.fieldRows_counts t r hh
    exact ⟨H.1.trans hq,fun p hp=>(H.2 p hp).trans hr⟩)
  have hh:=tableFavorableCountNet_count m (tableNets (M.fieldRows t))
    (c:=3*b+220*n+50) (by omega) hp
  rwa [M.fieldRows_table_length] at hh
end NodeMachine
end ExactQuantumFactoring


end

end OAI
