import Mathlib
import OAI.Computability.QuantumFactoring.TableTotientCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork
namespace BitArithmetic

def primesPhiNet {k n : ℕ} (m : BooleanNetwork k n) (ps : List (BooleanNetwork k n)) :
    BooleanNetwork k n := totientFromList m (List.flatten (List.replicate n ps))

lemma primesPhiNet_value {k n : ℕ} (hn : 0<n) (m : BooleanNetwork k n)
    (ps : List (BooleanNetwork k n)) (x : Basis k) (hm : (bitsValue (m.eval x)).toNat≠0)
    (hp : ∀ p∈ps,((bitsValue (p.eval x)).toNat).Prime)
    (hcover : ∀ p : ℕ,p.Prime→p∣(bitsValue (m.eval x)).toNat→
      p∈ps.map (fun q=>(bitsValue (q.eval x)).toNat)) :
    (bitsValue ((primesPhiNet m ps).eval x)).toNat=(bitsValue (m.eval x)).toNat.totient := by
  let vals:=ps.map (fun q=>(bitsValue (q.eval x)).toNat)
  have hps : ∀ p∈vals,p.Prime := by
    intro p hp'
    obtain ⟨q,hq,rfl⟩:=List.mem_map.mp hp'
    exact hp q hq
  have hd:=PhysicalTree.dvd_cover_power vals hm (bitsValue (m.eval x)).isLt.le hps hcover
  rw [primesPhiNet,totientFromList_value hn,List.map_flatten,List.map_replicate,
    totientScan_exact _ _ (Nat.pos_of_ne_zero hm) (by
      intro p hp'
      obtain ⟨qs,hqs,hp'⟩:=List.mem_flatten.mp hp'
      have he:=(List.mem_replicate.mp hqs).2
      subst qs
      exact hps p hp') (by
      rw [List.prod_flatten,List.map_replicate,List.prod_replicate]
      exact hd)]
  exact Nat.mod_eq_of_lt ((Nat.totient_le _).trans_lt (bitsValue (m.eval x)).isLt)

lemma primesPhiNet_count {k n c : ℕ} (m : BooleanNetwork k n)
    (ps : List (BooleanNetwork k n)) (hm : m.net.count≤c) (hp : ∀ p∈ps,p.net.count≤c) :
    (primesPhiNet m ps).net.count≤c+n+(n*ps.length)*totientStepBound n c := by
  have hh:=totientFromList_count m (List.flatten (List.replicate n ps)) (c:=c) (by
    intro p hp'
    obtain ⟨qs,hqs,hp'⟩:=List.mem_flatten.mp hp'
    have he:=(List.mem_replicate.mp hqs).2
    subst qs
    exact hp p hp')
  simp only [List.length_flatten,List.map_replicate,List.sum_replicate,smul_eq_mul] at hh
  exact hh.trans (by omega)
end BitArithmetic
end ExactQuantumFactoring


end

end OAI
