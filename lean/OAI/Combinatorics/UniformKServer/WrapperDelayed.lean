import Mathlib
import OAI.Combinatorics.UniformKServer.WrapperExpectation
import OAI.Combinatorics.UniformKServer.WrapperSlow

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open TypedStack RawCertificate
open scoped Classical

 theorem prefix_expected {n k : ℕ} [NeZero k] (mult L : ℕ) (hkn : k≤n)
    (v : Certificate) (hR : 0<restart v)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true)
    (c : RuntimeCertificate.Cert) (hc : RuntimeCertificate.verify n k v c=true)
    (delay : ℕ) (hd : 2^c.2≤delay) (a : State _ _)
    (p : Prefix (uniform mult) a (ready (RuntimeCertificate.B k v)
      (Encodable.encode (RawProgram.initial n k v)) BitTape.blank [] true) delay)
    (d : RationalMetric n) (w : List (Fin n)) (t : ℕ) (ht : t≤delay)
    (z : MachineState (machine mult)) (hz : CoreRep (uniform mult) (p.state t) z)
    (s : Configuration n k) :
    machineExpectedCost (machine mult) 64 1 L d (NeZero.pos k) t z s w=
      costAlong d s (ComputedInstance.prefixTrace (w.take (delay-t)))+
        tcExpected (NeZero.pos k) hkn v hR hT d (tcInitial hkn v hR)
          (UniformKServer.finish s (ComputedInstance.prefixTrace (w.take (delay-t)))) (w.drop (delay-t)) := by
  induction w generalizing t z s with
  | nil=>simp only [machineExpectedCost,List.take_nil,List.drop_nil,ComputedInstance.prefixTrace,
      List.map_nil,costAlong,UniformKServer.finish,tcExpected,TapeController.expected,add_zero]
  | cons r w ih=>
    by_cases ht' : t=delay
    · subst t
      rw [p.finish] at hz
      have hh:=active_expected mult L (NeZero.pos k) hkn v hR hT c hc d (r::w) delay hd
        (tcInitial hkn v hR) z (initial_represents mult hkn v hR c hc z hz) s
      simpa only [Nat.sub_self,List.take_zero,ComputedInstance.prefixTrace,List.map_nil,costAlong,
        UniformKServer.finish,List.drop_zero,zero_add] using hh
    · have hl : t<delay:=by omega
      rw [machine_cons]
      have he : ∀coins : Fin (requestBudget 64 1 L (t+1))→Bool,
        let z':=requestStep (machine mult) 64 1 L (t+1) z r coins
        (d.distance (s (selectedLabel (NeZero.pos k) z')) r:ℝ)+
          machineExpectedCost (machine mult) 64 1 L d (NeZero.pos k) (t+1) z'
            (serve s r (selectedLabel (NeZero.pos k) z')) w=
        (d.distance (s ⟨0,NeZero.pos k⟩) r:ℝ)+
          costAlong d (serve s r ⟨0,NeZero.pos k⟩) (ComputedInstance.prefixTrace (w.take (delay-(t+1))))+
          tcExpected (NeZero.pos k) hkn v hR hT d (tcInitial hkn v hR)
            (UniformKServer.finish (serve s r ⟨0,NeZero.pos k⟩)
              (ComputedInstance.prefixTrace (w.take (delay-(t+1))))) (w.drop (delay-(t+1))) := by
        intro coins
        dsimp only
        have hh:=slow_request mult L t (NeZero.pos k) _ _ (p.next t hl) z hz r coins
        dsimp only at hh
        rw [hh.2.1,ih (t+1) (by omega) _ hh.1]
        ring
      simp_rw [he]
      rw [BitSampling.mean_const]
      rw [show delay-t=delay-(t+1)+1 by omega]
      simp only [List.take_succ_cons,List.drop_succ_cons,ComputedInstance.prefixTrace,List.map_cons,
        costAlong,UniformKServer.finish]

end UniformKServer.UniformWrapper

end

end OAI
