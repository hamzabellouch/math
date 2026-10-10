import Mathlib
import OAI.Combinatorics.UniformKServer.WrapperTyped
import OAI.Combinatorics.UniformKServer.WrapperSlow

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open TypedStack RawCertificate
open scoped Classical

abbrev CoreState (mult : ℕ) :=
  State (Fintype.card (FlatTM2.Local Turing.PartrecToTM2.tr (LiteralPartrec.supp (ConstructorProgram.code mult))))
    (Fintype.card (FlatTM2.Local Turing.PartrecToTM2.tr (LiteralPartrec.supp LiteralVector.activeCode)))

def Live {n k : ℕ} (mult : ℕ) (v : Certificate) (c : RuntimeCertificate.Cert)
    (delay : ℕ) (f : ℕ → CoreState mult) (t : ℕ) (z : MachineState (machine mult)) : Prop :=
  (t<delay ∧ CoreRep (uniform mult) (f t) z) ∨
    (delay≤t ∧ ∃a : TC n k v,represents mult v c a z)

 theorem live_initial {n k : ℕ} (mult : ℕ) (v : Certificate) (c : RuntimeCertificate.Cert)
    (delay : ℕ) (hd : 2^c.2≤delay) (f : ℕ → CoreState mult)
    (z : MachineState (machine mult)) (hz : CoreRep (uniform mult) (f 0) z) :
    Live (n:=n) (k:=k) mult v c delay f 0 z := by
  left
  exact ⟨lt_of_lt_of_le (Nat.pow_pos (by decide)) hd,hz⟩

 theorem live_next {n k : ℕ} (mult L : ℕ) (hk : 0<k) (hkn : k≤n)
    (v : Certificate) (hR : 0<restart v)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true)
    (c : RuntimeCertificate.Cert) (hc : RuntimeCertificate.verify n k v c=true)
    (delay : ℕ) (hd : 2^c.2≤delay) (a : CoreState mult)
    (p : Prefix (uniform mult) a (ready (RuntimeCertificate.B k v)
      (Encodable.encode (RawProgram.initial n k v)) BitTape.blank [] true) delay)
    (t : ℕ) (z : MachineState (machine mult)) (hz : Live (n:=n) (k:=k) mult v c delay p.state t z)
    (r : Fin n) (coins : Fin (requestBudget 64 1 L (t+1))→Bool) :
    let z':=requestStep (machine mult) 64 1 L (t+1) z r coins
    Live (n:=n) (k:=k) mult v c delay p.state (t+1) z' ∧ z'.yielded=true ∧ outputValue z'<k := by
  dsimp only
  rcases hz with ⟨ht,hz⟩|⟨ht,b,hz⟩
  · have hh:=slow_request mult L t hk _ _ (p.next t ht) z hz r coins
    dsimp only at hh
    refine ⟨?_,hh.2.2⟩
    by_cases ht' : t+1<delay
    · exact Or.inl ⟨ht',hh.1⟩
    · have he : t+1=delay:=by omega
      have hh':=hh.1
      have hstate : p.state (t+1)=ready (RuntimeCertificate.B k v)
          (Encodable.encode (RawProgram.initial n k v)) BitTape.blank [] true :=
        (congrArg p.state he).trans p.finish
      rw [hstate] at hh'
      exact Or.inr ⟨by omega,tcInitial hkn v hR,initial_represents mult hkn v hR c hc _ hh'⟩
  · have hh:=typed_step mult L t hk hkn v hR hT c hc b z hz (process_bound L t c.2 delay hd ht) r coins
    dsimp only at hh
    exact ⟨Or.inr ⟨by omega,_,hh.1⟩,hh.2.2⟩

 theorem all_reachable {n k : ℕ} (mult : ℕ) (hk : 0<k) (hkn : k≤n)
    (v : Certificate) (hR : 0<restart v)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true)
    (c : RuntimeCertificate.Cert) (hc : RuntimeCertificate.verify n k v c=true)
    (delay : ℕ) (hd : 2^c.2≤delay) (a : CoreState mult)
    (p : Prefix (uniform mult) a (ready (RuntimeCertificate.B k v)
      (Encodable.encode (RawProgram.initial n k v)) BitTape.blank [] true) delay)
    (d : RationalMetric n) (s : Configuration n k)
    (hb : CoreRep (uniform mult) a (boot (machine mult) 64 1 d s))
    (t : ℕ) (z : MachineState (machine mult)) (hz : Reachable (machine mult) 64 1 d s t z) :
    Live (n:=n) (k:=k) mult v c delay p.state t z := by
  induction hz with
  | boot=>
    apply live_initial mult v c delay hd p.state
    rw [p.start]
    exact hb
  | @next t z hz r coins ih=>
    exact (live_next mult (instanceCode d s).length hk hkn v hR hT c hc delay hd a p t z ih r coins).1

end UniformKServer.UniformWrapper

end

end OAI
