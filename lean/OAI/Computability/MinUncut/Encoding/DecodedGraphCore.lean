import Mathlib
import OAI.Computability.MinUncut.Machines.FiberGraphMachine

namespace OAI

section
noncomputable section
namespace MinUncut.Costed.Arena
open _root_.Turing _root_.OAI.Turing Turing.ToPartrec _root_.Turing.PartrecToTM2 _root_.OAI.Turing.PartrecToTM2 Polynomial
open MinUncutGames.Foundations.Complexity MinUncutGames.BinaryEncoding

def decodedMachine (c : Code) : FinTM2 :=
  MachineSequential.machine FrameDecode.machine (initializedGraphMachine c) id .cons
lemma decodedMachine_finite (c : Code) (k : (decodedMachine c).K) :
    Finite ((decodedMachine c).Γ k) :=
  sequential_finiteAlphabet _ _ _ _ FrameDecode.finiteAlphabet (initializedGraphMachine_finite _) k

def decoded_outputs (c : Code) (K : ℕ) (v out : List Bool) (B : ℕ)
    (hr : TM2OutputsInTime (initializedGraphMachine c)
      (trList (K::v.map FrameDecode.symbol)) (some out) B) :
    TM2OutputsInTime (decodedMachine c) (nameBits K++v) (some out)
      (B+2*(nameBits K).length+3*(K+1)+4+11*v.length) := by
  let w:=trList (K::v.map FrameDecode.symbol)
  let h1:=FrameDecode.outputs K v
  let h2:TM2OutputsInTime (initializedGraphMachine c) (w.map id) (some out) B:=by
    have input_eq : @List.map ((initializedGraphMachine c).Γ (initializedGraphMachine c).k₀)
        ((initializedGraphMachine c).Γ (initializedGraphMachine c).k₀) id w = w := List.map_id _
    simpa only [input_eq] using hr
  have hh:=MachineSequential.execute FrameDecode.machine (initializedGraphMachine c)
    id Γ'.cons _ _ _ _ _ h1 h2
  have hv:=FrameDecode.magnitude_symbols v
  have hw:w.length≤K+1+3*v.length:=by
    have h:=(bitsize_le_magnitude (K::v.map FrameDecode.symbol))
    simp only [magnitude_cons] at h
    exact h.trans (by omega)
  refine ⟨hh.toEvalsTo,hh.steps_le_m.trans ?_⟩
  change 2*(nameBits K++v).length+w.length+2+2*(w.length+1)+B≤_
  simp only [List.length_append]
  omega
end MinUncut.Costed.Arena

end
end

end OAI
