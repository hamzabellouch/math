import Mathlib
import OAI.Computability.QuantumFactoring.BooleanNetwork
import OAI.Computability.QuantumFactoring.PolyBounds

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork

def NetworkPoly {a b : ℕ→ℕ} (f : ∀ n,BooleanNetwork (a n) (b n)) : Prop :=
  PolyBound (fun n=>(f n).net.count)

def NetworkVarsPoly {v : ℕ→Type*} {a b : ℕ→ℕ}
    (f : ∀ n,v n→BooleanNetwork (a n) (b n)) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n i,(f n i).net.count≤p.eval n


end ExactQuantumFactoring
end

end OAI
