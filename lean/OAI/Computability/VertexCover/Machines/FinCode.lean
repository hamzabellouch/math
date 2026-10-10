import Mathlib
import OAI.Computability.VertexCover.Machines.NatDiv

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                            
section

namespace VertexCover.Machine

def finCode {n : ℕ} (i : Fin n) : List Bool := natBits i.val

theorem finCode_injective (n : ℕ) : Function.Injective (finCode (n := n)) := by
  intro a b h
  apply Fin.ext
  have := congrArg List.length h
  simpa [finCode] using this

noncomputable def Poly.finMod (n : ℕ) (hn : 0 < n) :
    Poly natBits (finCode (n := n)) (fun i => (⟨i%n,Nat.mod_lt i hn⟩ : Fin n)) :=
  (((Poly.identity natBits).pair (Poly.const natBits natBits n)).comp Poly.natMod).encodeCongr
    id (fun _ => rfl) (fun _ => rfl)

noncomputable def Poly.finVal (n : ℕ) : Poly (finCode (n := n)) natBits Fin.val :=
  (Poly.identity natBits).encodeCongr Fin.val (fun _ => rfl) (fun _ => rfl)

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
