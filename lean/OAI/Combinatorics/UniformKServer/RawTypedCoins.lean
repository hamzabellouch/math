import Mathlib
import OAI.Combinatorics.UniformKServer.RawFinite

namespace OAI

noncomputable section

namespace UniformKServer.RawFinite
open RawProgram RawCertificate
open scoped Classical

 theorem choose_token {n k : ℕ} (hk : 0<k) (v : Certificate)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true)
    (s : TapeController.State n k (cap v) (restart v) (bits v)) (r : Fin n)
    (bs : TapeController.Tape k (cap v) (bits v)) :
    RawProgram.chosen (repr v s) (requestToken r.val) (BinaryTape.token bs)=
      (TapeController.choose hk (RawRows.complete hk (UniformKServer.horizon k (cap v)) (bits v) (table v))
        (RawRows.total hk hT) s r bs).val := by
  simp only [RawProgram.chosen,repr,payload,requestToken,request_code,BinaryTape.fresh_token]
  exact RawGlobal.label_state hk (table v) hT s r bs

 theorem next_token {n k : ℕ} (hk : 0<k) (hkn : k≤n) (v : Certificate) (hR : 0<restart v)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true)
    (s : TapeController.State n k (cap v) (restart v) (bits v)) (r : Fin n)
    (bs : TapeController.Tape k (cap v) (bits v)) :
    RawProgram.next (repr v s) (requestToken r.val) (BinaryTape.token bs)=
      repr v (TapeController.step hk hR (fun j : Fin k=>⟨j.val,lt_of_lt_of_le j.isLt hkn⟩)
        (RawRows.complete hk (UniformKServer.horizon k (cap v)) (bits v) (table v))
        (RawRows.total hk hT) s r bs) := by
  simp only [RawProgram.next,repr,payload,requestToken,request_code,BinaryTape.fresh_token]
  rw [RawGlobal.step_state hk hkn hR (table v) hT]

 theorem initial_repr {n k : ℕ} (hkn : k≤n) (v : Certificate) (hR : 0<restart v) :
    RawProgram.initial n k v=repr v (TapeController.initial (M:=cap v) (b:=bits v) hR
      (fun j : Fin k=>⟨j.val,lt_of_lt_of_le j.isLt hkn⟩)) := by
  unfold RawProgram.initial repr
  rw [RawGlobal.initial_state hkn hR]

end UniformKServer.RawFinite

end

end OAI
