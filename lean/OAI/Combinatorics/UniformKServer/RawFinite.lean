import Mathlib
import OAI.Combinatorics.UniformKServer.BinaryTape

namespace OAI

noncomputable section

namespace UniformKServer.RawFinite
open RawProgram RawCertificate
open scoped Classical

def requestToken (r : ℕ) : ℕ := RawBinary.value (natCode (r+1)++[true])
def repr {n k : ℕ} (v : Certificate)
    (s : TapeController.State n k (cap v) (restart v) (bits v)) : Payload :=
  payload n k v (RawGlobal.state s)

 theorem choose_repr {n k : ℕ} (hk : 0<k) (v : Certificate)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true)
    (s : TapeController.State n k (cap v) (restart v) (bits v)) (r : Fin n) (a : ℕ) :
    RawProgram.chosen (repr v s) (requestToken r.val) a=
      (TapeController.choose hk (RawRows.complete hk (UniformKServer.horizon k (cap v)) (bits v) (table v))
        (RawRows.total hk hT) s r (BinaryTape.coins k (cap v) (bits v) a)).val := by
  simp only [RawProgram.chosen,repr,payload,requestToken,request_code,BinaryTape.fresh_eq]
  exact RawGlobal.label_state hk (table v) hT s r _

 theorem next_repr {n k : ℕ} (hk : 0<k) (hkn : k≤n) (v : Certificate) (hR : 0<restart v)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true)
    (s : TapeController.State n k (cap v) (restart v) (bits v)) (r : Fin n) (a : ℕ) :
    RawProgram.next (repr v s) (requestToken r.val) a=
      repr v (TapeController.step hk hR (fun j : Fin k=>⟨j.val,lt_of_lt_of_le j.isLt hkn⟩)
        (RawRows.complete hk (UniformKServer.horizon k (cap v)) (bits v) (table v))
        (RawRows.total hk hT) s r (BinaryTape.coins k (cap v) (bits v) a)) := by
  simp only [RawProgram.next,repr,payload,requestToken,request_code,BinaryTape.fresh_eq]
  rw [RawGlobal.step_state hk hkn hR (table v) hT]

 theorem finite_closed {n k : ℕ} (hk : 0<k) (hkn : k≤n) (v : Certificate) (hR : 0<restart v)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true) :
    ∃S : List ℕ, Encodable.encode (RawProgram.initial n k v)∈S ∧
      ∀u∈S,∀r<n,∀a : ℕ,
        RawProgram.chosen (unpack u) (requestToken r) a<k ∧
        Encodable.encode (RawProgram.next (unpack u) (requestToken r) a)∈S := by
  let State:=TapeController.State n k (cap v) (restart v) (bits v)
  let : Fintype State:=Fintype.ofFinite _
  let S : Finset ℕ:=Finset.univ.image (fun s : State=>Encodable.encode (repr v s))
  have hm (s : State) : Encodable.encode (repr v s)∈S := Finset.mem_image.mpr ⟨s,Finset.mem_univ _,rfl⟩
  refine ⟨S.toList,?_,?_⟩
  · rw [Finset.mem_toList]
    convert hm (TapeController.initial hR (fun j : Fin k=>⟨j.val,lt_of_lt_of_le j.isLt hkn⟩)) using 1
    exact congrArg (fun x=>Encodable.encode (payload n k v x))
      (RawGlobal.initial_state (M:=cap v) (b:=bits v) hkn hR)
  · intro u hu r hr a
    rw [Finset.mem_toList] at hu
    obtain ⟨s,hs,rfl⟩:=Finset.mem_image.mp hu
    simp only [unpack_encode]
    rw [choose_repr hk v hT s (⟨r,hr⟩ : Fin n) a,
      next_repr hk hkn v hR hT s (⟨r,hr⟩ : Fin n) a]
    exact ⟨Fin.isLt _,Finset.mem_toList.mpr (hm _)⟩

end UniformKServer.RawFinite

end

end OAI
