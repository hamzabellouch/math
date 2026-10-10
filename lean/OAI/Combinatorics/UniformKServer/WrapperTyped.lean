import Mathlib
import OAI.Combinatorics.UniformKServer.WrapperActive
import OAI.Combinatorics.UniformKServer.WrapperCoins
import OAI.Combinatorics.UniformKServer.RawTypedCoins

namespace OAI

noncomputable section

namespace UniformKServer.UniformWrapper
open TypedStack RawCertificate
open scoped Classical

abbrev TC (n k : ℕ) (v : Certificate) := TapeController.State n k (cap v) (restart v) (bits v)
abbrev tcRows {n k : ℕ} (hk : 0<k) (v : Certificate) :=
  RawRows.complete (n:=n) hk (UniformKServer.horizon k (cap v)) (bits v) (table v)
abbrev tcN {n k : ℕ} (hk : 0<k) (v : Certificate)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true) := RawRows.total hk hT
abbrev tcInitial {n k : ℕ} (hkn : k≤n) (v : Certificate) (hR : 0<restart v) : TC n k v :=
  TapeController.initial hR (fun j : Fin k=>⟨j.val,lt_of_lt_of_le j.isLt hkn⟩)
abbrev tcLabel {n k : ℕ} (hk : 0<k) (v : Certificate)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true)
    (s : TC n k v) (r : Fin n) (bs : TapeController.Tape k (cap v) (bits v)) :=
  TapeController.choose hk (tcRows hk v) (tcN hk v hT) s r bs
abbrev tcNext {n k : ℕ} (hk : 0<k) (hkn : k≤n) (v : Certificate) (hR : 0<restart v)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true)
    (s : TC n k v) (r : Fin n) (bs : TapeController.Tape k (cap v) (bits v)) : TC n k v :=
  TapeController.step hk hR (fun j : Fin k=>⟨j.val,lt_of_lt_of_le j.isLt hkn⟩)
    (tcRows hk v) (tcN hk v hT) s r bs

def represents {n k : ℕ} (mult : ℕ) (v : Certificate) (c : RuntimeCertificate.Cert)
    (s : TC n k v) (z : MachineState (machine mult)) : Prop :=
  Encodable.encode (RawFinite.repr v s)∈c.1 ∧
    CoreRep (uniform mult)
      (ready (RuntimeCertificate.B k v) (Encodable.encode (RawFinite.repr v s)) BitTape.blank [] true) z

 theorem sample_bound (L t n k : ℕ) (v : Certificate) (c : RuntimeCertificate.Cert)
    (hc : RuntimeCertificate.verify n k v c=true)
    (ht : 16*(c.2+1)≤32*(L+Nat.clog 2 (t+2)+1)) :
    2*(UniformKServer.horizon k (cap v)*bits v)≤requestBudget 64 1 L (t+1) := by
  have hb:=((RuntimeCertificate.verify_iff n k v c).mp hc).2.1
  unfold RuntimeCertificate.B at hb
  rw [RawMetric.horizon_eq] at hb
  simp only [requestBudget,polynomialBudget,pow_one]
  rw [show t+1+1=t+2 by omega]
  omega

 theorem typed_step {n k : ℕ} (mult L t : ℕ) (hk : 0<k) (hkn : k≤n)
    (v : Certificate) (hR : 0<restart v)
    (hT : rowsOK n k (UniformKServer.horizon k (cap v)) (bits v) (table v)=true)
    (c : RuntimeCertificate.Cert) (hc : RuntimeCertificate.verify n k v c=true)
    (s : TC n k v) (z : MachineState (machine mult)) (hz : represents mult v c s z)
    (ht : 16*(c.2+1)≤32*(L+Nat.clog 2 (t+2)+1))
    (r : Fin n) (coins : Fin (requestBudget 64 1 L (t+1))→Bool) :
    let bs:=tapeCoins (sample_bound L t n k v c hc ht) coins
    let z':=requestStep (machine mult) 64 1 L (t+1) z r coins
    represents mult v c (tcNext hk hkn v hR hT s r bs) z' ∧
      selectedLabel hk z'=tcLabel hk v hT s r bs ∧ z'.yielded=true ∧ outputValue z'<k := by
  dsimp only
  let bs:=tapeCoins (sample_bound L t n k v c hc ht) coins
  have ha : RawBinary.value ((StackCompiler.alternate (List.ofFn coins)).take (RuntimeCertificate.B k v)++[true])=
      BinaryTape.token bs := by
    unfold BinaryTape.token
    rw [tapeCoins_word,RuntimeCertificate.B,RawMetric.horizon_eq]
  have hh:=physical_active mult L t n k v c hc (Encodable.encode (RawFinite.repr v s)) hz.1
    (by rw [RawProgram.unpack_encode];rfl) z hz.2 ht r coins
  dsimp only at hh
  rw [RawProgram.unpack_encode,ha,RawFinite.next_token hk hkn v hR hT s r bs,
    RawFinite.choose_token hk v hT s r bs] at hh
  refine ⟨⟨hh.2.1,hh.1⟩,?_,hh.1.yielded,hh.2.2.2⟩
  apply Fin.ext
  change outputValue _ % k=(tcLabel hk v hT s r bs).val
  rw [hh.2.2.1,Nat.mod_eq_of_lt (Fin.isLt _)]

 theorem initial_represents {n k : ℕ} (mult : ℕ) (hkn : k≤n) (v : Certificate) (hR : 0<restart v)
    (c : RuntimeCertificate.Cert) (hc : RuntimeCertificate.verify n k v c=true)
    (z : MachineState (machine mult))
    (hz : CoreRep (uniform mult) (ready (RuntimeCertificate.B k v)
      (Encodable.encode (RawProgram.initial n k v)) BitTape.blank [] true) z) :
    represents mult v c (tcInitial hkn v hR) z := by
  have hh:=((RuntimeCertificate.verify_iff n k v c).mp hc).1
  rw [RawFinite.initial_repr hkn v hR] at hh hz
  exact ⟨hh,hz⟩

end UniformKServer.UniformWrapper

end

end OAI
