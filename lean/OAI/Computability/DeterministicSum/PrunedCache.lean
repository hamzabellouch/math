import Mathlib
import OAI.Computability.DeterministicSum.CacheRows
import OAI.Computability.DeterministicSum.PrunedProgram

namespace OAI

/-! Paid prefix-key setup and complete sparse cache production. -/

namespace DeterministicThreeSum.Structured.Indexed.Cache
open Command DeterministicThreeSum.Pruned

def seedKeys : Command := straight [
  .assign 0 (.literal 0), .assign 1 (.literal 1), .assign 6 (.literal 0),
  .store (.register 4) (.literal 0),
  .binary 13 .add (.register 4) (.literal 1), .store (.register 13) (.literal 0)]

def seeded (s : Data) (Q : ℕ) : Data :=
  put (put (put (put (Pruned.storePair s Q 0 (0,0)) 0 0) 1 1) 6 0) 13 (Q+1)

lemma seedKeys_correct {w Q : ℕ} (s : Data) (hQ : Q+1 < wordModulus w)
    (h4 : s.registers 4=Q) : Eval w seedKeys s 6 (seeded s Q) := by
  apply straight_correct
  have hW : 1 < wordModulus w := by omega
  simp [seeded,execStraight,Atom.eval,operand_literal,operand_register,evalBinOp,
    put,Pruned.storePair,h4,Nat.mod_eq_of_lt hQ,Nat.mod_eq_of_lt (by omega : Q < wordModulus w),
    Nat.mod_eq_of_lt hW,Function.update_comm (show (0:ℕ)≠1 by decide),Nat.zero_mod]

lemma seeded_stored (s : Data) (Q : ℕ) : Pruned.Stored (seeded s Q) Q [(0,0)] := by
  change Pruned.Stored (Pruned.storePair s Q 0 (0,0)) Q ([]++[(0,0)])
  exact Pruned.storePair_stored s Q [] (0,0) (Pruned.stored_nil s Q)

lemma seeded_regs {s : Data} {D P Q d : ℕ}
    (h2 : s.registers 2=D) (h3 : s.registers 3=P)
    (h4 : s.registers 4=Q) (h5 : s.registers 5=d) :
    Pruned.LevelRegs (seeded s Q) D P Q d 1 := by
  simp [Pruned.LevelRegs,seeded,put,Pruned.storePair,h2,h3,h4,h5]

lemma seeded_frame (s : Data) (Q k r : ℕ) (hk : 26 ≤ k) :
    (seeded s Q).registers (k+r)=s.registers (k+r) := by
  simp only [seeded,put,Function.update_of_ne (show k+r≠13 by omega),
    Function.update_of_ne (show k+r≠6 by omega),Function.update_of_ne (show k+r≠1 by omega),
    Function.update_of_ne (show k+r≠0 by omega),Pruned.storePair]

def keysHandoff (k : ℕ) : Command := straight [
  .assign k (.literal 0), .assign (k+1) (.register 1), .assign (k+2) (.register 4)]

def keyHanded (s : Data) (k rows nodes : ℕ) : Data :=
  put (put (put s k 0) (k+1) rows) (k+2) nodes

lemma keysHandoff_correct {w k rows nodes : ℕ} (s : Data) (hk : 26 ≤ k)
    (hrows : rows < wordModulus w) (hnodes : nodes < wordModulus w)
    (h1 : s.registers 1=rows) (h4 : s.registers 4=nodes) :
    Eval w (keysHandoff k) s 3 (keyHanded s k rows nodes) := by
  apply straight_correct
  simp [keyHanded,execStraight,Atom.eval,operand_literal,operand_register,put,
    show (1:ℕ)≠k by omega,show (4:ℕ)≠k by omega,show (4:ℕ)≠k+1 by omega,
    h1,h4,Nat.mod_eq_of_lt hrows,Nat.mod_eq_of_lt hnodes]

def prunedKeys (r k : ℕ) : Command :=
  .seq seedKeys (.seq (Pruned.levelsCommand (scalarAlphabet r)) (keysHandoff k))

theorem prunedKeys_correct {w r D K P Q d k : ℕ} (s : Data)
    (hW : 2 < wordModulus w) (hr : 0 < r) (hrw : r < wordModulus w)
    (hD : D+r < wordModulus w) (hd : d < wordModulus w) (hk : 26 ≤ k)
    (hP : P+2*K*r+1 < wordModulus w) (hQ : Q+2*K*r+1 < wordModulus w)
    (hdis : P+2*K*r ≤ Q ∨ Q+2*K*r ≤ P)
    (hK : (enumerate D (List.replicate d (scalarAlphabet r))).length ≤ K)
    (hvol : r^d*r < wordModulus w)
    (h2 : s.registers 2=D) (h3 : s.registers 3=P)
    (h4 : s.registers 4=Q) (h5 : s.registers 5=d) :
    ∃ cost z, Eval w (prunedKeys r k) s cost z ∧
      cost ≤ d*((11*r+8)*K+10)+10 ∧
      let nodes:=(Pruned.banks d P Q).2
      let l:=enumerate D (List.replicate d (scalarAlphabet r))
      Pruned.Stored z nodes l ∧ z.registers k=0 ∧ z.registers (k+1)=l.length ∧
      z.registers (k+2)=nodes ∧
      (∀ j, 3 ≤ j → z.registers (k+j)=s.registers (k+j)) ∧
      (∀ a, (a < P ∨ P+2*K*r ≤ a) → (a < Q ∨ Q+2*K*r ≤ a) → z.memory a=s.memory a) := by
  have es:=seedKeys_correct (w:=w) s (by omega) h4
  obtain ⟨c,u,eu,hc,hur,hum,huf⟩:=Pruned.levelsEnumerate_correct (rest:=[]) (W:=r)
    (scalarAlphabet r) (seeded s Q) hW hr hrw rfl (by intro v hv; exact hv.le)
    (by simp) hD hd hP hQ hdis (by simpa only [List.append_nil] using hK)
    (by simpa only [List.append_nil,volume_replicate,scalarAlphabet] using hvol)
    (seeded_regs h2 h3 h4 h5) (seeded_stored s Q)
  simp only [List.append_nil] at hur hum
  let l:=enumerate D (List.replicate d (scalarAlphabet r))
  let nodes:=(Pruned.banks d P Q).2
  have hKpos : 0 < K := by
    have h:=length_enumerate_suffix D (List.replicate d (scalarAlphabet r)) []
      (by intro A hA; obtain ⟨_,rfl⟩:=List.mem_replicate.mp hA; exact hr)
      (by intro A hA; obtain ⟨_,rfl⟩:=List.mem_replicate.mp hA; rfl)
    simp only [List.append_nil,enumerate,List.length_singleton] at h
    omega
  have hKw : K < wordModulus w := by
    have hx : K ≤ 2*K*r := by nlinarith only [hr]
    omega
  have hnodes : nodes < wordModulus w := by
    dsimp [nodes,Pruned.banks]; split_ifs <;> dsimp <;> omega
  have eh:=keysHandoff_correct u hk (hK.trans_lt hKw) hnodes hur.2.1 hur.2.2.2.2.1
  simp only [scalarAlphabet] at hc
  refine ⟨6+(c+3),keyHanded u k l.length nodes,Eval.seq es (Eval.seq eu eh),by omega,?_,?_,?_,?_,?_,?_⟩
  · exact hum
  · simp [keyHanded,put,l,nodes]
  · simp [keyHanded,put,l,nodes]
  · simp [keyHanded,put,l,nodes]
  · intro j hj
    simp only [keyHanded,put,Function.update_of_ne (show k+j≠k+2 by omega),
      Function.update_of_ne (show k+j≠k+1 by omega),Function.update_of_ne (show k+j≠k by omega)]
    rw [register_frame eu (by
      intro hh
      have hh':=Pruned.levelsCommand_writes (scalarAlphabet r) hh
      simp only [Finset.mem_range] at hh'; omega)]
    exact seeded_frame s Q k j hk
  · intro a haP haQ
    change u.memory a=s.memory a
    rw [huf a haP haQ]
    change (Pruned.storePair s Q 0 (0,0)).memory a=s.memory a
    exact Pruned.storePair_outside s Q 0 (0,0) a (by
      have htwo : 2 ≤ 2*K*r := by nlinarith only [hKpos,hr]
      simp only [Nat.mul_zero,Nat.add_zero]
      omega)
end DeterministicThreeSum.Structured.Indexed.Cache
namespace DeterministicThreeSum.Structured.Indexed.Cache
open Command DeterministicThreeSum.Pruned Axis

def keyList (D r d : ℕ) : List Node := enumerate D (List.replicate d (scalarAlphabet r))
def keyAt (D r d j : ℕ) : ℕ := ((keyList D r d)[j]?.getD (0,0)).1

lemma keyAt_eq {D r d j : ℕ} (hj : j < (keyList D r d).length) :
    keyAt D r d j=(keyList D r d)[j].1 := by simp [keyAt,List.getElem?_eq_getElem hj]

lemma keyAt_bound {D r d j : ℕ} (hr : 0 < r) (hj : j < (keyList D r d).length) :
    keyAt D r d j < r^d := by
  rw [keyAt_eq hj]
  have h:= (enumerate_child D (List.replicate d (scalarAlphabet r))
    (by intro A hA; obtain ⟨_,rfl⟩:=List.mem_replicate.mp hA; exact hr) _).mp
    (List.getElem_mem hj)
  simpa only [volume_replicate,scalarAlphabet] using h.1

lemma keyAt_stored {s : Data} {P D r d j : ℕ} (hs : Pruned.Stored s P (keyList D r d))
    (hj : j < (keyList D r d).length) : s.memory (P+2*j)=some (keyAt D r d j) := by
  rw [keyAt_eq hj]; exact (hs j hj).1

lemma frame_interval {s t : Data} {P Q N A B : ℕ}
    (hf : ∀ a, (a < P ∨ P+N ≤ a) → (a < Q ∨ Q+N ≤ a) → t.memory a=s.memory a)
    (hP : P+N ≤ A ∨ A+B ≤ P) (hQ : Q+N ≤ A ∨ A+B ≤ Q)
    {i : ℕ} (hi : i < B) : t.memory (A+i)=s.memory (A+i) := by
  apply hf <;> omega

lemma keys_batch_regs {s t : Data} {tail : Bool} {m b q rows nodes dest S D H d T C P V : ℕ}
    (h0 : t.registers (batchBase tail m b q)=0)
    (h1 : t.registers (batchBase tail m b q+1)=rows)
    (h2 : t.registers (batchBase tail m b q+2)=nodes)
    (hf : ∀ j, 3 ≤ j → t.registers (batchBase tail m b q+j)=s.registers (batchBase tail m b q+j))
    (hs : ∀ r, 3 ≤ r → r < 16 → s.registers (batchBase tail m b q+r)=
      batchValues 0 rows nodes dest (q^d) S D H d (tensorStride q d) T C P V q r) :
    ∀ r, r < 16 → t.registers (batchBase tail m b q+r)=
      batchValues 0 rows nodes dest (q^d) S D H d (tensorStride q d) T C P V q r := by
  intro r hr
  by_cases h : 3 ≤ r
  · rw [hf r h,hs r h hr]
  · interval_cases r <;> simpa only [batchValues,Nat.add_zero] using (by assumption)
end DeterministicThreeSum.Structured.Indexed.Cache
namespace DeterministicThreeSum.Structured.Indexed.Cache
open Command DeterministicThreeSum.Pruned Axis

def prunedBatch (tail : Bool) (r m b q : ℕ) : Command :=
  .seq (prunedKeys r (batchBase tail m b q)) (batchCommand tail m b q)

theorem prunedBatch_correct {w T m b q d D H P S V C L nodes dest rows r Dkey K KP KQ : ℕ}
    (tail : Bool) (s : Data) (x c : ℕ → ℕ)
    (hrpos : 0 < r) (hrw : r < wordModulus w)
    (hDkey : Dkey+r < wordModulus w)
    (hKP : KP+2*K*r+1 < wordModulus w) (hKQ : KQ+2*K*r+1 < wordModulus w)
    (hKK : KP+2*K*r ≤ KQ ∨ KQ+2*K*r ≤ KP)
    (hK : (keyList Dkey r d).length ≤ K) (hkeyvol : r^d*r < wordModulus w)
    (hrowsEq : rows=(keyList Dkey r d).length) (hnodesEq : nodes=(Pruned.banks d KP KQ).2)
    (hKPS : KP+2*K*r ≤ S ∨ S+(m*b)^d ≤ KP)
    (hKQS : KQ+2*K*r ≤ S ∨ S+(m*b)^d ≤ KQ)
    (hKPC : KP+2*K*r ≤ C ∨ C+q*q ≤ KP)
    (hKQC : KQ+2*K*r ≤ C ∨ C+q*q ≤ KQ)
    (h2 : s.registers 2=Dkey) (h3 : s.registers 3=KP)
    (h4 : s.registers 4=KQ) (h5 : s.registers 5=d)
    (hm : 1  <  m) (hb : 1  <  b) (hq : 1  <  q) (hR : m*b < wordModulus w)
    (hT : 0 < T) (hadd : 2*T < wordModulus w) (hmul : T*T < wordModulus w)
    (hd : d < wordModulus w) (hD : D < wordModulus w) (hH : H < wordModulus w)
    (hvol : (m*b)^d < wordModulus w) (hsum : m^d+b^d < wordModulus w)
    (hL : q^d ≤ L) (hLw : L*q+L+3 < wordModulus w)
    (hP : P+L+1 < wordModulus w) (hV : V+L+1 < wordModulus w)
    (hS : S+(m*b)^d < wordModulus w) (hC : C+q*q < wordModulus w)
    (hSP : P+L ≤ S ∨ S+(m*b)^d ≤ P) (hSV : V+L ≤ S ∨ S+(m*b)^d ≤ V)
    (hVP : P+L ≤ V ∨ V+L ≤ P)
    (hCP : C+q*q ≤ P ∨ P+L ≤ C) (hCV : C+q*q ≤ V ∨ V+L ≤ C)
    (hrows : rows+1 < wordModulus w) (hnodes : nodes+2*rows < wordModulus w)
    (hdest : dest+rows*q^d+1 < wordModulus w)
    (hDP : P+L ≤ dest ∨ dest+rows*q^d ≤ P) (hDV : V+L ≤ dest ∨ dest+rows*q^d ≤ V)
    (hDS : dest+rows*q^d ≤ S ∨ S+(m*b)^d ≤ dest)
    (hDC : dest+rows*q^d ≤ C ∨ C+q*q ≤ dest)
    (hNP : P+L ≤ nodes ∨ nodes+2*rows ≤ P) (hNV : V+L ≤ nodes ∨ nodes+2*rows ≤ V)
    (hND : dest+rows*q^d ≤ nodes ∨ nodes+2*rows ≤ dest)
    (hl : ∀ j, j < rows → ∀ i, i < q^d → leftIndex tail (keyAt Dkey r d j) i < m^d)
    (hr : ∀ j, j < rows → ∀ i, i < q^d → rightIndex tail (keyAt Dkey r d j) i < b^d)
    (hxw : ∀ j, j < rows → ∀ i, i < q^d →
      x (ZipIndex.value m b d (leftIndex tail (keyAt Dkey r d j) i) (rightIndex tail (keyAt Dkey r d j) i)) < T)
    (hx : ∀ j, j < rows → ∀ i, i < q^d →
      DigitSum.value m d (leftIndex tail (keyAt Dkey r d j) i)+DigitSum.value b d (rightIndex tail (keyAt Dkey r d j) i) ≤ D →
      TailOK tail H (DigitSum.value b d (rightIndex tail (keyAt Dkey r d j) i)) →
      s.memory (S+ZipIndex.value m b d (leftIndex tail (keyAt Dkey r d j) i) (rightIndex tail (keyAt Dkey r d j) i))=
        some (x (ZipIndex.value m b d (leftIndex tail (keyAt Dkey r d j) i) (rightIndex tail (keyAt Dkey r d j) i))))
    (hc : ∀ i, i < q*q → s.memory (C+i)=some (c i) ∧ c i < T)
    (hregs : ∀ r, 3 ≤ r → r < 16 → s.registers (batchBase tail m b q+r)=
      batchValues 0 rows nodes dest (q^d) S D H d (tensorStride q d) T C P V q r) :
    ∃ cost z, Eval w (prunedBatch tail r m b q) s cost z ∧
      cost ≤ d*((11*r+8)*K+10)+10+(((14*d+27)*q^d+(((row q q).cost+5)*L+11)*d+49)*rows+1) ∧
      (∀ j, j < rows → ∀ v, v < q^d → z.memory (dest+j*q^d+v)=some
        (tensorValue T q q c d (gathered tail m b d D H (keyAt Dkey r d j) x) v)) ∧
      (∀ a, (a < P ∨ P+L ≤ a) → (a < V ∨ V+L ≤ a) →
        (a < dest ∨ dest+rows*q^d ≤ a) →
        (a < KP ∨ KP+2*K*r ≤ a) → (a < KQ ∨ KQ+2*K*r ≤ a) → z.memory a=s.memory a) ∧
      (∀ r, 3 ≤ r → z.registers (batchBase tail m b q+r)=s.registers (batchBase tail m b q+r)) := by
  have hkw : r^d < wordModulus w := by
    have hh : r^d ≤ r^d*r := Nat.le_mul_of_pos_right _ hrpos
    omega
  obtain ⟨a,t,et,ha,htm,ht0,ht1,ht2,htr,htf⟩:=prunedKeys_correct s
    (by omega) hrpos hrw hDkey hd (batchBase_ge ..) hKP hKQ hKK hK hkeyvol h2 h3 h4 h5
  have thregs : ∀ j, j < 16 → t.registers (batchBase tail m b q+j)=
      batchValues 0 rows nodes dest (q^d) S D H d (tensorStride q d) T C P V q j := by
    apply keys_batch_regs ht0
    · simpa only [hrowsEq,keyList] using ht1
    · simpa only [hnodesEq] using ht2
    · exact htr
    · exact hregs
  have thkeys : ∀ j, j < rows → keyAt Dkey r d j < wordModulus w := by
    intro j hj
    exact (keyAt_bound hrpos (by simpa only [←hrowsEq] using hj)).trans hkw
  have thmem : ∀ j, j < rows → t.memory (nodes+2*j)=some (keyAt Dkey r d j) := by
    intro j hj
    rw [hnodesEq]
    exact keyAt_stored htm (by simpa only [←hrowsEq] using hj)
  have thx : ∀ j, j < rows → ∀ i, i < q^d →
      DigitSum.value m d (leftIndex tail (keyAt Dkey r d j) i)+DigitSum.value b d (rightIndex tail (keyAt Dkey r d j) i) ≤ D →
      TailOK tail H (DigitSum.value b d (rightIndex tail (keyAt Dkey r d j) i)) →
      t.memory (S+ZipIndex.value m b d (leftIndex tail (keyAt Dkey r d j) i) (rightIndex tail (keyAt Dkey r d j) i))=
        some (x (ZipIndex.value m b d (leftIndex tail (keyAt Dkey r d j) i) (rightIndex tail (keyAt Dkey r d j) i))) := by
    intro j hj i hi hdeg htail
    rw [frame_interval htf hKPS hKQS (ZipIndex.value_lt (by omega) (by omega) d _ _)]
    exact hx j hj i hi hdeg htail
  have thc : ∀ i, i < q*q → t.memory (C+i)=some (c i) ∧ c i < T := by
    intro i hi
    rw [frame_interval htf hKPC hKQC hi]
    exact hc i hi
  obtain ⟨b,z,ez,hb,hzm,hzf,hzr⟩:=batchCommand_correct tail t x c (keyAt Dkey r d)
    hm hb hq hR hT hadd hmul hd hD hH hvol hsum hL hLw hP hV hS hC
    hSP hSV hVP hCP hCV hrows hnodes hdest hDP hDV hDS hDC hNP hNV hND
    thkeys thmem hl hr hxw thx thc thregs
  refine ⟨a+b,z,Eval.seq et ez,by omega,hzm,?_,?_⟩
  · intro addr hp hv hd hkp hkq
    rw [hzf addr hp hv hd,htf addr hkp hkq]
  · intro j hj
    exact (hzr j (by omega)).trans (htr j hj)
end DeterministicThreeSum.Structured.Indexed.Cache

end OAI
