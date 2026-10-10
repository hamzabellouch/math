import Mathlib
import OAI.Computability.QuantumFactoring.CyclicAlgebra
import OAI.Computability.QuantumFactoring.ModularMultiply
import OAI.Computability.QuantumFactoring.WordBlocks

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring.BitArithmetic
open BooleanNetwork Primality
open scoped BigOperators

noncomputable def decodeCyclic {s w : ℕ} (m : ℕ) (x : Basis (s*w)) : Cyclic (ZMod m) s :=
  cyclicOf (fun i => ((bitsValue (block x i)).toNat : ZMod m))

@[simp] lemma decodeCyclic_coeff {s w : ℕ} (m : ℕ) (x : Basis (s*w)) (i : Fin s) :
    (decodeCyclic m x).coeff i=((bitsValue (block x i)).toNat : ZMod m) := rfl

def cyclicTerm {n s w : ℕ} [NeZero s] (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (k i : Fin s) : BooleanNetwork n w :=
  mulMod (a.comp (blockNet s w i)) (b.comp (blockNet s w (k-i))) m

def cyclicMulNet {n s w : ℕ} [NeZero s] (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) : BooleanNetwork n (s*w) :=
  wordBlocks (fun k => sumMod m (List.ofFn (cyclicTerm a b m k)))

lemma cyclicMulNet_value {n s w : ℕ} [NeZero s] (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (x : Basis n) (hm : 0 < (bitsValue (m.eval x)).toNat)
    (k : Fin s) :
    (bitsValue (block ((cyclicMulNet a b m).eval x) k)).toNat =
      (∑ i : Fin s, (bitsValue (block (a.eval x) i)).toNat *
        (bitsValue (block (b.eval x) (k-i))).toNat) % (bitsValue (m.eval x)).toNat := by
  rw [cyclicMulNet,wordBlocks_eval,sumMod_value _ _ _ hm]
  simp only [List.map_ofFn,List.sum_ofFn]
  have hh : ∀ i : Fin s, (bitsValue ((cyclicTerm a b m k i).eval x)).toNat =
      ((bitsValue (block (a.eval x) i)).toNat *
        (bitsValue (block (b.eval x) (k-i))).toNat) % (bitsValue (m.eval x)).toNat := by
    intro i
    rw [cyclicTerm,mulMod_word _ _ _ _ hm]
    simp only [eval_comp,blockNet_eval]
  simp only [Function.comp_apply]
  simp_rw [hh]
  exact (Finset.sum_nat_mod _ _ _).symm

lemma cyclicMulNet_correct {n s w : ℕ} [NeZero s] (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (x : Basis n) (hm : 0 < (bitsValue (m.eval x)).toNat) :
    decodeCyclic (bitsValue (m.eval x)).toNat ((cyclicMulNet a b m).eval x) =
      decodeCyclic (bitsValue (m.eval x)).toNat (a.eval x)*
        decodeCyclic (bitsValue (m.eval x)).toNat (b.eval x) := by
  ext k
  rw [decodeCyclic_coeff,cyclicMulNet_value _ _ _ _ hm,cyclic_mul_coeff]
  simp only [ZMod.natCast_mod,Nat.cast_sum,Nat.cast_mul,decodeCyclic_coeff]

abbrev cyclicMulBound (s w ac bc mc : ℕ) : ℕ :=
  s*w*(w+s*(ac+bc+2*mc+(1224*w*w+143*w+12)+216*(w+1)^2+142*(w+1)+15))

lemma cyclicTerm_count {n s w : ℕ} [NeZero s] (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (k i : Fin s) :
    (cyclicTerm a b m k i).net.count ≤ a.net.count+b.net.count+m.net.count+
      (1224*w*w+143*w+12) := by
  have h := mulMod_count (a.comp (blockNet s w i)) (b.comp (blockNet s w (k-i))) m
  simpa only [cyclicTerm,count_comp,blockNet_count,add_zero] using h

lemma cyclicMulNet_count {n s w : ℕ} [NeZero s] (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) : (cyclicMulNet a b m).net.count ≤
      cyclicMulBound s w a.net.count b.net.count m.net.count := by
  apply wordBlocks_count
  intro k
  have h := sumMod_count m (List.ofFn (cyclicTerm a b m k)) (by
    intro c hc
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
    exact cyclicTerm_count a b m k i)
  simp only [List.length_ofFn] at h
  
  nlinarith

/-- Canonical representatives permit exact word comparison of arrays. -/
def CanonicalCyclic {s w : ℕ} (m : ℕ) (x : Basis (s*w)) : Prop :=
  ∀ i : Fin s, (bitsValue (block x i)).toNat < m

lemma cyclicMulNet_canonical {n s w : ℕ} [NeZero s] (a b : BooleanNetwork n (s*w))
    (m : BooleanNetwork n w) (x : Basis n) (hm : 0 < (bitsValue (m.eval x)).toNat) :
    CanonicalCyclic (bitsValue (m.eval x)).toNat ((cyclicMulNet a b m).eval x) := by
  intro k
  rw [cyclicMulNet_value _ _ _ _ hm]
  exact Nat.mod_lt _ hm

lemma decodeCyclic_injective {s w m : ℕ} (hm : 0 < m) {a b : Basis (s*w)}
    (ha : CanonicalCyclic m a) (hb : CanonicalCyclic m b)
    (hh : decodeCyclic m a=decodeCyclic m b) : a=b := by
  let : NeZero m := ⟨by omega⟩
  have hv : ∀ i : Fin s, bitsValue (block a i)=bitsValue (block b i) := by
    intro i
    have he := congrArg (fun c : Cyclic (ZMod m) s => (c.coeff i).val) hh
    simp only [decodeCyclic_coeff,ZMod.val_natCast,Nat.mod_eq_of_lt (ha i),
      Nat.mod_eq_of_lt (hb i)] at he
    exact BitVec.eq_of_toNat_eq he
  funext k
  obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective k
  have he := congrArg (fun v : BitVec w => v.getLsbD j.val) (hv i)
  simpa only [bitsValue_bit,block] using he

end ExactQuantumFactoring.BitArithmetic


end

end OAI
