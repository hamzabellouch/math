import Mathlib
import OAI.Computability.QuantumFactoring.OrderSamplerMass
import OAI.Computability.QuantumFactoring.LabelRecoveryCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring.OrderTrial
open BooleanNetwork

def sampleY {w b : ℕ} (x : Basis (OrderSample.width w b)) : Basis b :=
  fun i => x (((Fin.natAdd (w+w) (Triangular.dataWire i)).castAdd w).castAdd (OrderSample.scratch w b))
def sampleU {w b : ℕ} (x : Basis (OrderSample.width w b)) : Basis w :=
  fun i => x ((Fin.natAdd (OrderSample.inputWidth w b) i).castAdd (OrderSample.scratch w b))

lemma sampleY_word {w b : ℕ} (a m u : Basis w) (y : Basis b) :
    sampleY (OrderSample.word a m y u)=y := by
  funext i
  change (OrderSample.word a m y u) _=y i
  exact (packed_input (OrderSample.inputWord a m y) u (Fin.natAdd (w+w) (Triangular.dataWire i))).trans
    (by simp only [OrderSample.inputWord,Fin.append_right,Triangular.encode_bit])
lemma sampleU_word {w b : ℕ} (a m u : Basis w) (y : Basis b) :
    sampleU (OrderSample.word a m y u)=u := by
  funext i
  exact packed_target _ _ i

/-- Selected phase block, with every workspace bit accounted for. The input
copies are compared to their retained read-only values. -/
def SampleSelected {w b : ℕ} (a m : Basis w) (x : Basis (OrderSample.width w b)) : Prop :=
  x=OrderSample.word a m (sampleY x) (sampleU x)

lemma sampleSelected_word {w b : ℕ} (a m u : Basis w) (y : Basis b) :
    SampleSelected a m (OrderSample.word a m y u) := by
  rw [SampleSelected,sampleY_word,sampleU_word]

lemma sampleY_number_injective (b : ℕ) : Function.Injective (@Triangular.outputNumber b) := by
  intro x y h
  apply (bitsEquiv b).injective
  apply BitVec.eq_of_toNat_eq
  change (bitsValue x).toNat=(bitsValue y).toNat
  simpa only [bitsValue_toNat,Triangular.outputNumber] using h

lemma natBasis_outputNumber (b k : ℕ) : Triangular.outputNumber (natBasis b k)=k%2^b := by
  rw [Triangular.outputNumber,← bitsValue_toNat,natBasis_value]

lemma scanPairs_eq_iff {s Q B k : ℕ} (hQ : B^2≤Q) (hsize : Q<2^s)
    {d j : ℕ} (hd : 0<d) (hdB : d<B) (hj : j<d) (hcop : Nat.Coprime j d) :
    scanPairs Q B k (2*s+1)=(d,j) ↔ bin Q d j=k := by
  constructor
  · intro h
    have hh : (scanPairs Q B k (2*s+1)).1≠0 := by rw [h]; omega
    have hs := scanPairs_sound hh
    rw [h] at hs
    exact hs.2.2.2.2
  · intro h
    exact scanPairs_complete hQ hsize ⟨hd,hdB,hj,hcop,h⟩

lemma selected_recovered_label {w b s B d j : ℕ} (a m : Basis w)
    (hB : B^2≤2^b) (hs : 2^b<2^s) (hd : 0<d) (hdB : d<B)
    (hj : j<d) (hcop : Nat.Coprime j d) :
    (fun x : Basis (OrderSample.width w b) => SampleSelected a m x ∧
      scanPairs (2^b) B (Triangular.outputNumber (sampleY x)) (2*s+1)=(d,j))=
    (fun x => x∈Set.range (OrderSample.word a m (natBasis b (bin (2^b) d j)))) := by
  funext x
  apply propext
  rw [scanPairs_eq_iff hB hs hd hdB hj hcop]
  have hdQ : d≤2^b := by
    have hbpos : 1≤B := by omega
    have hsq : B≤B*B := by simpa using Nat.mul_le_mul_left B hbpos
    nlinarith
  have hk : bin (2^b) d j<2^b := bin_lt hd hdQ hj
  constructor
  · rintro ⟨hx,hy⟩
    refine ⟨sampleU x,?_⟩
    have he : natBasis b (bin (2^b) d j)=sampleY x := by
      apply sampleY_number_injective b
      rw [natBasis_outputNumber,Nat.mod_eq_of_lt hk,hy]
    rw [he]
    exact hx.symm
  · rintro ⟨u,rfl⟩
    refine ⟨sampleSelected_word a m u _,?_⟩
    rw [sampleY_word,natBasis_outputNumber,Nat.mod_eq_of_lt hk]

/-- Recovery and selected-block checking are now linked to the ACTUAL physical
bin mass, without enumerating bins or residues in the circuit. -/
theorem sampler_recovered_label_mass {w b s B : ℕ} (a m : Basis w)
    (hm : 2≤(bitsValue m).toNat) (u : (ZMod (bitsValue m).toNat)ˣ)
    (ha : ((bitsValue a).toNat : ZMod (bitsValue m).toNat)=(u : ZMod (bitsValue m).toNat))
    (hB : B^2≤2^(b+2)) (hs : 2^(b+2)<2^s) (hdB : orderOf u<B)
    (j : ℕ) (hj : j<orderOf u) (hcop : Nat.Coprime j (orderOf u)) :
    Exactness.outcomeMass (fun x : Basis (OrderSample.width w (b+2)) => SampleSelected a m x ∧
      scanPairs (2^(b+2)) B (Triangular.outputNumber (sampleY x)) (2*s+1)=(orderOf u,j))
      (samplerState (s:=b) a m)=
      ∑ t : Fin (orderOf u), residueProbability (2^(b+2)) (orderOf u) j t.val := by
  have hd : 0<orderOf u := orderOf_pos u
  rw [selected_recovered_label a m hB hs hd hdB hj hcop]
  apply sampler_selected_bin_mass a m _ hm u ha j
  have hdQ : orderOf u≤2^(b+2) := by
    have hbpos : 1≤B := by omega
    have hsq : B≤B*B := by simpa using Nat.mul_le_mul_left B hbpos
    nlinarith
  rw [natBasis_outputNumber,Nat.mod_eq_of_lt (bin_lt hd hdQ hj)]

end ExactQuantumFactoring.OrderTrial


end

end OAI
