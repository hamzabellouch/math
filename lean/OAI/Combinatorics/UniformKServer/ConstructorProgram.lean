import Mathlib
import OAI.Combinatorics.UniformKServer.ConstructorSearch
import OAI.Combinatorics.UniformKServer.LiteralPartial

namespace OAI

noncomputable section

namespace UniformKServer.ConstructorProgram
open RawCertificate
open scoped Classical

def read (a : ℕ) : Input := RawBinary.input a.bits

def result (i : Input) (v : ConstructorSearch.Cert) : List.Vector ℕ 3 :=
  ⟨[2^(2^v.2.2),2^(RuntimeCertificate.B i.2.1 v.1),
    Encodable.encode (RawProgram.initial i.1 i.2.1 v.1)],rfl⟩

def run (mult : ℕ) (a : List.Vector ℕ 1) : Part (List.Vector ℕ 3) :=
  (ConstructorSearch.search mult (read a.head)).map (result (read a.head))

theorem primitive_read : Primrec read :=
  RawBinary.primitive_input _ RawBits.primitive_bits

theorem primitive_result : Primrec₂ result := by
  apply Primrec.vector_toList_iff.mp
  change Primrec (fun p : Input×ConstructorSearch.Cert=>[2^(2^p.2.2.2),2^(RuntimeCertificate.B p.1.2.1 p.2.1),Encodable.encode (RawProgram.initial p.1.1 p.1.2.1 p.2.1)])
  fun_prop

theorem run_partrec (mult : ℕ) : Partrec (run mult) := by
  have h : Partrec (fun a : List.Vector ℕ 1=>ConstructorSearch.search mult (read a.head)) :=
    (ConstructorSearch.search_partrec mult).comp (primitive_read.comp Primrec.vector_head).to_comp
  exact h.map (primitive_result.comp
    (primitive_read.comp (Primrec.vector_head.comp Primrec.fst)) Primrec.snd).to_comp.to₂

def code (mult : ℕ) : Turing.ToPartrec.Code :=
  Classical.choose (LiteralVector.partial_code_exists (run mult) (run_partrec mult))

theorem code_correct {mult : ℕ} {a : ℕ} {v : ConstructorSearch.Cert}
    (h : v∈ConstructorSearch.search mult (read a)) :
    (result (read a) v).val∈Turing.ToPartrec.Code.eval (code mult) [a] := by
  exact Classical.choose_spec (LiteralVector.partial_code_exists (run mult) (run_partrec mult))
    (⟨[a],rfl⟩ : List.Vector ℕ 1) (result (read a) v) ((Part.mem_map_iff _).mpr ⟨v,h,rfl⟩)

theorem input_code {n k : ℕ} (d : RationalMetric n) (s : Configuration n k) (w : List Bool) :
    RawBinary.input (instanceCode d s++w)=(n,k,(RawBinary.distances d).map RawMetric.present) := by
  unfold RawBinary.input instanceCode
  simp only [List.append_assoc,RawBinary.read_natCode]
  rw [←RawBinary.distance_codes,←RawBinary.distances_length d,RawBinary.readMany_codes]

theorem read_code {n k : ℕ} (d : RationalMetric n) (s : Configuration n k) :
    read (RawBinary.value (instanceCode d s++[true]))=
      (n,k,(RawBinary.distances d).map RawMetric.present) := by
  rw [read,RawBits.bits_value,input_code]

end UniformKServer.ConstructorProgram

end

end OAI
