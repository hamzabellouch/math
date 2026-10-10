import Mathlib
import OAI.Combinatorics.UniformKServer.RawCertificate

namespace OAI

noncomputable section
                                
section

namespace UniformKServer.RawSearch
open RawCertificate

def candidate (mult : ℕ) (i : Input) (a : ℕ) : Option Certificate :=
  (Encodable.decode a).bind fun v=>if verify mult i v then some v else none

def search (mult : ℕ) (i : Input) : Part Certificate := Nat.rfindOpt (candidate mult i)

def accept (mult : ℕ) (i : Input) (v : Certificate) : Option Certificate :=
  bif verify mult i v then some v else none

theorem accept_primrec (mult : ℕ) : Primrec₂ (accept mult) :=
  Primrec.cond (primitive_verify mult) (Primrec.option_some.comp Primrec.snd) (Primrec.const none)

theorem candidate_primrec (mult : ℕ) : Primrec₂ (candidate mult) := by
  have hd : Primrec (fun p : Input×ℕ=>(Encodable.decode p.2 : Option Certificate)) :=
    Primrec.decode.comp Primrec.snd
  have hg : Primrec₂ (fun p : Input×ℕ=>fun v : Certificate=>accept mult p.1 v) :=
    (accept_primrec mult).comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact (Primrec.option_bind hd hg).of_eq (by intro p;simp only [candidate,accept,Bool.cond_eq_ite])

theorem search_partrec (mult : ℕ) : Partrec (search mult) :=
  Partrec.rfindOpt (candidate_primrec mult).to_comp

theorem terminates {mult : ℕ} {i : Input} (h : ∃v,verify mult i v=true) :
    (search mult i).Dom := by
  obtain ⟨v,hv⟩:=h
  apply Nat.rfindOpt_dom.mpr
  refine ⟨Encodable.encode v,v,?_⟩
  change v∈((Encodable.decode (Encodable.encode v) : Option Certificate).bind _)
  rw [Encodable.encodek]
  simp only [Option.bind_some,hv,ite_true,Option.mem_some_iff]

theorem correct {mult : ℕ} {i : Input} {v : Certificate} (h : v∈search mult i) :
    verify mult i v=true := by
  obtain ⟨a,ha⟩:=Nat.rfindOpt_spec h
  simp only [candidate,Option.mem_def,Option.bind_eq_some_iff] at ha
  obtain ⟨u,hu,hv⟩:=ha
  split at hv
  next accepted =>
    cases Option.some.inj hv
    exact accepted
  next h=>simp at hv

end UniformKServer.RawSearch

end


end

end OAI
