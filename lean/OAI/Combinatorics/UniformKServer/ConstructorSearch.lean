import Mathlib
import OAI.Combinatorics.UniformKServer.RawAccepted
import OAI.Combinatorics.UniformKServer.RuntimeExistence
import OAI.Combinatorics.UniformKServer.RawExistence

namespace OAI

noncomputable section

namespace UniformKServer.ConstructorSearch
open RawCertificate
open scoped Classical
abbrev Cert := Certificate×RuntimeCertificate.Cert

def verify (mult : ℕ) (i : Input) (v : Cert) : Bool :=
  RawCertificate.verify mult i v.1 && RuntimeCertificate.verify i.1 i.2.1 v.1 v.2

def candidate (mult : ℕ) (i : Input) (a : ℕ) : Option Cert :=
  (Encodable.decode a).bind fun v=>if verify mult i v then some v else none

def search (mult : ℕ) (i : Input) : Part Cert := Nat.rfindOpt (candidate mult i)

theorem primitive_verify (mult : ℕ) : Primrec₂ (verify mult) := by
  unfold verify
  apply PrimitiveRules.bool_and
  · exact (RawCertificate.primitive_verify mult).comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  · exact RuntimeCertificate.primitive_verify.comp
      ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair (Primrec.fst.comp Primrec.snd)) |>.pair
          (Primrec.snd.comp Primrec.snd))

theorem candidate_primrec (mult : ℕ) : Primrec₂ (candidate mult) := by
  have hd : Primrec (fun p : Input×ℕ=>(Encodable.decode p.2 : Option Cert)) := Primrec.decode.comp Primrec.snd
  have hg : Primrec (fun p : (Input×ℕ)×Cert=>if verify mult p.1.1 p.2 then some p.2 else none) := by
    rw [show (fun p : (Input×ℕ)×Cert=>if verify mult p.1.1 p.2 then some p.2 else none)=
      (fun p=>bif verify mult p.1.1 p.2 then some p.2 else none) from by funext p;rw [Bool.cond_eq_ite]]
    exact Primrec.cond ((primitive_verify mult).comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (Primrec.option_some.comp Primrec.snd) (Primrec.const none)
  exact Primrec.option_bind hd hg.to₂

theorem search_partrec (mult : ℕ) : Partrec (search mult) :=
  Partrec.rfindOpt (candidate_primrec mult).to_comp

theorem terminates {mult : ℕ} {i : Input} (h : ∃v,verify mult i v=true) :
    (search mult i).Dom := by
  obtain ⟨v,hv⟩:=h
  apply Nat.rfindOpt_dom.mpr
  refine ⟨Encodable.encode v,v,?_⟩
  change v∈((Encodable.decode (Encodable.encode v) : Option Cert).bind _)
  rw [Encodable.encodek]
  simp only [Option.bind_some,hv,ite_true,Option.mem_some_iff]

theorem correct {mult : ℕ} {i : Input} {v : Cert} (h : v∈search mult i) :
    verify mult i v=true := by
  obtain ⟨a,ha⟩:=Nat.rfindOpt_spec h
  simp only [candidate,Option.mem_def,Option.bind_eq_some_iff] at ha
  obtain ⟨u,hu,hv⟩:=ha
  split at hv
  next h=>cases Option.some.inj hv;exact h
  next h=>simp at hv

theorem exists_certificate {n k : ℕ} [NeZero k] (hn : 2≤n) (hk : 2≤k) (hkn : k≤n)
    (mult : ℕ) (hm : PartitionTree.absoluteRate≤(mult:ℝ)) (d : RationalMetric n)
    (draw : List RawArithmetic.Q)
    (hd : ∀x y : Fin n,RawArithmetic.value (RawTable.dist n draw x.val y.val)=d.distance x y) :
    ∃v : Cert,verify mult (n,k,draw) v=true := by
  obtain ⟨v,hv⟩:=RawExistence.exists_certificate hn hk hkn mult hm d draw hd
  have hp:=RawAccepted.spec d draw hd hv
  obtain ⟨c,hc⟩:=RuntimeCertificate.exists_cert (by omega) hkn v hp.numbers.restart_pos hp.rows
  exact ⟨(v,c),by simp only [verify,hv,hc,Bool.and_self]⟩

end UniformKServer.ConstructorSearch

end

end OAI
