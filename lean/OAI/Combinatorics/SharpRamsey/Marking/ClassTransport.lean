import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.ActualClassLaw
import OAI.Combinatorics.SharpRamsey.Marking.UniformSupports

namespace OAI

section
namespace SharpLogRamsey.ReciprocalBands
open Real

lemma reflected_integer_band {d r : ℕ} (hr : r≤d+1) {σ K u : ℝ}
    (h : IntegerBand r σ K u) :
    IntegerBand (d+1-r) σ K (((d:ℝ)+1)*σ-u) := by
  unfold IntegerBand at h ⊢
  rw [Nat.cast_sub hr,Nat.cast_add,Nat.cast_one]
  convert h using 1
  rw [show ((d:ℝ)+1)*σ-u-((d:ℝ)+1-r)*σ= -(u-r*σ) by ring,abs_neg]

lemma reflected_open_band {d r : ℕ} (hr : r≤d+2) {σ K u : ℝ}
    (h : OpenBand r σ K u) :
    OpenBand (d+2-r) σ K (((d:ℝ)+1)*σ-u) := by
  unfold OpenBand at h ⊢
  rw [Nat.cast_sub hr,Nat.cast_add,Nat.cast_ofNat]
  constructor <;> nlinarith [h.1,h.2]

end SharpLogRamsey.ReciprocalBands

namespace SharpLogRamsey.Marking
open Finset Selection ReciprocalBands
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

abbrev CovectorPair := Projectivization K (Module.Dual K V) × Projectivization K V

def covectorTuple {ι : Type*} (F : ι→ProjectivePair (K:=K) (V:=V)) :
    ι → (CovectorPair (K:=K) (V:=V)) := fun i => (F i).swap

def covectorDomain (D : Finset (ProjectivePair (K:=K) (V:=V))) :
    Finset (CovectorPair (K:=K) (V:=V)) := D.map (Equiv.prodComm _ _).toEmbedding

lemma covectorDomain_mem (D : Finset (ProjectivePair (K:=K) (V:=V)))
    (f : ProjectivePair (K:=K) (V:=V)) : f.swap ∈covectorDomain D ↔ f∈D := by
  simp [covectorDomain]

lemma covectorDomain_card (D : Finset (ProjectivePair (K:=K) (V:=V))) :
    (covectorDomain D).card=D.card := card_map _

lemma covectorDomain_first (D : Finset (ProjectivePair (K:=K) (V:=V))) :
    (covectorDomain D).image Prod.fst=D.image Prod.snd := by
  ext a
  simp [covectorDomain]

lemma covectorDomain_second (D : Finset (ProjectivePair (K:=K) (V:=V))) :
    (covectorDomain D).image Prod.snd=D.image Prod.fst := by
  ext a
  simp [covectorDomain]

lemma covectorTuple_consistent {N : ℕ} (F : Fin N→ProjectivePair (K:=K) (V:=V))
    [FiniteDimensional K V]
    (h : ScanConsistent ((List.ofFn F).map toScan)) :
    ∀ (i j : Fin N),i<j→(covectorTuple F i).1.rep (covectorTuple F j).2.rep=0→
      (covectorTuple F j).1.rep (covectorTuple F i).2.rep=0 := by
  rw [List.map_ofFn] at h
  exact List.pairwise_ofFn.mp h

lemma covectorTuple_flag {ι : Type*} (F : ι→ProjectivePair (K:=K) (V:=V))
    (h : ∀ i,Incidence.Incident (F i).1 (F i).2) (i : ι) :
    (covectorTuple F i).1.rep (covectorTuple F i).2.rep=0 := h i

variable [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

omit [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)]
  [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
theorem covectorDomain_reciprocal {d : ℕ} {gap : ℝ}
    (D : Finset (ProjectivePair (K:=K) (V:=V)))
    (integer : Bool) (r : Fin (d+1))
    (h : ValidSlotClass d gap D (.inl (integer,r))) :
    let r' := if integer then d+1-r.val else d+2-r.val
    1≤r' ∧ r'≤d ∧ ∃ u : ℝ,
      Real.log (Nat.card K)≤u ∧ u≤(d:ℝ)*Real.log (Nat.card K) ∧
      (((covectorDomain D).image Prod.fst).card:ℝ)≤
        1024*Real.exp (((d:ℝ)+1)*Real.log (Nat.card K)-u) ∧
      (((covectorDomain D).image Prod.snd).card:ℝ)≤1024*Real.exp u ∧
      (if integer then IntegerBand r' (Real.log (Nat.card K)) gap u
        else 2≤r' ∧ OpenBand r' (Real.log (Nat.card K)) gap u) := by
  obtain ⟨u,hlo,hhi,hA,hB,hr,hband⟩:=h
  have hrle : r.val≤d := by omega
  cases integer
  · simp only [Bool.false_eq_true,ite_false] at hband ⊢
    refine ⟨by omega,by omega,((d:ℝ)+1)*Real.log (Nat.card K)-u,?_,?_,?_,?_,
      by omega,reflected_open_band (by omega) hband.2⟩
    · nlinarith
    · nlinarith
    · rw [covectorDomain_first]
      convert hB using 1
      congr 2
      ring
    · rw [covectorDomain_second]
      exact hA
  · simp only [ite_true] at hband ⊢
    refine ⟨by omega,by omega,((d:ℝ)+1)*Real.log (Nat.card K)-u,?_,?_,?_,?_,
      reflected_integer_band (by omega) hband⟩
    · nlinarith
    · nlinarith
    · rw [covectorDomain_first]
      convert hB using 1
      congr 2
      ring
    · rw [covectorDomain_second]
      exact hA

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma covectorTuple_entropy (p : Law Ω)
    (F : Ω→ι→ProjectivePair (K:=K) (V:=V)) :
    entropy (p.map (fun x=>covectorTuple (F x)))=entropy (p.map F) := by
  rw [show (fun x=>covectorTuple (F x))=covectorTuple∘F from rfl,←Law.map_map]
  apply entropy_map_eq_of_injective
  intro f g he
  funext i
  exact Prod.swap_injective (congrFun he i)

end
end SharpLogRamsey.Marking

end

end OAI
