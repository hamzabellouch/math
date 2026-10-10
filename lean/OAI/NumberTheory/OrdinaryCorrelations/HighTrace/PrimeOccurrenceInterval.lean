import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.DivisorFamily
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.ForwardSegment

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem.Specification
open OrdinaryCorrelations.SignedTrace
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h L : ℕ}

theorem prime_occurrence_interval (s : S.Specification D h L) (hs : s.Primitive)
    (q : S.Index) (i j k : Fin s.length) (hij : i ≤ j) (hjk : j ≤ k)
    (hqi : (q:ℕ) ∣ s.label i) (hqk : (q:ℕ) ∣ s.label k) : (q:ℕ) ∣ s.label j := by
  by_contra hqj
  have hij' : i<j := lt_of_le_of_ne hij (by intro he; exact hqj (he ▸ hqi))
  have hjk' : j<k := lt_of_le_of_ne hjk (by intro he; exact hqj (he ▸ hqk))
  let A := univ.filter (fun r : Fin s.length => r<j ∧ (q:ℕ) ∣ s.label r)
  let C := univ.filter (fun r : Fin s.length => j<r ∧ (q:ℕ) ∣ s.label r)
  have hA : A.Nonempty := ⟨i,mem_filter.mpr ⟨mem_univ _,hij',hqi⟩⟩
  have hC : C.Nonempty := ⟨k,mem_filter.mpr ⟨mem_univ _,hjk',hqk⟩⟩
  let a := A.max' hA
  let c := C.min' hC
  have ha := (mem_filter.mp (max'_mem A hA)).2
  have hc := (mem_filter.mp (min'_mem C hC)).2
  have hg : a.val+1<c.val := by
    have ha' : a<j := ha.1
    have hc' : j<c := hc.1
    change a.val<j.val at ha'
    change j.val<c.val at hc'
    omega
  apply s.primitive_no_prime_gap hs q a c hg ha.2 hc.2
  intro r har hrc hqr
  rcases lt_trichotomy r j with hrj | hrj | hjr
  · have hrA : r ∈ A := mem_filter.mpr ⟨mem_univ _,hrj,hqr⟩
    exact (not_le_of_gt har) (le_max' A r hrA)
  · exact hqj (hrj ▸ hqr)
  · have hrC : r ∈ C := mem_filter.mpr ⟨mem_univ _,hjr,hqr⟩
    exact (not_le_of_gt hrc) (min'_le C r hrC)

lemma sign_eq_of_adjacent_label (s : S.Specification D h L) (i j : Fin s.length)
    (hij : j.val=i.val+1) (he : s.label i=s.label j) : s.sign i=s.sign j := by
  have hv : j.castSucc=i.succ := Fin.ext hij
  have hi := s.step i
  have hj := s.step j
  rw [hv,← he] at hj
  by_contra hne
  have hz : s.sign i + s.sign j = 0 := by
    rcases s.sign_mem i with ha|ha <;> rcases s.sign_mem j with hb|hb <;> omega
  have hoff : s.offset j.succ = s.offset i.castSucc := by
    calc
      s.offset j.succ = s.offset i.castSucc + (s.sign i+s.sign j)*(h:ℤ)*s.label i := by
        linear_combination hi + hj
      _ = s.offset i.castSucc := by rw [hz]; ring
  have hval := congrArg Fin.val (s.offsets_distinct hoff)
  simp only [Fin.val_succ,Fin.val_castSucc] at hval
  omega

end OrdinaryCorrelations.GraphKernel.PrimeSystem.Specification

end

end OAI
