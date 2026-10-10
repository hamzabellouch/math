import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.LocalWithList
import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.VertexWeight

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.FiniteIntegration OrdinaryCorrelations.SignedTrace
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h L ℓ : ℕ}

def listSupport (w : ClosedLine h ℓ) (𝔏 : List (AttachedSpec w D L)) : Finset ℕ :=
  𝔏.toFinset.biUnion (fun s => s.spec.primeSupport)

lemma listLocal_eq_one_of_not_mem (w : ClosedLine h ℓ)
    (𝔏 : List (AttachedSpec w D L)) (p : S.Index)
    (hp : (p : ℕ) ∉ listSupport w 𝔏) (a : ZMod (p : ℕ)) :
    listLocal w 𝔏 p a = 1 := by
  apply ite_eq_left
  intro s hs
  have hnot : (p : ℕ) ∉ s.spec.primeSupport := by
    intro hmem
    exact hp (mem_biUnion.mpr ⟨s, List.mem_toFinset.mpr hs, hmem⟩)
  constructor
  · intro hpeq
    exact (hnot (by simp [Specification.primeSupport, hpeq])).elim
  · intro i hd
    have hpf : (p : ℕ) ∈ (s.spec.label i).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨S.prime_mem p p.property, hd,
        (D.squarefree _ (s.spec.label_mem i)).ne_zero⟩
    exact (hnot (mem_insert_of_mem (mem_biUnion.mpr ⟨i, mem_univ i, hpf⟩))).elim

lemma unique_occurrence_of_free (w : ClosedLine h ℓ) (p : S.Index)
    (hp : ¬S.IsFixed w p) (e : Fin ℓ) (he : (p : ℕ) ∣ w.label e) :
    ∀ i, (p : ℕ) ∣ w.label i ↔ i = e := by
  have hcard : S.occurrenceCount w p ≤ 1 := by
    by_contra hn
    have htwo : 2 ≤ S.occurrenceCount w p := by omega
    exact hp ⟨⟨e,he⟩, Or.inr htwo⟩
  have huniq := (Finset.card_le_one.mp hcard)
  intro i
  constructor
  · intro hi
    exact huniq i (mem_filter.mpr ⟨mem_univ i,hi⟩) e (mem_filter.mpr ⟨mem_univ e,he⟩)
  · rintro rfl
    exact he

lemma localWithList_eq_centerFactor (w : ClosedLine h ℓ)
    (𝔏 : List (AttachedSpec w D L)) (p : S.Index)
    (hp : ¬S.IsCore p) (hlist : (p : ℕ) ∉ listSupport w 𝔏) :
    localWithList w 𝔏 p = centerPrimeFactor w.departures w.label := by
  funext a
  rw [localWithList, listLocal_eq_one_of_not_mem w 𝔏 p hlist, mul_one]
  exact center_primeFactor_eq S w p hp a

theorem good_free_center_mean (w : ClosedLine h ℓ) (hh : 0 < h)
    (𝔏 : List (AttachedSpec w D L)) (p : S.FreeCenterIndex w)
    (e : Fin ℓ) (he : (p.val.val : ℕ) ∣ w.label e)
    (hgood : w.Good e) (hunc : w.Uncorrupted (p.val.val : ℕ) e)
    (hlist : (p.val.val : ℕ) ∉ listSupport w 𝔏)
    (hlarge : 2 * (ℓ+1) ≤ (p.val.val : ℕ)) :
    0 ≤ avg (localWithList w 𝔏 p.val.val) ∧
    |avg (localWithList w 𝔏 p.val.val)| ≤ theta / (2*(p.val.val : ℝ)) := by
  rw [localWithList_eq_centerFactor w 𝔏 p.val.val p.property hlist]
  have hmean := w.good_center_prime_mean hh e
    (unique_occurrence_of_free w p.val.val p.val.property e he) hgood hunc hlarge
  simpa only [avg, primeMean, ZMod.card] using hmean

end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
