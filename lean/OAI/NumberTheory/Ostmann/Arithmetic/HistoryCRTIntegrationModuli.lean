import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTIntegrationBlocks
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepresentativeSourceSeparationSelected

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryCRTIntegration
open Construction HistoryPairRepresentatives HistoryRepresentativeSourceSeparation
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

def rootModulus (h : History l) : ℕ := (h.root.small.map SmallSlot.value).prod
def outsideModulus (outside : List ℕ) : ℕ := outside.prod
def frequencyModulus (h g : History l) (n : ℕ) : ℕ :=
  FrequencyPrecision.product (h.frequencies++g.frequencies)^n
def representativeModulus (h g : History l) : ℕ :=
  ∏ r : Representative h g,(prime h g r)^2

def historyModuli (h g : History l) (outside : List ℕ) (n : ℕ) : Fin 4 → ℕ :=
  fourModuli (rootModulus h) (outsideModulus outside)
    (frequencyModulus h g n) (representativeModulus h g)

theorem historyModuli_prod (h g : History l) (outside : List ℕ) (n : ℕ) :
    (∏ i,historyModuli h g outside n i)=
      rootModulus h*outsideModulus outside*frequencyModulus h g n*representativeModulus h g :=
  fourModuli_prod _ _ _ _

theorem historyModuli_pairwise (h g : History l) (hp : PairAdmissible h g outside) (n : ℕ) :
    Pairwise (fun i j => (historyModuli h g outside n i).Coprime
      (historyModuli h g outside n j)) :=
  fourModuli_pairwise _ _ _ _ (hp.2.2.2 n)

theorem rootModulus_pos (h : History l) (hs : h.Supported V outside) : 0 < rootModulus h := by
  apply List.prod_pos
  intro n hn
  exact History.supported_root_positive hs n
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hn))

theorem outsideModulus_pos (hout : ∀ p ∈ outside,Nat.Prime p) : 0 < outsideModulus outside :=
  List.prod_pos (fun p hp => (hout p hp).pos)

theorem frequencyModulus_pos (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside) (n : ℕ) :
    0 < frequencyModulus h g n := by
  apply pow_pos
  apply List.prod_pos
  intro a ha
  obtain ⟨s,hs',rfl⟩ := List.mem_map.mp ha
  apply Int.natAbs_pos.mpr
  rcases List.mem_append.mp hs' with hh | hg
  · exact (History.supported_frequency_bounds hs s hh).1
  · exact (History.supported_frequency_bounds gs s hg).1

theorem representativeModulus_pos (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside) :
    0 < representativeModulus h g :=
  Finset.prod_pos (fun r _ => pow_pos (representative_prime h g hs gs r).pos _)

theorem historyModuli_pos (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (hout : ∀ p ∈ outside,Nat.Prime p) (n : ℕ) (i : Fin 4) :
    0 < historyModuli h g outside n i := by
  fin_cases i
  · exact rootModulus_pos h hs
  · exact outsideModulus_pos hout
  · exact frequencyModulus_pos h g hs gs n
  · exact representativeModulus_pos h g hs gs

theorem historyModuliNeZero (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside)
    (hout : ∀ p ∈ outside,Nat.Prime p) (n : ℕ) : ∀ i,NeZero (historyModuli h g outside n i) :=
  fun i => ⟨ne_of_gt (historyModuli_pos h g hs gs hout n i)⟩

theorem representativeSquaresNeZero (h g : History l)
    (hs : h.Supported V outside) (gs : g.Supported V outside) :
    ∀ r : Representative h g,NeZero ((prime h g r)^2) :=
  fun r => ⟨ne_of_gt (pow_pos (representative_prime h g hs gs r).pos _)⟩

end Ostmann.Arithmetic.HistoryCRTIntegration

end

end OAI
