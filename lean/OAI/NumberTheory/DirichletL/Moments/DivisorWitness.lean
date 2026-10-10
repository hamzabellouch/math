import OAI.NumberTheory.DirichletL.Moments.DivisorRawEnergy
import OAI.NumberTheory.DirichletL.Moments.SlotRatios

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorWitness
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
open CenteredMomentDivisorRows CenteredMomentDivisorRaw CenteredMomentHeckeExpansion
open CenteredMomentRectangle HeckeFamily IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem exists_tsum_term {α : Type*} (f : α → ℂ) (h : (∑' x,f x) ≠ 0) :
    ∃ x,f x ≠ 0 := by
  by_contra hn
  push Not at hn
  exact h (by simp only [hn,tsum_zero])

theorem allocated_nonzero_witness (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ)
    (hne : allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂ ≠ 0) :
    ∃ (v : (i : ι) → S i) (I J : Ideal O),
      allocationTerm D Finset.univ (factorTuple (fun i => v i) I J) a ≠ 0 ∧
      (∀ i,β i (v i) ≠ 0) ∧ idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J ≠ 0 := by
  obtain ⟨v,_,hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨hβ,ht⟩ := mul_ne_zero_iff.mp hv
  obtain ⟨I,hI⟩ := exists_tsum_term _ ht
  obtain ⟨J,hJ⟩ := exists_tsum_term _ hI
  have hh := mul_ne_zero_iff.mp hJ
  exact ⟨v,I,J,(mul_ne_zero_iff.mp hh.1).1,
    fun i => Finset.prod_ne_zero_iff.mp hβ i (Finset.mem_univ i),hh.2⟩

def actualExtracted (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) : Ideal O :=
  (selectedPlain D a 0*selectedPlain D a 1)*∏ i∈frozenIndices D a,v i

private theorem prime_dvd_selectedPlain (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (j : Fin 2) (P : primeSupport D)
    (hP : P ∈ selectedPrimes D Finset.univ a (Sum.inr j)) :
    (P : Ideal O) ∣ selectedPlain D a j := by
  exact Finset.dvd_prod_of_mem (fun q : primeSupport D => (q : Ideal O))
    (a := P) (s := selectedPrimes D Finset.univ a (Sum.inr j)) hP

theorem divisor_dvd_actualExtracted (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) (I J : Ideal O)
    (hn : allocationTerm D Finset.univ (factorTuple v I J) a ≠ 0) :
    D ∣ actualExtracted D a v := by
  apply (squarefree_dvd_iff D _ hD).mpr
  intro P hP
  let PP : primeSupport D := ⟨P,hP⟩
  obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp (a PP).property).1
  have hmem : PP ∈ selectedPrimes D Finset.univ a i :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ PP,hi⟩
  cases i with
  | inl i =>
      have hfr : i ∈ frozenIndices D a := Finset.mem_filter.mpr ⟨Finset.mem_univ i,⟨PP,hmem⟩⟩
      have hd : P∣v i := selected_divides_factor D Finset.univ (factorTuple v I J) a hn PP (Sum.inl i) hi
      exact dvd_mul_of_dvd_right (hd.trans (Finset.dvd_prod_of_mem v (a := i) (s := frozenIndices D a) hfr)) _
  | inr j =>
      have hd : P∣selectedPlain D a j := prime_dvd_selectedPlain D a j PP hmem
      fin_cases j
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _
      · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _

theorem actualExtracted_ne_zero (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) (hv : ∀ i,v i ≠ 0) : actualExtracted D a v ≠ 0 :=
  mul_ne_zero (mul_ne_zero (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 0))
    (selectedDivisor_ne_zero D Finset.univ a (Sum.inr 1)))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hv i))

theorem actualExtracted_norm_boundary (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) (hv : ∀ i,v i ≠ 0) (I J : Ideal O)
    (hn : allocationTerm D Finset.univ (factorTuple v I J) a ≠ 0) :
    (Ideal.absNorm D:ℝ) ≤ selectedNorm D a*∏ i∈frozenIndices D a,(Ideal.absNorm (v i):ℝ) := by
  have h := Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (actualExtracted_ne_zero D a v hv))) (map_dvd Ideal.absNorm (divisor_dvd_actualExtracted D hD a v I J hn))
  simpa only [actualExtracted,map_mul,map_prod,Nat.cast_mul,Nat.cast_prod,selectedNorm] using
    (show (Ideal.absNorm D:ℝ) ≤ Ideal.absNorm (actualExtracted D a v) by exact_mod_cast h)

end SevenEighths.CenteredMomentDivisorWitness

end

end OAI
