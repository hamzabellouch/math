import OAI.Combinatorics.SquareDifference.CyclicIndicator

namespace OAI

section

open Finset

open scoped BigOperators ComplexConjugate

namespace SquareDifference

open LiftTheory.SquareDifference PairBridge

section Coefficient

variable {J : Type*} [Fintype J] [instDecidableEqJ : DecidableEq J] (p : J → ℕ) [instNeZeropj : ∀j,NeZero (p j)]

lemma residueFourier_real_mul (a : ℝ) (f : ResidueSpace p → ℝ) (ξ : ResidueSpace p) :
    residueFourier p (fun x => ((a*f x:ℝ):ℂ)) ξ=(a:ℂ)*residueFourier p (fun x => (f x:ℂ)) ξ := by
  simp only [residueFourier,Complex.ofReal_mul,mul_assoc,mul_expect]

lemma sequenceCoeff_mul {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (N : ℕ) (a : ℝ) (f : ℕ → ℝ) (ξ : ResidueSpace p) :
    sequenceCoeff p N (fun n => a*f n) ξ=(a:ℂ)*sequenceCoeff p N f ξ := by
  simp only [sequenceCoeff,Complex.ofReal_mul,mul_assoc,←mul_sum]
  ring

lemma selected_gated {J : Type*}
    [Fintype J]
    [DecidableEq J]
    (p : J → ℕ)
    [∀ (j : J), NeZero (p j)] (M a L : ℕ) (A : Finset ℕ) (s : ZMod M) (B : Finset J) (z : ResidueSpace p) (n : ℕ) :
    gatedSequence p B z (intervalInput a L (smallResidueInput M A s)) n=
      (M*(∏j∈B,p j):ℝ)*selectedIndicator p M a L A s B z n := by
  unfold gatedSequence intervalInput smallResidueInput natIndicator selectedIndicator
  by_cases hA : n∈A <;> by_cases hi : n∈Ico a (a+L) <;>
    by_cases hs : (n:ZMod M)=s <;> by_cases hz : ∀j∈B,(n:ZMod (p j))=z j <;>
    simp [hA,hi,hs,hz,Nat.cast_prod] ; ring_nf

lemma smallResidueInput_zero (M N : ℕ) (A : Finset ℕ) (hA : A⊆range N) (s : ZMod M)
    (n : ℕ) (hn : N≤n) : smallResidueInput M A s n=0 := by
  unfold smallResidueInput
  rw [natIndicator_vanish N A hA n hn]
  simp

lemma selected_sequenceCoeff (M a L N : ℕ) (A : Finset ℕ) (hA : A⊆range N)
    (s : ZMod M) (B : Finset J) (z : ResidueSpace p) (q : ℕ) [NeZero q] (hN : N≤q)
    (ξ : ResidueSpace (OutsideModulus p B)) :
    sequenceCoeff (OutsideModulus p B) N (selectedIndicator p M a L A s B z) ξ=
      sequenceResidueFourier (OutsideModulus p B) N
        (fun x : ZMod q => (selectedIndicator p M a L A s B z x.val:ℂ)) ZMod.val ξ := by
  unfold sequenceCoeff sequenceResidueFourier
  congr 1
  symm
  exact sum_zmod_val_support q N hN
    (fun n => (selectedIndicator p M a L A s B z n:ℂ)*conj (prodChar (OutsideModulus p B) ξ (fun j => (n:ZMod (p j)))))
    (fun n hn => by rw [selectedIndicator_zero p M a L N A hA s B z n hn]; simp)

lemma actual_interval_outside_coefficient (M a L N Q H : ℕ) (hN : 0<N)
    (A : Finset ℕ) (hA : A⊆range N) (s : ZMod M) (B : Finset J)
    (hHQ : H*(∏j∈B,p j)≤Q) (z : ResidueSpace p) (q : ℕ) [NeZero q] (hNq : N≤q)
    (ξ : ResidueSpace (OutsideModulus p B)) (hξ : supportDenominator (OutsideModulus p B) ξ≤H) :
    residueFourier (OutsideModulus p B)
      (fun x => (intervalLift p a L Q (smallResidueInput M A s) (assembleOutside p B z x):ℂ)) ξ=
      (((N:ℝ)/L*(M*(∏j∈B,p j):ℝ)):ℂ)*
        sequenceResidueFourier (OutsideModulus p B) N
          (fun x : ZMod q => (selectedIndicator p M a L A s B z x.val:ℂ)) ZMod.val ξ := by
  simp_rw [intervalLift_global p N a L Q hN (smallResidueInput M A s)
    (smallResidueInput_zero M N A hA s)]
  rw [residueFourier_real_mul,actual_frozen_outside_coefficient p B N Q H _ hHQ z ξ hξ]
  have heg : gatedSequence p B z (intervalInput a L (smallResidueInput M A s))=
      fun n => (M*(∏j∈B,p j):ℝ)*selectedIndicator p M a L A s B z n :=
    funext (selected_gated p M a L A s B z)
  rw [heg]
  rw [sequenceCoeff_mul,selected_sequenceCoeff p M a L N A hA s B z q hNq]
  push_cast
  ring

end Coefficient

end SquareDifference

end

end OAI
