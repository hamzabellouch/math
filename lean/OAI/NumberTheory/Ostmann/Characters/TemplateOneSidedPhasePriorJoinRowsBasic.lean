import OAI.NumberTheory.Ostmann.Characters.OneSidedBilinearRows
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPrior

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction Preliminaries TemplateOneSidedPrior PrimeDyadicCover
attribute [local instance] Classical.propDecidable

def sourceRowAmplitude {A : ℕ} {κ : Type*} (Q : ℕ)
    (F : PrimeUpTo A → κ → ℂ) (r : Fin Q) (n : ℕ) (j : κ) : ℂ :=
  sourceTest (fun q => F q j) (Q*n+r.val)

theorem sourceTest_bilinear {A : ℕ} {κ : Type*} [Fintype κ]
    (q : κ → ℕ) (χ : ∀j,MulChar (ZMod (q j)) ℂ)
    (ν : κ → ℝ) (U : PrimeUpTo A → ℂ) (V : κ → ℂ)
    (F : PrimeUpTo A → κ → ℂ) (n : ℕ) :
    sourceTest (fun p=>U p*∑j,(ν j:ℂ)*V j*χ j (p.val:ZMod (q j))*F p j) n =
      sourceTest U n * ∑j,(ν j:ℂ)*V j*
        (χ j (n:ZMod (q j))*sourceTest (fun p=>F p j) n) := by
  by_cases hn:n∈A.primesLE
  · simp only [sourceTest,dite_eq_left hn,mul_assoc]
  · simp only [sourceTest,dite_eq_right hn,zero_mul]

theorem source_bilinear_cmean_eq_rows {A : ℕ} {κ : Type*} [Fintype κ]
    (Q H : ℕ) (hQ : 0<Q) (E : Finset (PrimeUpTo A)) (hE : 0<primeShellMass E)
    (hmin : ∀p∈E,Q≤p.val) (hmax : ∀p∈E,p.val≤H)
    (q : κ → ℕ) (χ : ∀j,MulChar (ZMod (q j)) ℂ)
    (ν : κ → ℝ) (U : PrimeUpTo A → ℂ) (V : κ → ℂ)
    (F : PrimeUpTo A → κ → ℂ) :
    (primeShellPrior E hE).cmean (fun p=>U p*∑j,(ν j:ℂ)*V j*χ j (p.val:ZMod (q j))*F p j) =
      ∑i:Index H, oneSidedMean (sourceRowMass Q H E i) ν
        (fun x=>sourceTest U (rowValue Q (2*lower Q H i+1) x)) V
        (rowCharacterKernel q χ Q (2*lower Q H i+1) (fun r:Fin Q=>r.val)
          (sourceRowAmplitude Q F)) := by
  rw [source_cmean_eq_rows_actual Q H hQ E hE hmin hmax]
  apply Finset.sum_congr rfl
  intro i hi
  simp_rw [sourceTest_bilinear]
  simp only [oneSidedMean,rowCharacterKernel,primeCharacterKernel,
    sourceRowAmplitude,rowValue,mul_assoc]

theorem source_bilinear_cmean_eq_rows_of_log {A : ℕ} {κ : Type*} [Fintype κ]
    (Q : ℕ) (hQ : 0<Q) (E : Finset (PrimeUpTo A)) (hE : 0<primeShellMass E)
    {β L : ℝ} (hmin : ∀p∈E,Q≤p.val)
    (hmax : ∀p∈E,Real.log p.val≤Real.exp (β*L))
    (q : κ → ℕ) (χ : ∀j,MulChar (ZMod (q j)) ℂ)
    (ν : κ → ℝ) (U : PrimeUpTo A → ℂ) (V : κ → ℂ)
    (F : PrimeUpTo A → κ → ℂ) :
    (primeShellPrior E hE).cmean (fun p=>U p*∑j,(ν j:ℂ)*V j*χ j (p.val:ZMod (q j))*F p j) =
      ∑i:Index (sourceUpper β L), oneSidedMean (sourceRowMass Q (sourceUpper β L) E i) ν
        (fun x=>sourceTest U (rowValue Q (2*lower Q (sourceUpper β L) i+1) x)) V
        (rowCharacterKernel q χ Q (2*lower Q (sourceUpper β L) i+1) (fun r:Fin Q=>r.val)
          (sourceRowAmplitude Q F)) :=
  source_bilinear_cmean_eq_rows Q (sourceUpper β L) hQ E hE hmin
    (source_upper_of_log E hmax) q χ ν U V F

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
