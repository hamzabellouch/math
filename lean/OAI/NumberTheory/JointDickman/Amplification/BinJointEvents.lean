import OAI.NumberTheory.JointDickman.Analysis.CanonicalCharacterPairs

namespace OAI

/-! # Finite Fourier inversion gives every joint bin event -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem bin_joint_event_limit
    (hMR : RealShortIntervalInput) (hMRT : ComplexShortIntervalInput)
    (hKMT : CharacterDistanceDivergence) (hFord : FordUpperSieveInput)
    (hSD : SquarefreeSelbergDelangeInput) (hSW : SquarefreeCharacterEstimateInput)
    (hM : PrimeReciprocalMertensInput) (hMP : PrimeProductMertensInput)
    (hMC : ∀ B M : ℕ, FiniteMcDiarmidInput (Fin M) (auxiliaryPrimes B).powerset)
    {J : ℕ} (hJ : 0 < J) (ν : BinCountState J → ℝ)
    (hν : ∀ r, 0 ≤ ν r) (hνone : ∑ r, ν r = 1)
    (hνmean : ∀ A : ℝ, 0 < A → ∀ r,
      Tendsto (fun x : ℝ => binStateDensity J A x r) atTop (𝓝 (ν r)))
    (P Q : BinCountState J → Prop) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N,
      if P (canonicalBinVector J (N : ℝ) n) ∧ Q (canonicalBinVector J (N : ℝ) (n+1))
        then (1 : ℂ) else 0)/(N : ℂ)) atTop
      (𝓝 (((∑ r with P r, ν r : ℝ) : ℂ)*((∑ r with Q r, ν r : ℝ) : ℂ))) := by
  have hc (χ ψ : AddChar (BinCountState J) ℂ) :=
    canonical_character_pair_limit hMR hMRT hKMT hFord hSD hSW hM hMP hMC hJ ν hν hνone hνmean χ ψ
  have he := jointEvent_factorization (G := BinCountState J) (H := BinCountState J)
    (fun N => range N) (fun N => 1/(N : ℂ))
    (fun N n => canonicalBinVector J (N : ℝ) n)
    (fun N n => canonicalBinVector J (N : ℝ) (n+1))
    (fun r => (ν r : ℂ)) (fun r => (ν r : ℂ))
    (fun χ ψ => by simpa only [one_div_mul_eq_div] using hc χ ψ) P Q
  simpa only [one_div_mul_eq_div,Complex.ofReal_sum] using he

noncomputable def higherBinEvent (J k : ℕ) (r : BinCountState J) : Prop :=
  ∀ i : Fin (J-1), k ≤ i.val+1 → r i = 0

theorem higherBinEvent_iff {J k n : ℕ} {x : ℝ} (hJ : 0 < J) (hk : 0 < k) :
    higherBinEvent J k (canonicalBinVector J x n) ↔
      ∀ i ∈ Ico k J, binCount (primeBin x J i) n = 0 := by
  have hzero (i : Fin (J-1)) : canonicalBinVector J x n i = 0 ↔
      binCount (primeBin x J (i.val+1)) n = 0 := by
    simp only [canonicalBinVector,Fin.ext_iff,Fin.val_zero]
    omega
  constructor
  · intro h i hi
    have hi0 : 0 < i := hk.trans_le (mem_Ico.mp hi).1
    let a : Fin (J-1) := ⟨i-1,by have := (mem_Ico.mp hi).2; omega⟩
    have ha : a.val+1 = i := by dsimp [a]; omega
    have hh := (hzero a).mp (h a (by rw [ha]; exact (mem_Ico.mp hi).1))
    rwa [ha] at hh
  · intro h i hi
    apply (hzero i).mpr
    exact h (i.val+1) (mem_Ico.mpr ⟨hi,by have := i.isLt; omega⟩)

end JointDickman

end OAI
