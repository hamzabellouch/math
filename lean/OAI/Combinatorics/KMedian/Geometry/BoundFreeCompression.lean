import Mathlib
import OAI.Combinatorics.KMedian.Compression.ComputedCompression
import OAI.Combinatorics.KMedian.Compression.IntegerRationalCompression

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

theorem exists_feature_bound {n d : ℕ} (v : Fin n → Fin d → ℤ) :
    ∃ L : ℕ, ∀ i j, |v i j| ≤ (2:ℤ)^L := by
  let L := ∑ i, ∑ j, (v i j).natAbs
  refine ⟨L,?_⟩
  intro i j
  have h1 : (v i j).natAbs ≤ ∑ j, (v i j).natAbs :=
    single_le_sum (f:=fun (j : Fin d) => (v i j).natAbs) (fun _ _ => Nat.zero_le _) (mem_univ j)
  have h2 : (∑ j, (v i j).natAbs) ≤ L :=
    single_le_sum (f:=fun (i : Fin n) => ∑ j, (v i j).natAbs) (fun _ _ => Nat.zero_le _) (mem_univ i)
  have hn : (v i j).natAbs ≤ L := h1.trans h2
  have hh := hn.trans (Nat.lt_two_pow_self (n:=L)).le
  have hh' : ((v i j).natAbs:ℤ) ≤ (2:ℤ)^L := by exact_mod_cast hh
  simpa only [Int.natCast_natAbs] using hh'

def compressionStepAuto {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℤ) (hsize : d+1 < μ.support.card) : IntegerLaw (Fin n) :=
  let z := computedAffineKernel μ v
  have hz : (∃ i, z i ≠ 0) ∧ (∑ i, z i=0) := by
    obtain ⟨L,hL⟩ := exists_feature_bound v
    have h := computedAffineKernel_spec μ v L hL hsize
    exact ⟨h.1,h.2.1⟩
  have hP := positiveSet_nonempty z hz.2 hz.1
  let p := computedPivot μ z hP
  have hp := computedPivot_spec μ z hP
  eliminateAt μ z p hp.1 hp.2 hz.2

theorem compressionStepAuto_eq {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℤ) (L : ℕ) (hv : ∀ i j, |v i j| ≤ (2:ℤ)^L)
    (hsize : d+1 < μ.support.card) :
    compressionStepAuto μ v hsize=compressionStep μ v L hv hsize := rfl

def compressStepsAuto {n d : ℕ} (v : Fin n → Fin d → ℤ) :
    ℕ → IntegerLaw (Fin n) → IntegerLaw (Fin n)
  | 0,μ => μ
  | t+1,μ => if h : d+1 < μ.support.card then
      compressStepsAuto v t (compressionStepAuto μ v h) else μ

theorem compressStepsAuto_eq {n d : ℕ} (v : Fin n → Fin d → ℤ)
    (L : ℕ) (hv : ∀ i j, |v i j| ≤ (2:ℤ)^L) (t : ℕ) (μ : IntegerLaw (Fin n)) :
    compressStepsAuto v t μ=compressSteps v L hv t μ := by
  induction t generalizing μ with
  | zero => rfl
  | succ t ih =>
    simp only [compressStepsAuto,compressSteps]
    split_ifs with h
    · rw [compressionStepAuto_eq μ v L hv h,ih]
    · rfl

def compressAuto {n d : ℕ} (μ : IntegerLaw (Fin n)) (v : Fin n → Fin d → ℚ) :
    IntegerLaw (Fin n) :=
  compressStepsAuto (RationalLaw.scaledFeatures v) n μ

theorem compressAuto_eq {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℚ) (L : ℕ)
    (hnum : ∀ i j, |(v i j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i j, ((v i j).den:ℤ) ≤ (2:ℤ)^L) :
    μ.compressAuto v=μ.compressRational v L hnum hden :=
  compressStepsAuto_eq _ _ (RationalLaw.scaledFeatures_bound v L hnum hden) n μ

theorem compressAuto_spec {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℚ) (L : ℕ)
    (hnum : ∀ i j, |(v i j).num| ≤ (2:ℤ)^L)
    (hden : ∀ i j, ((v i j).den:ℤ) ≤ (2:ℤ)^L) :
    let ν := μ.compressAuto v
    ν.denominator ≤ μ.denominator*(2:ℤ)^(((2*(d+1)*(d+1+L*(n+1)))*(n+1))*n) ∧
      ν.support ⊆ μ.support ∧ ν.support.card ≤ d+1 ∧
      ∀ j, (∑ i, ν.rational.weight i*v i j)=∑ i, μ.rational.weight i*v i j := by
  rw [compressAuto_eq μ v L hnum hden]
  exact compressRational_spec μ v L hnum hden

theorem exists_rational_feature_bound {n d : ℕ} (v : Fin n → Fin d → ℚ) :
    ∃ L : ℕ, (∀ i j, |(v i j).num| ≤ (2:ℤ)^L) ∧
      (∀ i j, ((v i j).den:ℤ) ≤ (2:ℤ)^L) := by
  obtain ⟨A,hA⟩ := exists_feature_bound (fun i j => (v i j).num)
  obtain ⟨B,hB⟩ := exists_feature_bound (fun i j => ((v i j).den:ℤ))
  refine ⟨max A B,fun i j => (hA i j).trans ?_,fun i j => ?_⟩
  · exact pow_le_pow_right₀ (by norm_num) (le_max_left _ _)
  · exact (le_abs_self _).trans ((hB i j).trans
      (pow_le_pow_right₀ (by norm_num) (le_max_right _ _)))

theorem compressAuto_correct {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℚ) :
    let ν := μ.compressAuto v
    ν.support ⊆ μ.support ∧ ν.support.card ≤ d+1 ∧
      ∀ j, (∑ i, ν.rational.weight i*v i j)=∑ i, μ.rational.weight i*v i j := by
  obtain ⟨L,hnum,hden⟩ := exists_rational_feature_bound v
  exact (compressAuto_spec μ v L hnum hden).2

end MetricKMedian.IntegerLaw

end OAI
