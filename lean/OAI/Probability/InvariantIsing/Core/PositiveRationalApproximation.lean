import OAI.Probability.InvariantIsing.Cavity.CavityCanonicalMass
import Mathlib.Algebra.Order.Floor.Semiring

namespace OAI

/-! Positive rational approximations to a finite probability vector,
with explicit integer multiplicities. -/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace InvariantIsing

def positiveApproxCount (x : ℝ) (k : ℕ) : ℕ := ⌊(k+1 : ℝ)*x⌋₊+1

lemma positiveApproxCount_pos (x : ℝ) (k : ℕ) : 0 < positiveApproxCount x k := by
  unfold positiveApproxCount
  omega

lemma positiveApproxCount_ratio (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun k => (positiveApproxCount x k : ℝ)/(k+1)) atTop (𝓝 x) := by
  have herror k : 0 ≤ (positiveApproxCount x k : ℝ)/(k+1)-x ∧
      (positiveApproxCount x k : ℝ)/(k+1)-x ≤ 1/(k+1) := by
    have hk : 0 < (k+1 : ℝ) := by positivity
    have hlow := Nat.lt_floor_add_one ((k+1 : ℝ)*x)
    have hupp := Nat.floor_le (mul_nonneg hk.le hx)
    have heq : (positiveApproxCount x k : ℝ)/(k+1)-x=
        (((⌊(k+1 : ℝ)*x⌋₊ : ℕ) : ℝ)+1-x*(k+1))/(k+1) := by
      simp only [positiveApproxCount,Nat.cast_add,Nat.cast_one]
      field_simp
    rw [heq]
    constructor
    · apply div_nonneg _ hk.le
      nlinarith
    · apply div_le_div_of_nonneg_right _ hk.le
      nlinarith
  have he := squeeze_zero (fun k => (herror k).1) (fun k => (herror k).2)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [sub_add_cancel,zero_add] using he.add_const x

def positiveApproxDenominator {m : ℕ} (ρ : Fin m → ℝ) (k : ℕ) : ℕ :=
  ∑ a, positiveApproxCount (ρ a) k

lemma positiveApproxDenominator_pos {m : ℕ} (hm : 0 < m) (ρ : Fin m → ℝ) (k : ℕ) :
    0 < positiveApproxDenominator ρ k := by
  have hle := Finset.single_le_sum (f := fun a => positiveApproxCount (ρ a) k)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨0,hm⟩ : Fin m))
  exact (positiveApproxCount_pos (ρ ⟨0,hm⟩) k).trans_le hle

lemma positiveApproxWeights_tendsto {m : ℕ} (ρ : Fin m → ℝ)
    (hρ : ∀ a, 0 ≤ ρ a) (hsum : ∑ a, ρ a=1) :
    Tendsto (fun k a => (positiveApproxCount (ρ a) k : ℝ)/positiveApproxDenominator ρ k)
      atTop (𝓝 ρ) := by
  have hden : Tendsto (fun k => (positiveApproxDenominator ρ k : ℝ)/(k+1)) atTop (𝓝 (1:ℝ)) := by
    have hh := tendsto_finsetSum Finset.univ (fun a _ => positiveApproxCount_ratio (ρ a) (hρ a))
    simpa only [positiveApproxDenominator,Nat.cast_sum,Finset.sum_div,hsum] using hh
  apply tendsto_pi_nhds.mpr
  intro a
  have hh := (positiveApproxCount_ratio (ρ a) (hρ a)).div hden one_ne_zero
  simp only [div_one] at hh
  apply hh.congr
  intro k
  exact div_div_div_cancel_right₀ (by positivity : (k+1 : ℝ)≠0) _ _

def positiveApproxWeights {m : ℕ} (ρ : Fin m → ℝ) (k : ℕ) (a : Fin m) : ℝ :=
  (positiveApproxCount (ρ a) k : ℝ)/positiveApproxDenominator ρ k

lemma positiveApproxWeights_pos {m : ℕ} (hm : 0 < m) (ρ : Fin m → ℝ) (k : ℕ) (a : Fin m) :
    0 < positiveApproxWeights ρ k a :=
  div_pos (by exact_mod_cast positiveApproxCount_pos (ρ a) k)
    (by exact_mod_cast positiveApproxDenominator_pos hm ρ k)

lemma positiveApproxWeights_sum {m : ℕ} (hm : 0 < m) (ρ : Fin m → ℝ) (k : ℕ) :
    ∑ a, positiveApproxWeights ρ k a=1 := by
  simp only [positiveApproxWeights,← Finset.sum_div,← Nat.cast_sum]
  exact div_self (Nat.cast_ne_zero.mpr (positiveApproxDenominator_pos hm ρ k).ne')

end InvariantIsing

end

end OAI
