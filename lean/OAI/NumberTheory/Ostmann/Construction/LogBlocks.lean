import Mathlib
import OAI.NumberTheory.Ostmann.Construction.SourcePriors

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Construction

def logBlockIndex (h : ℝ) (p : ℕ) : ℕ := ⌊Real.log p/h⌋₊
def logBlockPrimes (S : Finset ℕ) (h : ℝ) (j : ℕ) : Finset ℕ :=
  S.filter (fun p => logBlockIndex h p=j)
def logBlockMass (S : Finset ℕ) (h : ℝ) (j : ℕ) : ℝ :=
  ∑p∈logBlockPrimes S h j, Real.log p/(p:ℝ)

lemma logBlock_lower {S : Finset ℕ} {h : ℝ} (hh : 0<h) {j p : ℕ}
    (hp : p∈logBlockPrimes S h j) : (j:ℝ)*h≤Real.log p := by
  have hi := (Finset.mem_filter.mp hp).2
  rw [← hi]
  unfold logBlockIndex
  have hf := Nat.floor_le (div_nonneg (Real.log_natCast_nonneg p) hh.le)
  have hm := mul_le_mul_of_nonneg_right hf hh.le
  simpa only [div_mul_cancel₀ _ hh.ne'] using hm

lemma logBlock_upper {S : Finset ℕ} {h : ℝ} (hh : 0<h) {j p : ℕ}
    (hp : p∈logBlockPrimes S h j) : Real.log p<((j:ℝ)+1)*h := by
  have hi := (Finset.mem_filter.mp hp).2
  have hf := Nat.lt_floor_add_one (Real.log p/h)
  change Real.log p/h < (logBlockIndex h p:ℝ)+1 at hf
  rw [hi] at hf
  exact (div_lt_iff₀ hh).mp hf

theorem harmonicPrimeMass_le_of_logBlocks (S : Finset ℕ) (h a : ℝ) (N : ℕ)
    (hh : 0<h) (hindex : ∀p∈S,logBlockIndex h p∈Finset.Icc 1 N)
    (hblocks : ∀j∈Finset.Icc 1 N,logBlockMass S h j≤a*h) :
    harmonicPrimeMass S≤a*(harmonic N:ℝ) := by
  have hsum : harmonicPrimeMass S=
      ∑j∈Finset.Icc 1 N,∑p∈logBlockPrimes S h j,(1:ℝ)/p := by
    exact (Finset.sum_fiberwise_of_maps_to hindex (fun p : ℕ => (1:ℝ)/p)).symm
  rw [hsum]
  have hle (j : ℕ) (hj : j∈Finset.Icc 1 N) :
      (∑p∈logBlockPrimes S h j,(1:ℝ)/p)≤a/(j:ℝ) := by
    have hj0 : (0:ℝ)<j := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hj).1)
    have hjh : 0<(j:ℝ)*h := mul_pos hj0 hh
    calc
      _ ≤ (∑p∈logBlockPrimes S h j,Real.log p/(p:ℝ))/((j:ℝ)*h) := by
        rw [Finset.sum_div]
        apply Finset.sum_le_sum
        intro p hp
        apply (le_div_iff₀ hjh).mpr
        have hl := div_le_div_of_nonneg_right (logBlock_lower hh hp) (Nat.cast_nonneg p)
        simpa only [one_div,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,mul_one] using hl
      _ ≤ (a*h)/((j:ℝ)*h) := div_le_div_of_nonneg_right (hblocks j hj) hjh.le
      _ = a/(j:ℝ) := by field_simp
  calc
    _ ≤ ∑j∈Finset.Icc 1 N,a/(j:ℝ) := Finset.sum_le_sum hle
    _ = a*(harmonic N:ℝ) := by
      simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,
        Finset.mul_sum,div_eq_mul_inv]

theorem exists_logBlock_mass_gt (S : Finset ℕ) (h a : ℝ) (N : ℕ)
    (hh : 0<h) (hindex : ∀p∈S,logBlockIndex h p∈Finset.Icc 1 N)
    (hmass : a*(harmonic N:ℝ)<harmonicPrimeMass S) :
    ∃j∈Finset.Icc 1 N,a*h<logBlockMass S h j := by
  by_contra hn
  push Not at hn
  exact (not_le_of_gt hmass) (harmonicPrimeMass_le_of_logBlocks S h a N hh hindex hn)

end Ostmann.Construction

end

end OAI
