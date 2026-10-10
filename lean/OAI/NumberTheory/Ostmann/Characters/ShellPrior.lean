import OAI.NumberTheory.Ostmann.Construction.FiniteTransfer
import OAI.NumberTheory.Ostmann.Construction.WeightedSelection
import OAI.NumberTheory.Ostmann.Preliminaries.PrimeSums

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters
open Construction Preliminaries

def primeShellMass {Q:ℕ} (E:Finset (PrimeUpTo Q)) : ℝ := ∑p∈E,(p.val:ℝ)⁻¹

def primeShellPrior {Q:ℕ} (E:Finset (PrimeUpTo Q)) (hE:0<primeShellMass E) :
    FinitePrior (PrimeUpTo Q) :=
  FinitePrior.fromWeights (fun p=>if p∈E then (p.val:ℝ)⁻¹ else 0)
    (fun p=>by split_ifs <;> positivity)
    (by simpa only [Finset.sum_ite_mem, Finset.univ_inter, primeShellMass] using hE)

theorem primeShellPrior_mass {Q:ℕ} (E:Finset (PrimeUpTo Q)) (hE:0<primeShellMass E)
    (p:PrimeUpTo Q) :
    (primeShellPrior E hE).mass p=(if p∈E then (p.val:ℝ)⁻¹ else 0)/primeShellMass E := by
  simp only [primeShellPrior, FinitePrior.fromWeights, Finset.sum_ite_mem,
    Finset.univ_inter, primeShellMass]

theorem primeShellPrior_mass_le {Q:ℕ} (E:Finset (PrimeUpTo Q)) (hE:0<primeShellMass E)
    (L:ℝ) (hL:0<L) (hscale:∀p∈E,L≤Real.log p.val) (p:PrimeUpTo Q) :
    (primeShellPrior E hE).mass p≤
      (primeShellMass E*L)⁻¹*(Real.log p.val/p.val) := by
  rw [primeShellPrior_mass]
  by_cases hp:p∈E
  · rw [ite_eq_left hp]
    have hpr : (0:ℝ)<p.val := by exact_mod_cast (primeUpTo_prime p).pos
    have hid : (p.val:ℝ)⁻¹/primeShellMass E=
        (primeShellMass E*L)⁻¹*(L/p.val) := by field_simp
    rw [hid]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hscale p hp) hpr.le)
      (by positivity)
  · rw [ite_eq_right hp,zero_div]
    have hlog : 0≤Real.log p.val := Real.log_nonneg
      (by exact_mod_cast (primeUpTo_prime p).one_le)
    positivity

theorem primeShellPrior_error_le {Q:ℕ} (E:Finset (PrimeUpTo Q)) (hE:0<primeShellMass E)
    (L:ℝ) (hL:0<L) (hscale:∀p∈E,L≤Real.log p.val)
    (e:PrimeUpTo Q→ℂ) (B:ℝ)
    (hbound:(∑p:PrimeUpTo Q,(Real.log p.val/p.val)*‖e p‖^2)≤B) :
    (primeShellPrior E hE).mean (fun p=>‖e p‖^2)≤(primeShellMass E*L)⁻¹*B := by
  calc
    _ ≤ ∑p:PrimeUpTo Q,((primeShellMass E*L)⁻¹*(Real.log p.val/p.val))*‖e p‖^2 := by
      exact Finset.sum_le_sum (fun p _=>mul_le_mul_of_nonneg_right
        (primeShellPrior_mass_le E hE L hL hscale p) (sq_nonneg _))
    _ = (primeShellMass E*L)⁻¹*(∑p:PrimeUpTo Q,(Real.log p.val/p.val)*‖e p‖^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by positivity)

end Ostmann.Characters

end

end OAI
