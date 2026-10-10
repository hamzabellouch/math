import OAI.Analysis.LipschitzHilbert.Trees.SourceTreeCells
import Mathlib.Analysis.PSeries

namespace OAI

/-! The remaining transverse tail in the long-tree density estimate:
412 powers in squared energy absorb twice the density loss 203, leaving
the summable sixth power. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

/-- The transverse tail left by the fixed manuscript exponents is summable. -/
theorem summable_transverse_sixth :
    Summable (fun n : ℤ => ((1+|(n:ℝ)|)^6)⁻¹) := by
  have hs : Summable (fun n : ℕ => (((n:ℝ)+1)^6)⁻¹) := by
    have h := (summable_nat_add_iff (f:=fun n : ℕ => ((n:ℝ)^6)⁻¹) 1).mpr
      (Real.summable_nat_pow_inv.mpr (by norm_num : 1<(6:ℕ)))
    simpa only [Nat.cast_add,Nat.cast_one] using h
  have ha (n : ℕ) : |(n:ℝ)|=(n:ℝ) := abs_of_nonneg n.cast_nonneg
  apply Summable.of_nat_of_neg
  · simpa only [Int.cast_natCast,ha,add_comm] using hs
  · simpa only [Int.cast_neg,Int.cast_natCast,abs_neg,ha,add_comm] using hs

def transverseTailConstant : ℝ := ∑' n : ℤ, ((1+|(n:ℝ)|)^6)⁻¹

theorem transverseTailConstant_nonneg : 0≤transverseTailConstant :=
  tsum_nonneg (fun _ => by positivity)

theorem finite_transverse_tail (s : Finset ℤ) :
    ∑ n∈s, ((1+|(n:ℝ)|)^6)⁻¹≤transverseTailConstant :=
  summable_transverse_sixth.sum_le_tsum s (fun _ _ => by positivity)

/-- Weighted Cauchy--Schwarz with exactly the exponents needed by the
cell-density and polynomial-energy estimates. -/
theorem transverse_density_cauchy {J : Type*} (s : Finset J)
    (A m w : J → ℝ) (hm : ∀ j∈s, 0≤m j) (hw : ∀ j∈s, 0<w j) :
    (∑ j∈s, A j*m j*(w j)^203)^2≤
      (∑ j∈s, (A j)^2*m j*(w j)^412)*(∑ j∈s, m j/(w j)^6) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun j hj => mul_nonneg (mul_nonneg (sq_nonneg _) (hm j hj)) (pow_nonneg (hw j hj).le _))
    (fun j hj => div_nonneg (hm j hj) (pow_nonneg (hw j hj).le _))
  intro j hj
  apply le_of_eq
  have hw0 : (w j)^6≠0 := pow_ne_zero _ (hw j hj).ne'
  have hp : (w j)^412/(w j)^6=(w j)^406 := by
    rw [show (412:ℕ)=406+6 by omega,pow_add,mul_div_cancel_right₀ _ hw0]
  calc
    (A j*m j*(w j)^203)^2=(A j)^2*(m j)^2*(w j)^406 := by
      rw [mul_pow,mul_pow,←pow_mul]
    _ = (A j)^2*(m j)^2*((w j)^412/(w j)^6) := by rw [hp]
    _ = _ := by ring

/-- Density mass times the actual supremum is controlled by weighted
energy and the summable volume tail. -/
theorem finite_density_supremum_sum {J : Type*} (s : Finset J)
    (A d m w : J → ℝ) (D E V : ℝ)
    (hA : ∀ j∈s, 0≤A j) (hd : ∀ j∈s, 0≤d j)
    (hm : ∀ j∈s, 0≤m j) (hw : ∀ j∈s, 0<w j)
    (hE : 0≤E)
    (hmass : ∀ j∈s, d j≤D*(w j)^203*m j)
    (henergy : (∑ j∈s, (A j)^2*m j*(w j)^412)≤E)
    (hvolume : (∑ j∈s, m j/(w j)^6)≤V) :
    (∑ j∈s, A j*d j)^2≤D^2*E*V := by
  have hsum : (∑ j∈s, A j*d j)≤D*∑ j∈s, A j*m j*(w j)^203 := by
    calc
      _ ≤ ∑ j∈s, A j*(D*(w j)^203*m j) :=
        Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_left (hmass j hj) (hA j hj))
      _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  have hs0 : 0≤∑ j∈s, A j*d j :=
    Finset.sum_nonneg (fun j hj => mul_nonneg (hA j hj) (hd j hj))
  have hc := transverse_density_cauchy s A m w hm hw
  have hEV : (∑ j∈s, A j*m j*(w j)^203)^2≤E*V :=
    hc.trans (mul_le_mul henergy hvolume
      (Finset.sum_nonneg (fun j hj => div_nonneg (hm j hj) (pow_nonneg (hw j hj).le _))) hE)
  calc
    _ ≤ (D*∑ j∈s, A j*m j*(w j)^203)^2 := pow_le_pow_left₀ hs0 hsum 2
    _ = D^2*(∑ j∈s, A j*m j*(w j)^203)^2 := mul_pow _ _ _
    _ ≤ D^2*(E*V) := mul_le_mul_of_nonneg_left hEV (sq_nonneg D)
    _ = _ := by ring

namespace SourceWhitney
open DyadicLineGrid

/-- For any finite family of small Whitney intervals, the entire
transverse tail has a uniform volume budget. -/
theorem finite_whitney_transverse_budget {ι : Type*} (tiles : Finset ι)
    (x ell : ι → ℝ) (c L W : ℝ) (hL : 0≤L) (hW : 0≤W)
    (hcenters : ∀ i∈tiles, |x i-c|≤L/2)
    (S : Finset (ℤ×ℤ)) (T : Finset ℤ)
    (hWhitney : ∀ p∈S, Whitney tiles x ell p.1 p.2)
    (hscale : ∀ p∈S, scale p.1≤L) :
    (∑ p∈S×ˢT, (scale p.1.1*W)/(1+|(p.2:ℝ)|)^6)≤
      9*L*W*transverseTailConstant := by
  have hS := small_length_budget tiles x ell hL hcenters S hWhitney hscale
  have hT := finite_transverse_tail T
  calc
    _ = (∑ p∈S, scale p.1)*W*(∑ n∈T, ((1+|(n:ℝ)|)^6)⁻¹) := by
      rw [Finset.sum_product,Finset.sum_mul,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [div_eq_mul_inv]
    _ ≤ (9*L)*W*transverseTailConstant := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hS hW) hT
        (Finset.sum_nonneg (fun _ _ => by positivity))
        (mul_nonneg (mul_nonneg (by norm_num) hL) hW)
    _ = _ := by ring

end SourceWhitney
end LipschitzHilbert

end

end OAI
