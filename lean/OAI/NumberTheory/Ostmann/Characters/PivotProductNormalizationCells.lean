import OAI.NumberTheory.Ostmann.Characters.PivotProductNormalization

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.PivotProductNormalization
open Construction Preliminaries PivotProductFibers

theorem cell_lower_to_exp {Z c width β L : ℝ} (hc : 0 < c) (hw : 0 < width)
    (hZ : c/width ≤ Z) (hwidth : width ≤ Real.exp (β*L))
    (hL : -Real.log c ≤ L) : Real.exp (-((β+1)*L)) ≤ Z := by
  have hc' : Real.exp (-L) ≤ c := by
    rw [←Real.exp_log hc]
    exact Real.exp_le_exp.mpr (by linarith)
  have hi : Real.exp (-(β*L)) ≤ width⁻¹ := by
    simpa only [Real.exp_neg] using inv_anti₀ hw hwidth
  calc
    Real.exp (-((β+1)*L)) = Real.exp (-L)*Real.exp (-(β*L)) := by
      rw [←Real.exp_add]
      congr 1
      ring
    _ ≤ c*width⁻¹ := mul_le_mul hc' hi (Real.exp_pos _).le hc.le
    _ = c/width := (div_eq_mul_inv _ _).symm
    _ ≤ Z := hZ

theorem primeShellMass_exp_lower {Q : ℕ} (E : Finset (PrimeUpTo Q))
    {c width β L : ℝ} (hc : 0 < c) (hw : 0 < width)
    (hZ : c/width ≤ primeShellMass E) (hwidth : width ≤ Real.exp (β*L))
    (hL : -Real.log c ≤ L) : Real.exp (-((β+1)*L)) ≤ primeShellMass E :=
  cell_lower_to_exp hc hw hZ hwidth hL

theorem factor_le_exp_of_cells {Q n : ℕ} (E : Fin n → Finset (PrimeUpTo Q))
    (c width β : Fin n → ℝ) (L : ℝ)
    (hc : ∀i,0 < c i) (hw : ∀i,0 < width i)
    (hZ : ∀i,c i/width i ≤ primeShellMass (E i))
    (hwidth : ∀i,width i ≤ Real.exp (β i*L))
    (hL : ∀i,-Real.log (c i) ≤ L) :
    (n.factorial:ℝ)*normalization E ≤
      Real.exp (Real.log (n.factorial:ℝ)+L*∑i,(β i+1)) := by
  have h := factor_le_exp E (fun i => (β i+1)*L)
    (fun i => primeShellMass_exp_lower (E i) (hc i) (hw i) (hZ i) (hwidth i) (hL i))
  simpa only [Finset.mul_sum,mul_comm] using h

theorem factor_le_exp_of_uniform_cells {Q n : ℕ} (E : Fin n → Finset (PrimeUpTo Q))
    (c : ℝ) (width : Fin n → ℝ) (β L : ℝ) (hc : 0 < c)
    (hw : ∀i,0 < width i) (hZ : ∀i,c/width i ≤ primeShellMass (E i))
    (hwidth : ∀i,width i ≤ Real.exp (β*L)) (hL : -Real.log c ≤ L) :
    (n.factorial:ℝ)*normalization E ≤
      Real.exp ((β+1)*(n:ℝ)*L+Real.log (n.factorial:ℝ)) :=
  factor_le_exp_uniform E (β+1) L
    (fun i => primeShellMass_exp_lower (E i) hc (hw i) (hZ i) (hwidth i) hL)

theorem factor_le_exp_of_uniform_cells_count {Q n : ℕ}
    (E : Fin n → Finset (PrimeUpTo Q)) (c : ℝ) (width : Fin n → ℝ) (β L : ℝ)
    (hc : 0 < c) (hβ : 0 ≤ β+1) (hL0 : 0 ≤ L)
    (hw : ∀i,0 < width i) (hZ : ∀i,c/width i ≤ primeShellMass (E i))
    (hwidth : ∀i,width i ≤ Real.exp (β*L)) (hL : -Real.log c ≤ L)
    (N : ℕ) (hn : n ≤ N) :
    (n.factorial:ℝ)*normalization E ≤
      Real.exp ((β+1)*(N:ℝ)*L+Real.log (N.factorial:ℝ)) :=
  factor_le_exp_of_count_bound E (β+1) L hβ hL0
    (fun i => primeShellMass_exp_lower (E i) hc (hw i) (hZ i) (hwidth i) hL) N hn

end Ostmann.Characters.PivotProductNormalization

end

end OAI
