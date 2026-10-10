import OAI.NumberTheory.Ostmann.Construction.InitialBalancedCellWeights

namespace OAI

/-! # Attach small cells after choosing the two broad cutoff centers -/
namespace Ostmann
open scoped Classical BigOperators

/-- The centers are fixed before the top and compensation priors are selected.
Their balanced masses therefore remain available when the cells depend on them. -/
theorem initial_balanced_cell_mass_at (P : Finset ℕ) (b d r m : ℕ)
    (μb : Fin b → P → ℝ) (μd : Fin d → P → ℝ) (μc : Fin r → P → ℝ)
    (gb : Fin b → P → Prop) (gd : Fin d → P → Prop) (gc : Fin r → P → Prop)
    (cb cd : ℝ)
    (hB : Real.exp (-(Real.log 2 + 2) * m) ≤
      ∑ x ∈ balancedTupleSet b gb, productPrior μb x *
        initialLogSumWeight (fun p : P => (p : ℕ)) cb x)
    (hD : Real.exp (-(Real.log 2 + 2) * m) ≤
      ∑ x ∈ balancedTupleSet d gd, productPrior μd x *
        initialLogSumWeight (fun p : P => (p : ℕ)) cd x)
    (hmc : ∀ i, ∑ p, μc i p = 1)
    (hgc : ∀ i p, μc i p ≠ 0 → gc i p) :
    Real.exp (-(2 * (Real.log 2 + 2)) * m) ≤
      ∑ x ∈ balancedTupleSet (b + (d + r)) (Fin.append gb (Fin.append gd gc)),
        productPrior (Fin.append μb (Fin.append μd μc)) x *
          (initialLogSumWeight (fun p : P => (p : ℕ)) cb (fun i => x (i.castAdd (d + r))) *
            initialLogSumWeight (fun p : P => (p : ℕ)) cd
              (fun i => x ((i.castAdd r).natAdd b))) := by
  have hcmass := balancedTupleSet_mass_one r μc gc hmc hgc
  let Bmass := ∑ x ∈ balancedTupleSet b gb, productPrior μb x *
    initialLogSumWeight (fun p : P => (p : ℕ)) cb x
  let Dmass := ∑ x ∈ balancedTupleSet d gd, productPrior μd x *
    initialLogSumWeight (fun p : P => (p : ℕ)) cd x
  let Cmass := ∑ x ∈ balancedTupleSet r gc, productPrior μc x
  change Real.exp (-(Real.log 2 + 2) * m) ≤ Bmass at hB
  change Real.exp (-(Real.log 2 + 2) * m) ≤ Dmass at hD
  change 1 ≤ Cmass at hcmass
  have hCD := balancedHalfMass_append d r μd μc gd gc
    (initialLogSumWeight (fun p : P => (p : ℕ)) cd) (fun _ => 1)
  simp only [mul_one] at hCD
  have hfull := balancedHalfMass_append b (d + r) μb (Fin.append μd μc) gb (Fin.append gd gc)
    (initialLogSumWeight (fun p : P => (p : ℕ)) cb)
    (fun y => initialLogSumWeight (fun p : P => (p : ℕ)) cd (fun i => y (i.castAdd r)))
  rw [hCD] at hfull
  rw [hfull]
  change Real.exp (-(2 * (Real.log 2 + 2)) * m) ≤ Bmass * (Dmass * Cmass)
  have hb0 : 0 ≤ Bmass := (Real.exp_nonneg _).trans hB
  have hd0 : 0 ≤ Dmass := (Real.exp_nonneg _).trans hD
  calc
    _ = Real.exp (-(Real.log 2 + 2) * m) * Real.exp (-(Real.log 2 + 2) * m) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Bmass * Dmass := mul_le_mul hB hD (Real.exp_nonneg _) hb0
    _ ≤ Bmass * (Dmass * Cmass) := by nlinarith [mul_nonneg hb0 hd0]

end Ostmann

end OAI
