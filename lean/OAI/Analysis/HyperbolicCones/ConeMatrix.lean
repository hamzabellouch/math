import OAI.Analysis.HyperbolicCones.MatrixPositive

namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder

namespace Paper256

def symInverse {n : ℕ} (X : Sym n) : Sym n :=
  ⟨(X : Mat n ℝ)⁻¹, Matrix.IsHermitian.inv X.property⟩

def phiSym (y : Fin 3 → ℝ) (X : Sym 4) : Sym 4 :=
  ⟨phi y (X : Mat 4 ℝ), phi_isHermitian y _ X.property⟩

def coneResidual (X Z : Sym 4) (y : Fin 3 → ℝ) (t : ℝ) : Sym 4 :=
  Z + t • 1 - phiSym y (symInverse (X + t • 1))

theorem continuousAt_symInverse {n : ℕ} (X : Sym n)
    (hX : IsUnit (X : Mat n ℝ)) : ContinuousAt symInverse X := by
  have hd : (X : Mat n ℝ).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp hX).ne_zero
  have hi : ContinuousAt Inv.inv (X : Mat n ℝ) :=
    continuousAt_matrix_inv _ (by
      simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hd))
  apply tendsto_subtype_rng.mpr
  exact hi.comp (f := fun H : Sym n => (H : Mat n ℝ)) (x := X)
    continuous_subtype_val.continuousAt

theorem continuous_phiSym (y : Fin 3 → ℝ) : Continuous (phiSym y) := by
  exact ((phiLinear y).continuous_of_finiteDimensional.comp continuous_subtype_val).subtype_mk _

theorem positive_shift {n : ℕ} (X : Sym n) (hX : (X : Mat n ℝ).PosDef)
    (t : ℝ) (ht : 0 ≤ t) : ((X + t • 1 : Sym n) : Mat n ℝ).PosDef :=
  hX.add_posSemidef (Matrix.PosSemidef.one.smul ht)

theorem continuousAt_coneResidual (X Z : Sym 4) (y : Fin 3 → ℝ) (t : ℝ)
    (ht : ((X + t • 1 : Sym 4) : Mat 4 ℝ).PosDef) :
    ContinuousAt (coneResidual X Z y) t := by
  have hX : Continuous (fun s : ℝ => X + s • (1 : Sym 4)) := by fun_prop
  have hZ : Continuous (fun s : ℝ => Z + s • (1 : Sym 4)) := by fun_prop
  have hi : ContinuousAt (fun s : ℝ => symInverse (X + s • (1 : Sym 4))) t :=
    (continuousAt_symInverse _ ht.isUnit).comp
      (f := fun s : ℝ => X + s • (1 : Sym 4)) hX.continuousAt
  exact hZ.continuousAt.sub ((continuous_phiSym y).continuousAt.comp hi)

theorem continuousOn_coneResidual (X Z : Sym 4) (y : Fin 3 → ℝ)
    (hX : (X : Mat 4 ℝ).PosDef) : ContinuousOn (coneResidual X Z y) (Ici 0) := by
  intro t ht
  exact (continuousAt_coneResidual X Z y t (positive_shift X hX t ht)).continuousWithinAt

end Paper256

end

end OAI
