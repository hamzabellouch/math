import OAI.Analysis.HyperbolicCones.PencilKernel
import OAI.Analysis.HyperbolicCones.PencilTopology

namespace OAI

noncomputable section

open Set Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder

namespace Paper256

theorem positiveLinearMap_monotone {m n : ℕ} (D : Sym m →ₗ[ℝ] Sym n)
    (hD : ∀ X : Sym m, (X : Mat m ℝ).PosSemidef → (D X : Mat n ℝ).PosSemidef)
    (X Y : Sym m) (hXY : (X : Mat m ℝ) ≤ (Y : Mat m ℝ)) :
    (D X : Mat n ℝ) ≤ (D Y : Mat n ℝ) := by
  have h := hD (Y - X) hXY
  change ((D Y : Mat n ℝ) - (D X : Mat n ℝ)).PosSemidef
  simpa using h

theorem positive_unital_map_posDef {m n : ℕ} (D : Sym m →ₗ[ℝ] Sym n)
    (hD : ∀ X : Sym m, (X : Mat m ℝ).PosSemidef → (D X : Mat n ℝ).PosSemidef)
    (hI : D 1 = 1) (X : Sym m) (hX : (X : Mat m ℝ).PosDef) :
    (D X : Mat n ℝ).PosDef := by
  obtain ⟨c, hc, hcX⟩ := posDef_scalar_lower_bound (X : Mat m ℝ) hX
  apply posDef_of_scalar_lower_bound hc
  have h := positiveLinearMap_monotone D hD (c • 1) X hcX
  simpa [hI] using h

theorem positiveLinearMap_common_kernel {m n : ℕ} (D : Sym m →ₗ[ℝ] Sym n)
    (hD : ∀ X : Sym m, (X : Mat m ℝ).PosSemidef → (D X : Mat n ℝ).PosSemidef)
    (X : Sym m) (v : Fin n → ℝ) (hv : (D 1 : Mat n ℝ) *ᵥ v = 0) :
    (D X : Mat n ℝ) *ᵥ v = 0 := by
  have hI : (1 : Sym m) ∈ interior {Y : Sym m | (Y : Mat m ℝ).PosDef} := by
    rw [(isOpen_posDef m).interior_eq]
    exact Matrix.PosDef.one
  obtain ⟨ε, hε, hp, hm⟩ := interior_line_pair hI X
  have hp' := hD (1 + ε • X) hp.posSemidef
  have hm' := hD (1 - ε • X) hm.posSemidef
  have hz : (ε • (D X : Mat n ℝ)) *ᵥ v = 0 := by
    apply posSemidef_pair_kernel (A := (D 1 : Mat n ℝ)) _ _ v hv
    · simpa using hp'
    · simpa using hm'
  rw [smul_mulVec] at hz
  exact (smul_eq_zero.mp hz).resolve_left hε.ne'

end Paper256

end

end OAI
