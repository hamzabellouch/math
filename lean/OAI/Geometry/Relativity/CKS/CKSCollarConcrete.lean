import OAI.Geometry.Relativity.CKS.CollarSourceParams

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix CKSAngularSlice
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

theorem cks_actual_collar_coordinate_DEC {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, Matrix.PosDef (fun i k => (q i k).1.1))
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (R : ℝ) (f : TensorFields) (ρ : ℝ) (x : AP),
      R₀ ≤ R → R ≤ Real.exp ρ → Real.exp ρ ≤ 3*R → f.RegularAt (slice ρ x) →
      ContDiffAt ℝ 3 f.base.mK (slice ρ x) → ContDiffAt ℝ 3 f.base.ek (slice ρ x) →
      (∀ᶠ y in 𝓝 (slice ρ x), (logMetric f.base y).PosDef) →
      matrixThreeJets f.base.sigma (slice ρ x) ∈ K → f.LogComponentBound B (slice ρ x) →
      CKSAngularGeometry.coordinateDEC
        (CKSAngularGeometry.fieldNullInput (CKSAngularGeometry.oldParams (CKSBending.collarParams R (Real.exp ρ)))
          ((sourceCollarData f).angular ρ) x) (Real.exp ρ) →
      CKSAngularGeometry.coordinateDEC
        (CKSAngularGeometry.fieldNullInput (CKSBending.collarParams R (Real.exp ρ))
          ((sourceCollarData f).angular ρ) x) (Real.exp ρ) := by
  obtain ⟨A,hA,hparams⟩ := CKSBending.collarParams_weighted
  obtain ⟨R₀,hR₀,hh⟩ := cks_coordinate_collar_DEC hK hreg hB
    (zero_le_one.trans hA) (zero_le_one.trans hA)
  refine ⟨R₀,hR₀,?_⟩
  intro R f ρ x hR hr htop hf hmk hek hp hs hb hold
  obtain ⟨hweight,hnorm⟩ := hparams R (Real.exp ρ) (hR₀.trans hR) hr htop
  apply hh f ρ x (hR.trans hr) hf hmk hek hp hs hb _ hnorm rfl
    (CKSBending.paddingWeight_nonneg R (Real.exp ρ)) hweight hold

end
end CKSMixedGeometry

end

end OAI
