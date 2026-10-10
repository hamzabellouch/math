import OAI.Geometry.Relativity.CKS.MixedMassCompact
import OAI.Geometry.Relativity.CKS.MixedInputBounds

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

theorem cks_normalized_mass_mixed {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1.1) ≠ 0)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ f : MassFields, ∀ x : Point,
      R₀ ≤ Real.exp (x 0) → f.RegularAt x → matrixThreeJets f.sigma x ∈ K →
      ‖matrixThreeJets f.sigma x‖ ≤ B → ‖matrixThreeJets f.mg x‖ ≤ B →
      ‖matrixThreeJets f.eg x‖ ≤ B/Real.exp (x 0)^2 →
      ‖matrixScalarJets f.mK x‖ ≤ B → ‖matrixScalarJets f.ek x‖ ≤ B/Real.exp (x 0)^2 →
      ‖fun a => actualThreeJet (fun y => f.b y a) x‖ ≤ B/Real.exp (x 0)^3 →
      ‖actualScalarJet f.mr x‖ ≤ B → ‖actualScalarJet f.err x‖ ≤ B/Real.exp (x 0)^6 →
      determinant (cksQField (radiusPower (-1)) (normalizeMassLogFields f) x) ≠ 0 →
      1+(radiusPower (-1) x)^3*cksVField (radiusPower (-1)) (normalizeMassLogFields f) x ≠ 0 →
      ‖actualScalarJet (cksFField (radiusPower (-1)) (normalizeMassLogFields f)) x-
        actualScalarJet (cksLeadingField f) x‖ ≤ C/Real.exp (x 0) := by
  obtain ⟨R,hR,C,hC,hh⟩ := cks_mass_uniform_bounded hK hreg (216*B)
  refine ⟨R,hR,C,hC,?_⟩
  intro f x hr hf hσ hs hmg heg hmk hek hb hmr herr h0 hV
  have hn := normalizeMassLogFields_regular hf
  have hz := radiusPower_diff (-1) 3 x
  have hσ0 : determinant (f.sigma x) ≠ 0 := hreg _ hσ
  have hnB := normalized_log_mass_input_bound hB hf hs hmg heg hmk hek hb hmr herr
  rw [cksFField_realized hz hn h0 hV,cksLeadingField_realized hf hσ0]
  have hleading : leadingMassJet (massInputOf (normalizeMassLogFields f) x) = leadingMassJet (massInputOf f x) := rfl
  rw [← hleading]
  exact hh (Real.exp (x 0)) (actualThreeJet (radiusPower (-1)) x)
    (massInputOf (normalizeMassLogFields f) x) hr (inverse_radius_three_norm x) hσ hnB

end
end CKSMixedGeometry

end

end OAI
