import OAI.Geometry.Relativity.CKS.CollarFieldConstraint
import OAI.Geometry.Relativity.CKS.CollarLogSlices

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

theorem bounded_thin_field_coordinate_DEC {K : Set MatrixScalarJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, positiveAngular (fun i k => (q i k).1)) {B A : ℝ}
    (hB : 0 ≤ B) (hA : 0 ≤ A) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (b : Fin 5 → ℝ) (f : CollarCoefficientFields) (x : Point),
      f.RegularAt x → matrixScalarJets (f.metric 0) x ∈ K → ‖b‖ ≤ B → f.ThinBoundedAt B x →
      ∀ r : ℝ, R₀ ≤ r → b 0=1/r → 0 ≤ b 4 →
      (∀ i, i ≠ 0 → |b i| ≤ A*b 4) →
      (fieldQ b f x) 1 0=(fieldQ b f x) 0 1 →
      (fieldQ (oldParams b) f x) 1 0=(fieldQ (oldParams b) f x) 0 1 →
      determinant (fieldQ b f x) ≠ 0 → determinant (fieldQ (oldParams b) f x) ≠ 0 →
      0 < lapseRadField (b 0) (fieldT b f) (fieldF b f) x →
      0 < lapseRadField ((oldParams b) 0) (fieldT (oldParams b) f) (fieldF (oldParams b) f) x →
      lapseDField (b 0) (fieldD b f) x ≠ 0 →
      lapseDField ((oldParams b) 0) (fieldD (oldParams b) f) x ≠ 0 →
      coordinateDEC (fieldNullInput (oldParams b) f x) r → coordinateDEC (fieldNullInput b f x) r := by
  obtain ⟨R,hR,hh⟩ := bounded_thin_field_map_DEC hK hreg hB hA
  refine ⟨R,hR,?_⟩
  intro b f x hf hq hb hbound r hr hz hw hparams hs hs₀ hdet hdet₀ hrad hrad₀ hd hd₀ hDEC
  rw [field_null_realization b hf hdet hrad hd]
  rw [field_null_realization (oldParams b) hf hdet₀ hrad₀ hd₀,fieldRaw_old] at hDEC
  rw [field_angular_matrix b hf] at hs
  rw [field_angular_matrix (oldParams b) hf,fieldRaw_old] at hs₀
  exact hh b f x hq hb hbound r hr hz hw hparams hs hs₀ hDEC

end
end CKSAngularGeometry

end

end OAI
