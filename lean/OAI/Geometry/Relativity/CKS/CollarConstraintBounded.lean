import OAI.Geometry.Relativity.CKS.CollarMomentumBounded
import OAI.Geometry.Relativity.CKS.CollarRatioBounded
import OAI.Geometry.Relativity.CKS.CollarConeErrors

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def coordinateEnergy (p : NullInput) (r : ℝ) : ℝ :=
  coordinateSmallNull p r+nullRatio (nP p)*coordinateQ (nP p)

theorem bounded_raw_CQ {K : Set MatrixScalarJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1) ≠ 0) (B A : ℝ) (hA : 0 ≤ A) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ p : RawNullInput, rmat p.1 0 ∈ K → ‖p‖ ≤ B →
      ∀ r : ℝ, R₀ ≤ r → rz p.1=1/r → 0 ≤ rwgt p.1 →
      (∀ i, i ≠ 0 → |p.1.1 i| ≤ A*rwgt p.1) →
      |coordinateQ (rawMomentumInput (rawOriginal p.1))| ≤ D/r^3 ∧
      |coordinateQ (rawMomentumInput p.1)-coordinateQ (rawMomentumInput (rawOriginal p.1))-
        2*rwgt p.1/r^2| ≤ C*rwgt p.1/r^3 ∧
      |(coordinateEnergy (rawNullMap p) r-coordinateEnergy (rawNullMap (rawNullOriginal p)) r)-
          (coordinateQ (rawMomentumInput p.1)-coordinateQ (rawMomentumInput (rawOriginal p.1)))-
        2*rwgt p.1/(r^3*Real.sqrt r)| ≤ C*rwgt p.1/r^4 ∧
      (∀ a, |coordinateZ (rawMomentumInput (rawOriginal p.1)) a| ≤ D/r^2) ∧
      (∀ a, |coordinateZ (rawMomentumInput p.1) a-
        coordinateZ (rawMomentumInput (rawOriginal p.1)) a| ≤ C*rwgt p.1/r^2) := by
  obtain ⟨R₁,hR₁,S,hS,hsmall⟩ := bounded_raw_small_null hK hreg B
  obtain ⟨R₂,hR₂,M,N,hM,hN,hmom⟩ := bounded_raw_momentum hK hreg B
  obtain ⟨R₃,hR₃,T,U,hT,hU,hratio⟩ := bounded_raw_ratio hK hreg B
  let C : ℝ := S*(A+1)+U*(2+(M*A+N))+T*A*N+(M*A+N)+M*A
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hp₁ : 0 ≤ S*(A+1) := by positivity
  have hp₂ : 0 ≤ U*(2+(M*A+N)) := by positivity
  have hp₃ : 0 ≤ T*A*N := by positivity
  have hp₄ : 0 ≤ M*A := mul_nonneg hM hA
  have hC₁ : M*A+N ≤ C := by dsimp [C]; linarith
  have hC₂ : S*(A+1)+U*(2+(M*A+N))+T*A*N ≤ C := by
    dsimp [C]; have := mul_nonneg hM hA; linarith
  have hC₃ : M*A ≤ C := le_trans (by linarith) hC₁
  refine ⟨max R₁ (max R₂ R₃),hR₁.trans (le_max_left _ _),C,N,hC,hN,?_⟩
  intro p hq hp r hr hz hw hparams
  have hr₁ : R₁ ≤ r := (le_max_left _ _).trans hr
  have hr₂ : R₂ ≤ r := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hr
  have hr₃ : R₃ ≤ r := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hr
  have hr0 : 1 ≤ r := hR₁.trans hr₁
  have hsmall' := hsmall p hq hp r A hr₁ hz hw hA hparams
  obtain ⟨hq₀,hdq,hdq',hz₀,hdz,hmean⟩ := hmom p hq hp r A hr₂ hz hw hA hparams
  obtain ⟨ha,hda⟩ := hratio p hq hp r A hr₃ hz hw hA hparams
  have hCQ := smallNull_to_CQ hr0 hw (mul_nonneg hS (by positivity))
    (show 0 ≤ M*A+N by positivity) hU (mul_nonneg hT hA) hN
    hsmall' hdq' hq₀ ha hda
  refine ⟨hq₀,hdq'.trans ?_,hCQ.trans ?_,hz₀,fun a => (hdz a).trans ?_⟩
  · gcongr
  · change (S*(A+1)+U*(2+(M*A+N))+(T*A)*N)*rwgt p.1/r^4 ≤ C*rwgt p.1/r^4
    gcongr
  · gcongr

end
end CKSAngularGeometry

end

end OAI
