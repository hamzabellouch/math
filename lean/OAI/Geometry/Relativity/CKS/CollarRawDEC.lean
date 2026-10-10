import OAI.Geometry.Relativity.CKS.CollarConstraintBounded
import OAI.Geometry.Relativity.CKS.CollarAngularWeighted

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise InnerProductSpace

def coordinateDEC (p : NullInput) (r : ℝ) : Prop :=
  Real.sqrt ((coordinateQ (nP p))^2+
    covectorPair (rescale (1/mz (nP p)^2) (mq (nP p))) (coordinateZ (nP p)) (coordinateZ (nP p))) ≤
      coordinateEnergy p r

lemma commonAngularMomentum_norm_sq {p : MomentumInput} (hz : mz p ≠ 0)
    (hp : positiveAngular (mq p).1) (hs : (mq p).1 1 0=(mq p).1 0 1) :
    ‖commonAngularMomentum p‖^2 =
      covectorPair (rescale (1/mz p^2) (mq p)) (coordinateZ p) (coordinateZ p) := by
  rw [commonAngularMomentum,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,
    covectorEmbedding_norm_sq hp hs]
  have hc := one_div_ne_zero (pow_ne_zero 2 hz)
  have hh := covectorPair_rescale (mq p) (coordinateZ p) (coordinateZ p) hc 1 1
  simp only [one_smul,mul_one] at hh
  rw [hh]
  unfold covectorPair
  field_simp

lemma coordinateDEC_iff {p : NullInput} {r : ℝ} (hz : mz (nP p) ≠ 0)
    (hp : positiveAngular (mq (nP p)).1) (hs : (mq (nP p)).1 1 0=(mq (nP p)).1 0 1) :
    coordinateDEC p r ↔ CKSEnd.DEC (coordinateEnergy p r) (coordinateQ (nP p))
      (commonAngularMomentum (nP p)) := by
  unfold coordinateDEC CKSEnd.DEC
  rw [commonAngularMomentum_norm_sq hz hp hs]

theorem bounded_raw_DEC {K : Set MatrixScalarJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, positiveAngular (fun i k => (q i k).1)) (B A : ℝ) (hA : 0 ≤ A) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧
      ∀ p : RawNullInput, rmat p.1 0 ∈ K → ‖p‖ ≤ B →
      ∀ r : ℝ, R₀ ≤ r → rz p.1=1/r → 0 ≤ rwgt p.1 →
      (∀ i, i ≠ 0 → |p.1.1 i| ≤ A*rwgt p.1) →
      (rawAngularMatrix p) 1 0=(rawAngularMatrix p) 0 1 →
      (rawAngularMatrix (rawNullOriginal p)) 1 0=(rawAngularMatrix (rawNullOriginal p)) 0 1 →
      coordinateDEC (rawNullMap (rawNullOriginal p)) r → coordinateDEC (rawNullMap p) r := by
  obtain ⟨R₁,hR₁,C,D,hC,hD,hscalar⟩ := bounded_raw_CQ hK (fun q hq => (hreg q hq).2.ne') B A hA
  obtain ⟨R₂,hR₂,T,hT,htan⟩ := bounded_raw_common_angular hK hreg B
  let R₀ := max R₁ (max R₂ (max (C^2) (max C ((T*A)^4))))
  refine ⟨R₀,hR₁.trans (le_max_left _ _),?_⟩
  intro p hq hp r hr hz hw hparams hs hs₀ hDEC
  have hr₁ : R₁ ≤ r := (le_max_left _ _).trans hr
  have hr₂ : R₂ ≤ r := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hr
  have hr3 : max (C^2) (max C ((T*A)^4)) ≤ r :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans hr
  have hCr₂ : C^2 ≤ r := (le_max_left _ _).trans hr3
  have hCr : C ≤ r := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hr3
  have hTr : (T*A)^4 ≤ r := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hr3
  have hr1 : 1 ≤ r := hR₁.trans hr₁
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  obtain ⟨hq₀,hdq,hsmall,hz₀,hdz⟩ := hscalar p hq hp r hr₁ hz hw hparams
  obtain ⟨hpos,hpos₀,ht⟩ := htan p hq hp r A hr₂ hz hw hA hparams
  have hz₁ : mz (nP (rawNullMap p)) ≠ 0 := by change rz p.1 ≠ 0; rw [hz]; positivity
  have hz₀ : mz (nP (rawNullMap (rawNullOriginal p))) ≠ 0 := by
    change rz (rawOriginal p.1) ≠ 0
    rw [rawOriginal_z,hz]; positivity
  apply (coordinateDEC_iff hz₁ hpos hs).mpr
  have h₀ := (coordinateDEC_iff hz₀ hpos₀ hs₀).mp hDEC
  apply CKSEnd.collar_DEC_of_weighted_errors (LinearIsometry.id) h₀ hr1 hw hC hC
    (mul_nonneg hT hA) hCr₂ hCr hTr
  · simpa only [CKSEnd.smallMargin,mul_div_assoc,nP,rawNullMap,rawNullOriginal,nr] using hsmall
  · simpa only [CKSEnd.largeMargin,mul_div_assoc,nP,rawNullMap,rawNullOriginal,nr] using hdq
  · exact ht

end
end CKSAngularGeometry

end

end OAI
