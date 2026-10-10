import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.Reversal

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section ProperPieces
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]

lemma tangentScale_mul (a b : ℝ) (z : TangentBundle 𝓘(ℝ,Model n) M) :
    tangentScale a (tangentScale b z)=tangentScale (a*b) z := by
  rcases z with ⟨x,v⟩
  change (⟨x,a • b • v⟩ : TangentBundle 𝓘(ℝ,Model n) M)=⟨x,(a*b) • v⟩
  exact congrArg (fun w => (⟨x,w⟩ : TangentBundle 𝓘(ℝ,Model n) M)) (smul_smul a b v)

variable [CompactSpace M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]

lemma reverseRay_segment (z : TangentBundle 𝓘(ℝ,Model n) M) (h T : ℝ) (hT : T≠0) :
    reverseRay (tangentScale (T-h) (sprayFlow h z))=
      tangentScale ((T-h)/T) (reverseRay (tangentScale T z)) := by
  unfold reverseRay
  rw [sprayFlow_scale,mul_one,←sprayFlow_add,sub_add_cancel,
    sprayFlow_scale,mul_one]
  rw [tangentScale_mul,tangentScale_mul,tangentScale_mul]
  congr 1
  field_simp

variable [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma proper_suffix_in_injectivityDomain {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hz : z.2∈minimizingVectors z.1) {h T : ℝ} (hh : 0<h) (hhT : h<T) (hT1 : T≤1) :
    (T-h) • (sprayFlow h z).2∈injectivityDomain (sprayFlow h z).1 := by
  have hT : 0<T := hh.trans hhT
  let w := tangentScale T z
  have hw : w.2∈minimizingVectors w.1 := minimizingVectors_smul hz hT.le hT1
  have hr := reverseRay_minimizing hw
  have hs : 0<(T-h)/T := div_pos (sub_pos.mpr hhT) hT
  have hs1 : (T-h)/T<1 := (div_lt_one hT).mpr (by linarith)
  have hi := contracted_minimizer_mem_injectivityDomain hr hs hs1
  change (tangentScale ((T-h)/T) (reverseRay (tangentScale T z))).2∈
    injectivityDomain (tangentScale ((T-h)/T) (reverseRay (tangentScale T z))).1 at hi
  rw [←reverseRay_segment z h T hT.ne'] at hi
  have H := reverseRay_injectivityDomain hi
  change (reverseRay (reverseRay (tangentScale (T-h) (sprayFlow h z)))).2∈
    injectivityDomain (reverseRay (reverseRay (tangentScale (T-h) (sprayFlow h z)))).1 at H
  rw [reverseRay_reverseRay] at H
  exact H

lemma proper_suffix_endpoint (z : TangentBundle 𝓘(ℝ,Model n) M) (h T : ℝ) :
    riemannianExp (sprayFlow h z).1 ((T-h) • (sprayFlow h z).2)=
      riemannianExp z.1 (T • z.2) := by
  rw [riemannianExp_smul,riemannianExp_smul,←sprayFlow_add,sub_add_cancel]

end ProperPieces
end WeakMTWTransport

end

end

end

end OAI
