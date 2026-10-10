import OAI.Analysis.StrictMeans.TransportTest

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma transport_fiber_inequality {β k N : ℝ} (hk : 0 < k) (hβ : 3*(k-1)=β-1)
    (f : DiskFamily) (A B : Set UpperHalfPlane)
    (hmap : ∀ z∈A, (f,z)∈truncatedPairingDomain k N → sourcePartner k (f,z)∈B) (ξ : ℂ) :
    fiberSum (criticalMap k (halfPlaneFunction f)) (signedJacobianLocus k f true)
      (fun z => A.indicator (fun w=>transportTest k N (f,w)) (halfPlaneProjection z) *
        unsignedTargetWeight β f (halfPlaneProjection z)) ξ ≤
    fiberSum (criticalMap k (halfPlaneFunction f)) (signedJacobianLocus k f false)
      (fun z => B.indicator (fun _=>1) (halfPlaneProjection z) *
        unsignedTargetWeight β f (halfPlaneProjection z)) ξ := by
  classical
  let T : Set ℂ := {z | halfPlaneProjection z∈A ∧
    (f,halfPlaneProjection z)∈truncatedPairingDomain k N}
  have he : (fun z => A.indicator (fun w=>transportTest k N (f,w)) (halfPlaneProjection z) *
      unsignedTargetWeight β f (halfPlaneProjection z)) =
      T.indicator (fun z => ENNReal.ofReal (partnerRatio k (f,halfPlaneProjection z)) *
        unsignedTargetWeight β f (halfPlaneProjection z)) := by
    funext z
    by_cases ha : halfPlaneProjection z∈A <;>
      by_cases hd : (f,halfPlaneProjection z)∈truncatedPairingDomain k N <;>
      simp [T,transportTest,ha,hd]
  rw [he,fiberSum_indicator]
  let s := signedJacobianLocus k f true ∩ T
  let R : s → ℂ := fun z => sourcePartner k (f,halfPlaneProjection z.1)
  have hD (z : s) : (f,halfPlaneProjection z.1) ∈ sourcePairingDomain k := z.2.2.2.1
  have hproj (z : s) : (halfPlaneProjection z.1 : ℂ)=z.1 := by
    rw [halfPlaneProjection_of_pos z.2.1.1]
  have hRinj : Function.Injective R := by
    intro z w he
    have hp := (sourcePartner_injectiveOn hk f) (hD z) (hD w)
      (UpperHalfPlane.coe_injective he)
    apply Subtype.ext
    rw [← hproj z,← hproj w,hp]
  apply fiberSum_le_of_injection R hRinj
  · intro z
    have hs := sourcePartner_spec k (hD z)
    exact ⟨(sourcePartner k (f,halfPlaneProjection z.1)).im_pos,hs.2.2.1⟩
  · intro z
    have hs := (sourcePartner_spec k (hD z)).2.2.2.1
    dsimp [R]
    rw [hproj z] at hs
    exact hs
  · intro z
    have hb := hmap (halfPlaneProjection z.1) z.2.2.1 z.2.2.2
    dsimp [R]
    rw [halfPlaneProjection_coe,indicator_of_mem hb,one_mul,
      partnerRatio_weight hk hβ f _ (hD z)]

lemma transport_set_inequality {β k N : ℝ} (hk : 0 < k) (hβ : 3*(k-1)=β-1)
    (f : DiskFamily) {A B : Set UpperHalfPlane} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hmap : ∀ z∈A, (f,z)∈truncatedPairingDomain k N → sourcePartner k (f,z)∈B) :
    (∫⁻ z in A, sourceMassDensity β k f true z * transportTest k N (f,z) ∂upperArea) ≤
      ∫⁻ z in B, sourceMassDensity β k f false z ∂upperArea := by
  have hm : Measurable (fun z : UpperHalfPlane => transportTest k N (f,z)) :=
    (measurable_transportTest hk N).comp (measurable_const.prodMk measurable_id)
  have hL : (∫⁻ z in A, sourceMassDensity β k f true z * transportTest k N (f,z) ∂upperArea) =
      ∫⁻ z, A.indicator (fun w=>transportTest k N (f,w)) z * sourceMassDensity β k f true z ∂upperArea := by
    rw [← lintegral_indicator hA]
    apply lintegral_congr
    intro z
    by_cases hz : z∈A <;> simp [hz,mul_comm]
  have hR : (∫⁻ z in B, sourceMassDensity β k f false z ∂upperArea) =
      ∫⁻ z, B.indicator (fun _=>1) z * sourceMassDensity β k f false z ∂upperArea := by
    rw [← lintegral_indicator hB]
    apply lintegral_congr
    intro z
    by_cases hz : z∈B <;> simp [hz]
  rw [hL,hR,upper_source_area_formula hk.ne' f true (hm.indicator hA),
    upper_source_area_formula hk.ne' f false (measurable_const.indicator hB)]
  exact lintegral_mono (transport_fiber_inequality hk hβ f A B hmap)

end
end StrictInverseFirstPower

end

end OAI
