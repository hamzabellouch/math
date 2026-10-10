import Mathlib
import OAI.Analysis.SymmetricDomains.WeightedUnscaleC1Error
import OAI.Analysis.SymmetricDomains.AffineProductCoordinates
import OAI.Analysis.SymmetricDomains.GeneratorLieAdjoint
import OAI.Analysis.SymmetricDomains.AdNilpotentPositiveDilations

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open Set Filter Topology
open Filter Topology
namespace Release061
open Set Filter Topology
namespace Biholomorph

section
variable {n : ℕ} {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))

theorem generator_ad_isNilpotent_of_scaled_flow
    (a : ℝ → Biholomorph U U) (ha : Continuous a) (ha0 : a 0=1)
    (ham : ∀ s t, a (s+t)=a s*a t)
    (hdil : ∀ r : ℝ, 0<r → ∃ q : Biholomorph U U,
      ∀ t, q*a t*q⁻¹=a (r*t)) :
    IsNilpotent (LieAlgebra.ad ℝ (completeGeneratorSpace hU hc hbd Γ hhol)
      ⟨infinitesimalGenerator a,⟨a,ha,ha0,ham,rfl⟩⟩) := by
  let := finiteDimensional_completeGeneratorSpace hU hc hbd Γ hhol
  apply LieAlgebra.ad_isNilpotent_of_positive_dilations
  intro r hr
  obtain ⟨q,hq⟩ := hdil r hr
  refine ⟨generatorLieAdjoint hU hbd hc Γ hhol q,?_⟩
  apply Subtype.ext
  change pushForwardGenerator q (infinitesimalGenerator a)=r • infinitesimalGenerator a
  rw [←infinitesimalGenerator_conjugate hU hbd a ha ha0 ham q,
    show (fun t => q*a t*q⁻¹)=(fun t => a (r*t)) from funext hq]
  exact infinitesimalGenerator_time_smul hU hbd a ha ha0 ham r
end

def weightedScaleCLE {r k : ℕ} {t : ℝ} (ht : 0<t) :
    (Affine r × Affine k) ≃L[ℂ] (Affine r × Affine k) :=
  ContinuousLinearEquiv.equivOfInverse
    ((Real.sqrt t • ContinuousLinearMap.fst ℂ (Affine r) (Affine k)).prod
      (t • ContinuousLinearMap.snd ℂ (Affine r) (Affine k)))
    (((Real.sqrt t)⁻¹ • ContinuousLinearMap.fst ℂ (Affine r) (Affine k)).prod
      (t⁻¹ • ContinuousLinearMap.snd ℂ (Affine r) (Affine k)))
    (weightedUnscale_scale ht) (weightedScale_unscale ht)

@[simp] theorem weightedScaleCLE_apply {r k : ℕ} {t : ℝ} (ht : 0<t)
    (p : Affine r × Affine k) : weightedScaleCLE ht p=(Real.sqrt t • p.1,t • p.2) := rfl

def flatWeightedScale {r k : ℕ} {t : ℝ} (ht : 0<t) :
    Affine (r+k) ≃L[ℂ] Affine (r+k) :=
  ((affineProductCoordinates r k).symm.trans (weightedScaleCLE ht)).trans
    (affineProductCoordinates r k)

 theorem flatWeightedScale_mem {r k : ℕ} (D : Set (Affine r × Affine k))
    (hd : ∀ t : ℝ, 0<t → ∀ p, (Real.sqrt t • p.1,t • p.2)∈D ↔ p∈D)
    {t : ℝ} (ht : 0<t) (x : Affine (r+k)) :
    flatWeightedScale ht x∈(affineProductCoordinates r k) '' D ↔
      x∈(affineProductCoordinates r k) '' D := by
  let e : (Affine r × Affine k) ≃L[ℂ] Affine (r+k) := affineProductCoordinates r k
  have hi (y : Affine (r+k)) : y∈e '' D ↔ e.symm y∈D := by
    constructor
    · rintro ⟨p,hp,rfl⟩; simpa only [e.symm_apply_apply] using hp
    · intro h; exact ⟨e.symm y,h,e.apply_symm_apply y⟩
  rw [hi,hi]
  change e.symm (e (weightedScaleCLE ht (e.symm x)))∈D ↔ _
  rw [e.symm_apply_apply]
  exact hd t ht (e.symm x)

def flatNormalVector (r k : ℕ) (a : Fin k → ℝ) : Affine (r+k) :=
  affineProductCoordinates r k (0,fun i => (a i : ℂ))

 theorem flatNormal_translation_mem {r k : ℕ} (D : Set (Affine r × Affine k))
    (htr : ∀ p : Affine r × Affine k, ∀ a : Fin k → ℝ,
      (p.1,fun i => p.2 i+(a i : ℂ)) ∈ D ↔ p∈D)
    (a : Fin k → ℝ) (t : ℝ) (x : Affine (r+k)) :
    x+t • flatNormalVector r k a∈(affineProductCoordinates r k) '' D ↔
      x∈(affineProductCoordinates r k) '' D := by
  let e : (Affine r × Affine k) ≃L[ℂ] Affine (r+k) := affineProductCoordinates r k
  have hi (y : Affine (r+k)) : y∈e '' D ↔ e.symm y∈D := by
    constructor
    · rintro ⟨p,hp,rfl⟩; simpa only [e.symm_apply_apply] using hp
    · intro h; exact ⟨e.symm y,h,e.apply_symm_apply y⟩
  rw [hi,hi]
  have he : e.symm (x+t • flatNormalVector r k a)=
      ((e.symm x).1,fun i => (e.symm x).2 i+((t*a i : ℝ) : ℂ)) := by
    rw [map_add,show e.symm (t • flatNormalVector r k a)=
      t • e.symm (flatNormalVector r k a) from (e.symm.toContinuousLinearMap.restrictScalars ℝ).map_smul t (flatNormalVector r k a)]
    simp only [flatNormalVector,e,ContinuousLinearEquiv.symm_apply_apply]
    ext i <;> simp [Complex.real_smul]
  rw [he]
  exact htr (e.symm x) (fun i => t*a i)

 theorem flatWeightedScale_normal {r k : ℕ} {t : ℝ} (ht : 0<t) (a : Fin k → ℝ) :
    flatWeightedScale ht (flatNormalVector r k a)=t • flatNormalVector r k a := by
  let e : (Affine r × Affine k) ≃L[ℂ] Affine (r+k) := affineProductCoordinates r k
  change e (weightedScaleCLE ht (e.symm (e (0,fun i => (a i : ℂ)))) )=
    t • e (0,fun i => (a i : ℂ))
  rw [e.symm_apply_apply,←show e (t • (0,fun i => (a i : ℂ)))=
    t • e (0,fun i => (a i : ℂ)) from (e.toContinuousLinearMap.restrictScalars ℝ).map_smul t (0,fun i => (a i : ℂ))]
  congr 1
  simp only [weightedScaleCLE_apply,smul_zero,Prod.smul_mk]

theorem model_normal_translation_ad_nilpotent {r k n : ℕ}
    (D : Set (Affine r × Affine k))
    (htr : ∀ p : Affine r × Affine k, ∀ a : Fin k → ℝ,
      (p.1,fun i => p.2 i+(a i : ℂ)) ∈ D ↔ p∈D)
    (hd : ∀ t : ℝ, 0<t → ∀ p, (Real.sqrt t • p.1,t • p.2)∈D ↔ p∈D)
    {U : Set (Affine n)} (hU : IsOpen U) [LocallyCompactSpace U]
    (hc : IsConnected U) (hbd : Bornology.IsBounded U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    [LocallyCompactSpace ((affineProductCoordinates r k) '' D)]
    (e : Biholomorph ((affineProductCoordinates r k) '' D) U) (a : Fin k → ℝ) :
    ∃ b : ℝ → Biholomorph U U, Continuous b ∧ b 0=1 ∧
      (∀ s t, b (s+t)=b s*b t) ∧
      (∀ t, b t=autTransport e (translationAut (flatNormalVector r k a)
        (flatNormal_translation_mem D htr a) t)) ∧
      ∃ X : completeGeneratorSpace hU hc hbd Γ hhol,
        X.val=infinitesimalGenerator b ∧ IsNilpotent (LieAlgebra.ad ℝ _ X) := by
  let v := flatNormalVector r k a
  let hD := flatNormal_translation_mem D htr a
  let b : ℝ → Biholomorph U U := fun t => autTransport e (translationAut v hD t)
  have hb : Continuous b := (continuous_autTransport e).comp (continuous_translationAut v hD)
  have hb0 : b 0=1 := by simp [b]
  have hbm : ∀ s t, b (s+t)=b s*b t := by
    intro s t
    simp only [b,translationAut_add,autTransport_mul]
  refine ⟨b,hb,hb0,hbm,fun _ => rfl,⟨infinitesimalGenerator b,⟨b,hb,hb0,hbm,rfl⟩⟩,rfl,?_⟩
  apply generator_ad_isNilpotent_of_scaled_flow hU hc hbd Γ hhol b hb hb0 hbm
  intro t ht
  let L : Affine (r+k) ≃L[ℂ] Affine (r+k) := flatWeightedScale ht
  let hL := flatWeightedScale_mem D hd ht
  refine ⟨autTransport e (linearAut L hL),?_⟩
  intro s
  change autTransport e (linearAut L hL)*autTransport e (translationAut v hD s)*
    (autTransport e (linearAut L hL))⁻¹=autTransport e (translationAut v hD (t*s))
  rw [←autTransport_inv,←autTransport_mul,←autTransport_mul,
    linearAut_translation_conjugate v hD L hL t (flatWeightedScale_normal ht a)]

end Biholomorph
end Release061

end

end OAI
