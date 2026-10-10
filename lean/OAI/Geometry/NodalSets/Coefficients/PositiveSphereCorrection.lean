import OAI.Geometry.NodalSets.Charts.SeedChartScalarExtension
import OAI.Geometry.NodalSets.Charts.SpherePositiveMargins
import OAI.Geometry.NodalSets.Elliptic.IntrinsicRoundPerturbation

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

local instance positiveSphereCorrectionLocalInst1 : NormedAddCommGroup CotangentModel := ContinuousLinearMap.toNormedAddCommGroup
local instance positiveSphereCorrectionLocalInst2 : NormedSpace ℝ CotangentModel := ContinuousLinearMap.toNormedSpace
local instance positiveSphereCorrectionLocalInst3 : NormedAddCommGroup (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance positiveSphereCorrectionLocalInst4 : NormedSpace ℝ (CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance positiveSphereCorrectionLocalInst5 : NormedAddCommGroup (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
local instance positiveSphereCorrectionLocalInst6 : NormedSpace ℝ (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
local instance positiveSphereCorrectionLocalInst7 (x : Base) : AddCommGroup (SphereCotangent x) := ContinuousLinearMap.addCommGroup
local instance positiveSphereCorrectionLocalInst8 (x : Base) : Module ℝ (SphereCotangent x) := ContinuousLinearMap.module
local instance positiveSphereCorrectionLocalInst9 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance positiveSphereCorrectionLocalInst10 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module
local instance positiveSphereCorrectionLocalInst11 (x : Base) : IsTopologicalAddGroup (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.isTopologicalAddGroup
local instance positiveSphereCorrectionLocalInst12 (x : Base) : ContinuousSMul ℝ (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.continuousSMul
local instance positiveSphereCorrectionLocalInst13 (x : Base) : TopologicalSpace (SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.topologicalSpace
local instance positiveSphereCorrectionLocalInst14 : TopologicalSpace (Bundle.TotalSpace (CotangentModel →L[ℝ] CotangentModel →L[ℝ] ℝ)
    (fun x : Base ↦ SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id ℝ) CotangentModel SphereCotangent
    (CotangentModel →L[ℝ] ℝ) (fun x : Base ↦ SphereCotangent x →L[ℝ] ℝ)

local instance positiveSphereCorrectionLocalInst15 (x : Base) : AddCommGroup (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.addCommGroup
local instance positiveSphereCorrectionLocalInst16 (x : Base) : Module ℝ (SphereCotangent x →L[ℝ] SphereCotangent x →L[ℝ] ℝ) := ContinuousLinearMap.module

lemma seed_scalar_extension_bound (v : Yau.Jets.Coord → ℝ) (V : Base → ℝ)
    (hs : tsupport V ⊆ seedSphereFromCoord '' tsupport v)
    (he : ∀ x, V (seedSphereFromCoord x) = v x) {eps : ℝ} (hp : 0 ≤ eps)
    (hb : ∀ x, |v x| ≤ eps) : ∀ p, |V p| ≤ eps := by
  intro p
  by_cases h : p ∈ tsupport V
  · obtain ⟨x,_,rfl⟩ := hs h
    rw [he]
    exact hb x
  · rw [image_eq_zero_of_notMem_tsupport h,abs_zero]
    exact hp

lemma round_perturbed_pair_positive (A : IntrinsicTensor) (rho alpha beta : Base → ℝ)
    {c : ℝ} (hc : 0 < c)
    (hA : ∀ x v, c*roundCotangentTensor x v v ≤ A x v v)
    (hr : ∀ x, c ≤ rho x) (ha : ∀ x, |alpha x| < c) (hb : ∀ x, |beta x| < c) :
    (∀ x v, v ≠ 0 → 0 < (A x+roundTensorPerturbation alpha x) v v) ∧
    ∀ x, 0 < rho x+beta x := by
  constructor
  · intro x v hv
    have hp := roundCotangentTensor_pos x v hv
    have hlow := hA x v
    have hs := (abs_lt.mp (ha x)).1
    have hmul : 0 < (c+alpha x)*roundCotangentTensor x v v := mul_pos (by linarith) hp
    change 0 < A x v v+alpha x*roundCotangentTensor x v v
    nlinarith
  · intro x
    by_cases hbeta : 0 ≤ beta x
    · exact add_pos_of_pos_of_nonneg (hc.trans_le (hr x)) hbeta
    have hs := (abs_lt.mp (hb x)).1
    have := hr x
    linarith

theorem positive_sphere_scalar_correction (A : IntrinsicTensor) (hA : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v) (rho : Base → ℝ)
    (hr : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho) (hrp : ∀ x, 0 < rho x) :
    ∃ c > 0, ∀ (alpha beta : Yau.Jets.Coord → ℝ) (Q : Set Yau.Jets.Coord),
      IsCompact Q → ContDiff ℝ ∞ alpha → ContDiff ℝ ∞ beta →
      tsupport alpha ⊆ Q → tsupport beta ⊆ Q → ∀ eps : ℝ, 0 ≤ eps → eps < c →
      (∀ x, |alpha x| ≤ eps) → (∀ x, |beta x| ≤ eps) →
      ∃ a b : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ a ∧ ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b ∧
        tsupport a ⊆ seedSphereFromCoord '' Q ∧ tsupport b ⊆ seedSphereFromCoord '' Q ∧
        (∀ x, a (seedSphereFromCoord x) = alpha x) ∧
        (∀ x, b (seedSphereFromCoord x) = beta x) ∧
        (∀ x, |a x| ≤ eps) ∧ (∀ x, |b x| ≤ eps) ∧
        IntrinsicTensorSmooth (fun x ↦ A x+roundTensorPerturbation a x) ∧
        (∀ x v w, (A x+roundTensorPerturbation a x) v w = (A x+roundTensorPerturbation a x) w v) ∧
        (∀ x v, v ≠ 0 → 0 < (A x+roundTensorPerturbation a x) v v) ∧
        ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ rho x+b x) ∧
        ∀ x, 0 < rho x+b x := by
  obtain ⟨c,hc,hAm,hrm⟩ := intrinsic_pair_positive_margin A hA hs hp rho hr hrp
  refine ⟨c,hc,?_⟩
  intro alpha beta Q hQ has hbs haq hbq eps heps hec hab hbb
  obtain ⟨a,ha,hasup,haval⟩ := seed_chart_scalar_extension alpha has
    (hQ.of_isClosed_subset isClosed_closure haq)
  obtain ⟨b,hb,hbsup,hbval⟩ := seed_chart_scalar_extension beta hbs
    (hQ.of_isClosed_subset isClosed_closure hbq)
  have haB := seed_scalar_extension_bound alpha a hasup haval heps hab
  have hbB := seed_scalar_extension_bound beta b hbsup hbval heps hbb
  obtain ⟨hposA,hposR⟩ := round_perturbed_pair_positive A rho a b hc hAm hrm
    (fun x ↦ (haB x).trans_lt hec) (fun x ↦ (hbB x).trans_lt hec)
  refine ⟨a,b,ha,hb,hasup.trans (image_mono haq),hbsup.trans (image_mono hbq),haval,hbval,
    haB,hbB,hA.add_section (roundTensorPerturbation_smooth a ha),?_,hposA,hr.add hb,hposR⟩
  intro x v w
  change A x v w+a x*roundCotangentTensor x v w = A x w v+a x*roundCotangentTensor x w v
  rw [hs,roundCotangentTensor_symm]

end
end Yau.Target

end OAI
