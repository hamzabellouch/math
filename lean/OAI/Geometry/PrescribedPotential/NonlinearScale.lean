import Mathlib
import OAI.Geometry.PrescribedPotential.RealNonlinearDerivative
import OAI.Geometry.PrescribedPotential.RealPoissonEquivalence

namespace OAI

/-! Nonlinear Scale. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace Localizers
variable (D : Localizers A ι)
local instance scaleNG (s : ℝ) : NormedAddCommGroup (D.RealSobolev s) :=
  (D.realCompletion s).normedAddCommGroup
local instance scaleNS (s : ℝ) : NormedSpace ℝ (D.RealSobolev s) :=
  (D.realCompletion s).normedSpace
local instance scaleTG (s : ℝ) : IsTopologicalAddGroup (D.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance scaleCS (s : ℝ) : ContinuousSMul ℝ (D.RealSobolev s) :=
  SMulMemClass.continuousSMul _

def realLower (s t : ℝ) (hst : t ≤ s) : D.RealSobolev s →L[ℝ] D.RealSobolev t :=
  ((D.lower s t).comp (D.realCompletion s).subtypeL).codRestrict (D.realCompletion t)
    (fun u => D.maps_realCompletion (D.lower s t)
      (fun f => ⟨f,D.lower_embed hst f.val⟩) u.val u.property)

lemma realLower_embed {s t : ℝ} (hst : t ≤ s) (f : RealSmooth A) :
    D.realLower s t hst (D.realEmbed s f) = D.realEmbed t f := by
  apply Subtype.ext
  exact D.lower_embed hst f.val

lemma realLower_injective {s t : ℝ} (hst : t ≤ s) :
    Function.Injective (D.realLower s t hst) := by
  intro u v h
  apply Subtype.ext
  exact D.lower_injective hst (congrArg Subtype.val h)

end Localizers
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)
local instance nonlinearScaleNG (s : ℝ) : NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance nonlinearScaleNS (s : ℝ) : NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace
local instance nonlinearScaleTG (s : ℝ) : IsTopologicalAddGroup (D.localizers.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance nonlinearScaleCS (s : ℝ) : ContinuousSMul ℝ (D.localizers.RealSobolev s) :=
  SMulMemClass.continuousSMul _

lemma realVolume_embed (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (f : RealSmooth A) :
    D.realVolume k hk (D.localizers.realEmbed ((k : ℝ)+2) f) =
      D.localizers.realEmbed (k : ℝ) (RealSmooth.ofReal (g.potentialDensity f.source)) := by
  apply Subtype.ext
  change D.completedVolume k hk (D.localizers.embed ((k : ℝ)+2) f.val) = _
  rw [← f.ofReal_source,D.completedVolume_embed k hk]
  rfl

lemma realVolume_lower (k l : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (hl : Module.finrank ℝ (EC d) < l) (hlk : l ≤ k)
    (u : D.localizers.RealSobolev ((k : ℝ)+2)) :
    D.realVolume l hl (D.localizers.realLower ((k : ℝ)+2) ((l : ℝ)+2)
      (by exact_mod_cast Nat.add_le_add_right hlk 2) u) =
    D.localizers.realLower (k : ℝ) (l : ℝ) (by exact_mod_cast hlk) (D.realVolume k hk u) := by
  have hst : (l : ℝ)+2 ≤ (k : ℝ)+2 := by exact_mod_cast Nat.add_le_add_right hlk 2
  have hkl : (l : ℝ) ≤ (k : ℝ) := by exact_mod_cast hlk
  have he : (D.realVolume l hl) ∘ D.localizers.realLower ((k : ℝ)+2) ((l : ℝ)+2) hst =
      D.localizers.realLower (k : ℝ) (l : ℝ) hkl ∘ D.realVolume k hk := by
    apply (D.localizers.realEmbed_dense ((k : ℝ)+2)).equalizer
      ((D.realVolume_continuous l hl).comp (D.localizers.realLower _ _ hst).continuous)
      ((D.localizers.realLower _ _ hkl).continuous.comp (D.realVolume_continuous k hk))
    funext f
    simp only [Function.comp_apply,Localizers.realLower_embed,realVolume_embed]
  exact congr_fun he u

variable [ConnectedSpace X]
omit [ConnectedSpace X] in
lemma realVolumeDerivative_lower (k l : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (hl : Module.finrank ℝ (EC d) < l) (hlk : l ≤ k)
    (u : D.localizers.RealSobolev ((k : ℝ)+2)) :
    (D.realVolumeDerivative l hl (D.localizers.realLower ((k : ℝ)+2) ((l : ℝ)+2)
        (by exact_mod_cast Nat.add_le_add_right hlk 2) u)).comp
      (D.localizers.realLower ((k : ℝ)+2) ((l : ℝ)+2)
        (by exact_mod_cast Nat.add_le_add_right hlk 2)) =
    (D.localizers.realLower (k : ℝ) (l : ℝ) (by exact_mod_cast hlk)).comp
      (D.realVolumeDerivative k hk u) := by
  let L := D.localizers.realLower ((k : ℝ)+2) ((l : ℝ)+2)
    (by exact_mod_cast Nat.add_le_add_right hlk 2)
  let M := D.localizers.realLower (k : ℝ) (l : ℝ) (by exact_mod_cast hlk)
  have h₁ := (D.realVolume_hasStrictFDerivAt l hl (L u)).hasFDerivAt.comp u L.hasFDerivAt
  have h₂ := M.hasFDerivAt.comp u (D.realVolume_hasStrictFDerivAt k hk u).hasFDerivAt
  have hf : D.realVolume l hl ∘ L = M ∘ D.realVolume k hk :=
    funext (D.realVolume_lower k l hk hl hlk)
  rw [hf] at h₁
  exact h₁.unique h₂

def linearizedVolume (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (x₀ : X)
    (u : D.localizers.RealSobolev ((k : ℝ)+2)) :
    (D.localizers.RealSobolev ((k : ℝ)+2) × ℝ) →L[ℝ]
      (D.localizers.RealSobolev (k : ℝ) × ℝ) :=
  ((D.realVolumeDerivative k hk u ∘L ContinuousLinearMap.fst ℝ _ ℝ) -
    (D.realConstants (k : ℝ) ∘L ContinuousLinearMap.snd ℝ _ ℝ)).prod
    (D.realEvaluation ((k : ℝ)+2) x₀ ∘L ContinuousLinearMap.fst ℝ _ ℝ)

omit [ConnectedSpace X] in
lemma linearizedVolume_zero (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (x₀ : X) :
    D.linearizedVolume k hk x₀ 0 = D.realAugmentedL k x₀ := by
  simp only [linearizedVolume,realVolumeDerivative_zero,realAugmentedL]

omit [ConnectedSpace X] in
lemma linearizedVolume_continuous (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (x₀ : X) :
    Continuous (D.linearizedVolume k hk x₀) := by
  have hc : Continuous (fun u =>
      (D.realVolumeDerivative k hk u ∘L ContinuousLinearMap.fst ℝ _ ℝ) -
      (D.realConstants (k : ℝ) ∘L ContinuousLinearMap.snd ℝ _ ℝ)) := by
    exact ((D.realVolumeDerivative_continuous k hk).clm_comp continuous_const).sub continuous_const
  let : NormedAddCommGroup (D.localizers.RealSobolev ((k : ℝ)+2) × ℝ) := inferInstance
  let : NormedSpace ℝ (D.localizers.RealSobolev ((k : ℝ)+2) × ℝ) := inferInstance
  let : NormedAddCommGroup ((D.localizers.RealSobolev ((k : ℝ)+2) × ℝ) →L[ℝ]
      D.localizers.RealSobolev (k : ℝ)) := inferInstance
  let : NormedAddCommGroup ((D.localizers.RealSobolev ((k : ℝ)+2) × ℝ) →L[ℝ] ℝ) := inferInstance
  exact (ContinuousLinearMap.prodₗᵢ (𝕜 := ℝ)
    (E := D.localizers.RealSobolev ((k : ℝ)+2) × ℝ)
    (F := D.localizers.RealSobolev (k : ℝ)) (G := ℝ) ℝ).continuous.comp
      (hc.prodMk continuous_const)

lemma linearizedVolume_invertible_nhds (m : ℝ) (hm : 1 ≤ m) (he : ‖D.completedError m hm‖ < 1)
    (P : D.localizers.ConstantProjection) (k : ℕ)
    (hk : Module.finrank ℝ (EC d) < k) (x₀ : X) :
    ∀ᶠ u in 𝓝 (0 : D.localizers.RealSobolev ((k : ℝ)+2)),
      ∃ e : (D.localizers.RealSobolev ((k : ℝ)+2) × ℝ) ≃L[ℝ]
          (D.localizers.RealSobolev (k : ℝ) × ℝ),
        (e : _ →L[ℝ] _) = D.linearizedVolume k hk x₀ u := by
  have hke : (Module.finrank ℝ (EC d) : ℝ) < 2*((k : ℝ)+2) := by
    have hh : (Module.finrank ℝ (EC d) : ℝ) < (k : ℝ) := by exact_mod_cast hk
    linarith [Nat.cast_nonneg (α := ℝ) k]
  let e := D.realPoissonEquiv m hm he P k hke x₀
  have hz : (e : _ →L[ℝ] _) = D.linearizedVolume k hk x₀ 0 := by
    rw [D.linearizedVolume_zero]
    rfl
  have hn := e.nhds
  rw [hz] at hn
  exact (D.linearizedVolume_continuous k hk x₀).continuousAt hn

end GluingData
end GlobalElliptic

end
end

end OAI
