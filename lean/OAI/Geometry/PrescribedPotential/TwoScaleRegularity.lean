import Mathlib
import OAI.Geometry.PrescribedPotential.NonlinearScale

namespace OAI

/-! Two Scale Regularity. -/

section

 

noncomputable section
open Set Filter Topology
open scoped Classical
namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)
local instance gainNG (s : ℝ) : NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance gainNS (s : ℝ) : NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace
local instance gainTG (s : ℝ) : IsTopologicalAddGroup (D.localizers.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance gainCS (s : ℝ) : ContinuousSMul ℝ (D.localizers.RealSobolev s) :=
  SMulMemClass.continuousSMul _

omit [ConnectedSpace X] in
lemma realConstants_lower {s t : ℝ} (hst : t ≤ s) (c : ℝ) :
    D.localizers.realLower s t hst (D.realConstants s c) = D.realConstants t c := by
  apply Subtype.ext
  exact D.constantsOrder_lower hst (c : ℂ)

omit [ConnectedSpace X] in
lemma realEvaluation_embed {s : ℝ} (hs : (Module.finrank ℝ (EC d) : ℝ) < 2*s)
    (x₀ : X) (f : RealSmooth A) :
    D.realEvaluation s x₀ (D.localizers.realEmbed s f) = (f.val x₀).re := by
  change (D.pointEvaluation s x₀ (D.localizers.embed s f.val)).re = _
  rw [D.pointEvaluation_embed hs]

omit [ConnectedSpace X] in
lemma realEvaluation_lower {s t : ℝ} (hst : t ≤ s)
    (ht : (Module.finrank ℝ (EC d) : ℝ) < 2*t) (x₀ : X)
    (u : D.localizers.RealSobolev s) :
    D.realEvaluation t x₀ (D.localizers.realLower s t hst u) = D.realEvaluation s x₀ u := by
  let : NormedAddCommGroup (D.localizers.RealSobolev s) := inferInstance
  let : NormedSpace ℝ (D.localizers.RealSobolev s) := inferInstance
  let : NormedAddCommGroup (D.localizers.RealSobolev t) := inferInstance
  let : NormedSpace ℝ (D.localizers.RealSobolev t) := inferInstance
  have hs : (Module.finrank ℝ (EC d) : ℝ) < 2*s := by linarith
  have hf : (fun v : D.localizers.RealSobolev s =>
      D.realEvaluation t x₀ (D.localizers.realLower s t hst v)) =
      (fun v : D.localizers.RealSobolev s => D.realEvaluation s x₀ v) := by
    apply (D.localizers.realEmbed_dense s).equalizer
      ((D.realEvaluation t x₀).continuous.comp (D.localizers.realLower s t hst).continuous)
      (D.realEvaluation s x₀).continuous
    funext f
    simp only [Function.comp_apply,Localizers.realLower_embed,D.realEvaluation_embed ht,
      D.realEvaluation_embed hs]
  exact congr_fun hf u

def pairLower (s t : ℝ) (hst : t ≤ s) :
    (D.localizers.RealSobolev s × ℝ) →L[ℝ] (D.localizers.RealSobolev t × ℝ) :=
  (D.localizers.realLower s t hst ∘L ContinuousLinearMap.fst ℝ _ ℝ).prod
    (ContinuousLinearMap.snd ℝ _ ℝ)

omit [ConnectedSpace X] in
lemma pairLower_apply (s t : ℝ) (hst : t ≤ s)
    (w : D.localizers.RealSobolev s × ℝ) :
    D.pairLower s t hst w = (D.localizers.realLower s t hst w.1,w.2) := rfl

omit [ConnectedSpace X] in
lemma linearizedVolume_apply (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (x₀ : X)
    (u : D.localizers.RealSobolev ((k : ℝ)+2))
    (w : D.localizers.RealSobolev ((k : ℝ)+2) × ℝ) :
    D.linearizedVolume k hk x₀ u w =
      (D.realVolumeDerivative k hk u w.1 - D.realConstants (k : ℝ) w.2,
        D.realEvaluation ((k : ℝ)+2) x₀ w.1) := by
  simp only [linearizedVolume,ContinuousLinearMap.prod_apply,_root_.sub_apply,
    ContinuousLinearMap.comp_apply]
  rfl

omit [ConnectedSpace X] in
lemma linearizedVolume_lower (k l : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (hl : Module.finrank ℝ (EC d) < l) (hlk : l ≤ k) (x₀ : X)
    (u : D.localizers.RealSobolev ((k : ℝ)+2)) (w : D.localizers.RealSobolev ((k : ℝ)+2) × ℝ) :
    D.linearizedVolume l hl x₀ (D.localizers.realLower ((k : ℝ)+2) ((l : ℝ)+2)
      (by exact_mod_cast Nat.add_le_add_right hlk 2) u)
      (D.pairLower ((k : ℝ)+2) ((l : ℝ)+2) (by exact_mod_cast Nat.add_le_add_right hlk 2) w) =
    D.pairLower (k : ℝ) (l : ℝ) (by exact_mod_cast hlk) (D.linearizedVolume k hk x₀ u w) := by
  let : NormedAddCommGroup (D.localizers.RealSobolev ((k : ℝ)+2)) := inferInstance
  let : NormedSpace ℝ (D.localizers.RealSobolev ((k : ℝ)+2)) := inferInstance
  let : NormedAddCommGroup (D.localizers.RealSobolev ((l : ℝ)+2)) := inferInstance
  let : NormedSpace ℝ (D.localizers.RealSobolev ((l : ℝ)+2)) := inferInstance
  let : NormedAddCommGroup (D.localizers.RealSobolev (k : ℝ)) := inferInstance
  let : NormedSpace ℝ (D.localizers.RealSobolev (k : ℝ)) := inferInstance
  let : NormedAddCommGroup (D.localizers.RealSobolev (l : ℝ)) := inferInstance
  let : NormedSpace ℝ (D.localizers.RealSobolev (l : ℝ)) := inferInstance
  have hst : (l : ℝ)+2 ≤ (k : ℝ)+2 := by exact_mod_cast Nat.add_le_add_right hlk 2
  have hkl : (l : ℝ) ≤ (k : ℝ) := by exact_mod_cast hlk
  simp only [linearizedVolume_apply,pairLower_apply]
  apply Prod.ext
  · have hh := congrArg (fun L : D.localizers.RealSobolev ((k : ℝ)+2) →L[ℝ]
        D.localizers.RealSobolev (l : ℝ) => L w.1)
      (D.realVolumeDerivative_lower k l hk hl hlk u)
    simp only [ContinuousLinearMap.comp_apply] at hh
    rw [map_sub,D.realConstants_lower,hh]
  · apply D.realEvaluation_lower hst
    have hh : (Module.finrank ℝ (EC d) : ℝ) < (l : ℝ) := by exact_mod_cast hl
    linarith [Nat.cast_nonneg (α := ℝ) l]

 

theorem linearizedVolume_local_gain (k l : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (hl : Module.finrank ℝ (EC d) < l) (hlk : l ≤ k) (x₀ : X) :
    ∀ᶠ u in 𝓝 (0 : D.localizers.RealSobolev ((k : ℝ)+2)),
      ∀ (w : D.localizers.RealSobolev ((l : ℝ)+2) × ℝ)
        (f : D.localizers.RealSobolev (k : ℝ) × ℝ),
      D.linearizedVolume l hl x₀ (D.localizers.realLower ((k : ℝ)+2) ((l : ℝ)+2)
          (by exact_mod_cast Nat.add_le_add_right hlk 2) u) w =
        D.pairLower (k : ℝ) (l : ℝ) (by exact_mod_cast hlk) f →
      ∃ v : D.localizers.RealSobolev ((k : ℝ)+2) × ℝ,
        D.pairLower ((k : ℝ)+2) ((l : ℝ)+2) (by exact_mod_cast Nat.add_le_add_right hlk 2) v = w ∧
        D.linearizedVolume k hk x₀ u v = f := by
  obtain ⟨m,hm,he⟩ := D.exists_completedError_small
  obtain ⟨P⟩ := D.localizers.constantProjection_exists
  let : NormedAddCommGroup (D.localizers.RealSobolev ((k : ℝ)+2)) := inferInstance
  let : NormedSpace ℝ (D.localizers.RealSobolev ((k : ℝ)+2)) := inferInstance
  let : NormedAddCommGroup (D.localizers.RealSobolev ((l : ℝ)+2)) := inferInstance
  let : NormedSpace ℝ (D.localizers.RealSobolev ((l : ℝ)+2)) := inferInstance
  let : NormedAddCommGroup (D.localizers.RealSobolev (k : ℝ)) := inferInstance
  let : NormedSpace ℝ (D.localizers.RealSobolev (k : ℝ)) := inferInstance
  let : NormedAddCommGroup (D.localizers.RealSobolev (l : ℝ)) := inferInstance
  let : NormedSpace ℝ (D.localizers.RealSobolev (l : ℝ)) := inferInstance
  have hst : (l : ℝ)+2 ≤ (k : ℝ)+2 := by exact_mod_cast Nat.add_le_add_right hlk 2
  have hkl : (l : ℝ) ≤ (k : ℝ) := by exact_mod_cast hlk
  let L := D.localizers.realLower ((k : ℝ)+2) ((l : ℝ)+2) hst
  have hN : Tendsto L (𝓝 0) (𝓝 0) := by simpa only [map_zero] using L.continuous.tendsto 0
  filter_upwards [D.linearizedVolume_invertible_nhds m hm he P k hk x₀,
    hN.eventually (D.linearizedVolume_invertible_nhds m hm he P l hl x₀)] with u hu hv
  obtain ⟨e,heq⟩ := hu
  obtain ⟨e',heq'⟩ := hv
  intro w f hw
  refine ⟨e.symm f,?_,?_⟩
  · apply e'.injective
    have hm₁ := congrArg (fun T : _ →L[ℝ] _ => T
      (D.pairLower ((k : ℝ)+2) ((l : ℝ)+2) hst (e.symm f))) heq'
    have hm₂ := congrArg (fun T : _ →L[ℝ] _ => T w) heq'
    have hm₃ := congrArg (fun T : _ →L[ℝ] _ => T (e.symm f)) heq
    have hei : e.toContinuousLinearMap (e.symm f) = f := e.apply_symm_apply f
    rw [hei] at hm₃
    exact hm₁.trans ((D.linearizedVolume_lower k l hk hl hlk x₀ u (e.symm f)).trans
      ((congrArg (D.pairLower (k : ℝ) (l : ℝ) hkl) hm₃.symm).trans
        (hw.symm.trans hm₂.symm)))
  · have hh := congrArg (fun T : _ →L[ℝ] _ => T (e.symm f)) heq
    exact hh.symm.trans (e.apply_symm_apply f)

end GluingData
end GlobalElliptic

end
end

end OAI
