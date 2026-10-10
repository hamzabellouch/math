import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierSpatialBarrier
import OAI.Analysis.CoulombIonization.Localization.BarrierConditionalBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open Set Filter MeasureTheory Laplacian Metric
open scoped Topology BigOperators

namespace CoulombBarrier
open CoulombAnalysis CoulombPDE CoulombAtom

def nuclearField (Z : ℝ) (x : TFSpace) : ℝ := Z/‖x‖

def clippedNuclearField (Z R : ℝ) (x : TFSpace) : ℝ := Z/max R ‖x‖

lemma nuclearField_locallyIntegrable (Z : ℝ) : LocallyIntegrable (nuclearField Z) := by
  change LocallyIntegrable (fun x : TFSpace => Z*‖x‖⁻¹)
  exact newtonInverse_locallyIntegrable.smul Z

lemma clippedNuclearField_continuous (Z : ℝ) {R : ℝ} (hR : 0 < R) :
    Continuous (clippedNuclearField Z R) := by
  exact continuous_const.div (continuous_const.max continuous_norm)
    (fun x => ne_of_gt (hR.trans_le (le_max_left R ‖x‖)))

lemma weighted_clipped_reaction (Z R : ℝ) {χ : TFSpace → ℝ}
    (hχ : ∀ x, ‖x‖ < R → χ x = 0) (F : ℝ → ℝ) (t : ℝ) (x : TFSpace) :
    χ x*F (nuclearField Z x+t) = χ x*F (clippedNuclearField Z R x+t) := by
  by_cases hx : ‖x‖ < R
  · rw [hχ x hx,zero_mul,zero_mul]
  · simp only [clippedNuclearField,max_eq_right (le_of_not_gt hx),nuclearField]

lemma nuclearField_weak_laplacian (Z : ℝ) {φ : TFSpace → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    (∫ x, nuclearField Z x*Δ φ x) = -(4*Real.pi*Z)*φ 0 := by
  have h := tfPotential_laplacian hφ hc (0 : TFSpace)
  have he : (fun x => nuclearField Z x*Δ φ x) = fun x => Z*(Δ φ x/‖x‖) := by
    funext x
    dsimp only [nuclearField]
    ring
  rw [he,integral_const_mul]
  simp only [tfPotential,zero_sub,norm_neg] at h
  rw [h]
  ring

def WeakNuclearLowerOn (U : Set TFSpace) (Z : ℝ) (u h : TFSpace → ℝ) : Prop :=
  ∀ φ : TFSpace → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
    tsupport φ ⊆ U → (∀ x, 0 ≤ φ x) →
    -(4*Real.pi*Z)*φ 0+(∫ x, h x*φ x) ≤ ∫ x, u x*Δ φ x

theorem weakNuclearLower_add_iff {U : Set TFSpace} (Z : ℝ) {u h : TFSpace → ℝ}
    (hu : LocallyIntegrable u) :
    WeakNuclearLowerOn U Z (fun x => nuclearField Z x+u x) h ↔
      WeakLaplacianLowerOn U u h := by
  have he (φ : TFSpace → ℝ) (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
      (∫ x, (nuclearField Z x+u x)*Δ φ x) =
        -(4*Real.pi*Z)*φ 0+(∫ x, u x*Δ φ x) := by
    simp_rw [add_mul]
    rw [integral_add
      (locallyIntegrable_mul_test (nuclearField_locallyIntegrable Z)
        (tfLaplacian_continuous hφ) (tfLaplacian_compact hφ hc))
      (locallyIntegrable_mul_test hu (tfLaplacian_continuous hφ) (tfLaplacian_compact hφ hc)),
      nuclearField_weak_laplacian Z hφ hc]
  constructor
  · intro hw φ hφ hc hs hn
    have ht := hw φ hφ hc hs hn
    rw [he φ hφ hc] at ht
    exact (add_le_add_iff_left _).mp ht
  · intro hw φ hφ hc hs hn
    rw [he φ hφ hc]
    exact add_le_add_right (hw φ hφ hc hs hn) _

theorem nuclear_finset_maximum {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {U : Set TFSpace} (hU : IsOpen U) (Z : ℝ) {R k : ℝ} (hR : 0 < R)
    (u : ι → TFSpace → ℝ) (hu : ∀ i ∈ s, Continuous (u i))
    {g χ : TFSpace → ℝ} (hg : LocallyIntegrable g) (hχ : Measurable χ)
    (hbχ : ∀ x, ‖χ x‖ ≤ 1) (hzero : ∀ x, ‖x‖ < R → χ x = 0)
    (hw : ∀ i ∈ s, WeakNuclearLowerOn U Z (fun x => nuclearField Z x+u i x)
      (fun x => g x+χ x*reaction k (nuclearField Z x+u i x))) :
    WeakNuclearLowerOn U Z (fun x => nuclearField Z x+s.sup' hs (fun i => u i x))
      (fun x => g x+χ x*reaction k (nuclearField Z x+s.sup' hs (fun i => u i x))) := by
  rw [weakNuclearLower_add_iff Z (Continuous.finset_sup'_apply hs hu).locallyIntegrable]
  simp_rw [weighted_clipped_reaction Z R hzero]
  apply weak_finset_maximum_spatial s hs hU u hu hg hχ hbχ
    (F := fun x t => reaction k (clippedNuclearField Z R x+t))
    ((reaction_continuous k).comp (((clippedNuclearField_continuous Z hR).comp continuous_fst).add continuous_snd))
  intro i hi
  have hw' := (weakNuclearLower_add_iff Z (hu i hi).locallyIntegrable).mp (hw i hi)
  simpa only [weighted_clipped_reaction Z R hzero] using hw'

end CoulombBarrier

end

end OAI
