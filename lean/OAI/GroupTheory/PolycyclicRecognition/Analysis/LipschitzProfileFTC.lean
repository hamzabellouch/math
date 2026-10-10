import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Operator.Banach

namespace OAI

/-! # Fundamental integral identities for Lipschitz profile lines -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped NNReal

theorem scalar_lipschitz_fundamental_identity
    {f q : ℝ → ℝ} {C : ℝ≥0} {T : ℝ} (hT : 0 ≤ T)
    (hf : LipschitzOnWith C f (Icc 0 T))
    (hq : ∀ᵐ t ∂volume.restrict (Icc 0 T), HasDerivAt f (q t) t) :
    IntervalIntegrable q volume 0 T ∧
      ∀ t ∈ Icc 0 T, f t - f 0 = ∫ s in 0..t, q s := by
  have hac : AbsolutelyContinuousOnInterval f 0 T := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le hT] using hf
  have heq : deriv f =ᵐ[volume.restrict (Icc 0 T)] q := hq.mono (fun _ ht => ht.deriv)
  have heqt (t : ℝ) (ht : t ∈ Icc 0 T) : deriv f =ᵐ[volume.restrict (uIoc 0 t)] q := by
    rw [uIoc_of_le ht.1]
    apply heq.filter_mono
    apply ae_mono
    exact Measure.restrict_mono
      (show Ioc (0 : ℝ) t ⊆ Icc 0 T from fun _ hs => ⟨hs.1.le, hs.2.trans ht.2⟩) le_rfl
  refine ⟨hac.intervalIntegrable_deriv.congr_ae (heqt T ⟨hT, le_rfl⟩), ?_⟩
  intro t ht
  have hac' : AbsolutelyContinuousOnInterval f 0 t :=
    hac.mono (by
      simp only [uIcc_of_le ht.1, uIcc_of_le hT]
      exact Icc_subset_Icc le_rfl ht.2)
  exact hac'.integral_deriv_eq_sub.symm.trans (intervalIntegral.integral_congr_ae_restrict (heqt t ht))

theorem profile_weight_fundamental_identities
    {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (α : I → W →L[ℝ] ℝ) {h q : ℝ → W} {C : ℝ≥0} {T : ℝ} (hT : 0 ≤ T)
    (hh : LipschitzOnWith C h (Icc 0 T))
    (hq : ∀ᵐ t ∂volume.restrict (Icc 0 T), HasDerivAt h (q t) t) :
    (∀ i, IntervalIntegrable (fun t => α i (q t)) volume 0 T) ∧
      ∀ i t, t ∈ Icc 0 T → α i (h t - h 0) = ∫ s in 0..t, α i (q s) := by
  have hf (i : I) := scalar_lipschitz_fundamental_identity hT
    ((α i).lipschitzWith.comp_lipschitzOnWith hh)
    (hq.mono (fun t ht => (α i).hasFDerivAt.comp_hasDerivAt t ht))
  exact ⟨fun i => (hf i).1, fun i t ht => by
    simpa only [map_sub, Function.comp_apply] using (hf i).2 t ht⟩

/-- The spanning weights detect an affine vector-valued line when its
almost-everywhere derivative is constant. -/
theorem affine_of_lipschitz_ae_constant_derivative
    {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (α : I → W →L[ℝ] ℝ) (hsep : ∀ w : W, (∀ i, α i w = 0) → w = 0)
    {h : ℝ → W} {C : ℝ≥0} {T : ℝ} (hT : 0 ≤ T)
    (hh : LipschitzOnWith C h (Icc 0 T)) (u : W)
    (hderiv : ∀ᵐ t ∂volume.restrict (Icc 0 T), HasDerivAt h u t) :
    ∀ t ∈ Icc 0 T, h t = h 0 + t • u := by
  have hFTC := profile_weight_fundamental_identities α hT hh hderiv
  intro t ht
  have hz : h t - h 0 - t • u = 0 := by
    apply hsep
    intro i
    rw [map_sub, (hFTC.2 i t ht), map_smul]
    simp [intervalIntegral.integral_const, smul_eq_mul]
  exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp hz)).trans (add_comm _ _)

end PolycyclicRecognition

end

end OAI
