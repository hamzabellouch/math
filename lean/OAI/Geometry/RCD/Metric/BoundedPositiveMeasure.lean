import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

namespace OAI

/-! # A finite measure from a bounded local positive functional

The one-sided bound by the positive part preserves positivity under the
Hahn--Banach extension. Riesz--Markov then gives a finite positive measure.
-/

open Set MeasureTheory TopologicalSpace
open scoped CompactlySupported BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

theorem exists_finite_measure_of_positive_bound
    (S : Submodule ℝ (X →ᵇ ℝ)) (F : S →ₗ[ℝ] ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ f : S, F f ≤ M * ‖(f : X →ᵇ ℝ) ⊔ 0‖) :
    ∃ σ : Measure X, IsFiniteMeasure σ ∧
      ∀ (f : S) (_hf : HasCompactSupport (f : X → ℝ)),
        (∫ x, (f : X →ᵇ ℝ) x ∂σ) = F f := by
  let P (f : X →ᵇ ℝ) := M * ‖f ⊔ 0‖
  have hPmul (c : ℝ) (hc : 0 < c) (f : X →ᵇ ℝ) : P (c • f) = c * P f := by
    have heq : (c • f) ⊔ 0 = c • (f ⊔ 0) := by
      ext x
      change max (c * f x) 0 = c * max (f x) 0
      rw [mul_max_of_nonneg _ _ hc.le, mul_zero]
    simp only [P, heq, norm_smul, Real.norm_of_nonneg hc.le]
    ring
  have hPadd (f g : X →ᵇ ℝ) : P (f + g) ≤ P f + P g := by
    have hn : ‖(f + g) ⊔ 0‖ ≤ ‖f ⊔ 0‖ + ‖g ⊔ 0‖ := by
      apply (BoundedContinuousFunction.norm_le (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      intro x
      have hf := (f ⊔ 0).apply_le_norm x
      have hg := (g ⊔ 0).apply_le_norm x
      change max (f x) 0 ≤ _ at hf
      change max (g x) 0 ≤ _ at hg
      change ‖max (f x + g x) 0‖ ≤ _
      rw [Real.norm_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [le_max_left (f x) 0, le_max_left (g x) 0])
        (add_nonneg (norm_nonneg _) (norm_nonneg _))
    dsimp only [P]
    nlinarith [mul_le_mul_of_nonneg_left hn hM]
  obtain ⟨G, hG, hGP⟩ := exists_extension_of_le_sublinear ⟨S, F⟩ P hPmul hPadd hF
  have hGpos {f : X →ᵇ ℝ} (hf : 0 ≤ f) : 0 ≤ G f := by
    have hn : (-f) ⊔ 0 = 0 := sup_eq_right.mpr (neg_nonpos.mpr hf)
    have hh := hGP (-f)
    simpa only [P, hn, norm_zero, mul_zero, map_neg, neg_nonpos] using hh
  let Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun f => G f.toBoundedContinuousFunction
      map_add' := fun f g => by
        rw [show (f + g).toBoundedContinuousFunction =
          f.toBoundedContinuousFunction + g.toBoundedContinuousFunction by ext x; rfl]
        exact G.map_add _ _
      map_smul' := fun c f => by
        rw [show (c • f).toBoundedContinuousFunction = c • f.toBoundedContinuousFunction by ext x; rfl]
        exact G.map_smul c _
      monotone' := fun f g hfg => by
        have hh := hGpos (f := g.toBoundedContinuousFunction - f.toBoundedContinuousFunction)
          (sub_nonneg.mpr hfg)
        simpa only [map_sub, sub_nonneg] using hh }
  let σ := RealRMK.rieszMeasure Λ
  have hmass : σ univ ≤ ENNReal.ofReal M := by
    rw [isOpen_univ.measure_eq_iSup_isCompact]
    refine iSup_le fun K => iSup_le fun _ => iSup_le fun hK => ?_
    obtain ⟨f, hf, hfc, _, hfrange⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ (subset_univ K)
    let u : C_c(X, ℝ) := ⟨f, hfc⟩
    have hm := RealRMK.rieszMeasure_le_of_eq_one Λ (f := u)
      (fun x => (hfrange x).1) hK hf
    have hn : ‖u.toBoundedContinuousFunction ⊔ 0‖ ≤ 1 := by
      apply (BoundedContinuousFunction.norm_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      intro x
      change ‖max (f x) 0‖ ≤ 1
      rw [max_eq_left (hfrange x).1, Real.norm_of_nonneg (hfrange x).1]
      exact (hfrange x).2
    have hu : Λ u ≤ M := (hGP u.toBoundedContinuousFunction).trans (by
      dsimp only [P]
      nlinarith [mul_le_mul_of_nonneg_left hn hM])
    exact hm.trans (ENNReal.ofReal_le_ofReal hu)
  refine ⟨σ, ⟨hmass.trans_lt ENNReal.ofReal_lt_top⟩, ?_⟩
  intro f hf
  let u : C_c(X, ℝ) := ⟨(f : X →ᵇ ℝ).toContinuousMap, hf⟩
  have hu : u.toBoundedContinuousFunction = (f : X →ᵇ ℝ) := by ext x; rfl
  change (∫ x, u x ∂σ) = F f
  rw [RealRMK.integral_rieszMeasure]
  change G u.toBoundedContinuousFunction = F f
  rw [hu]
  exact hG f

end RegularPointCoordinates

end

end OAI
