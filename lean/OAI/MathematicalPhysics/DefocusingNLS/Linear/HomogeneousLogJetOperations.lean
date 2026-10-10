import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLogJetBound
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRobinMatrix
import Mathlib.Analysis.Calculus.ContDiff.Bounds

namespace OAI

/-! # Linear maps and polynomial operations on logarithmic jet bounds

These operations apply the checked scalar jet bounds to the two-channel
coefficient matrices of the original radial equation.
-/

open Set Filter Topology
open scoped ContDiff

namespace DefocusingNLS

namespace HasLogJetBound

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  {σ : ℝ} {f : ℝ → A}

theorem map (hf : HasLogJetBound σ f) (L : A →L[ℝ] B) :
    HasLogJetBound σ (fun t => L (f t)) := by
  obtain ⟨T, hT⟩ := hf.smooth
  refine ⟨⟨T, L.contDiff.comp_contDiffOn hT⟩, ?_⟩
  intro k
  obtain ⟨C, hC, hb⟩ := hf.bound k
  refine ⟨‖L‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
  filter_upwards [hb, eventually_gt_atTop T] with t ht hTt
  have hs := (hT t hTt).contDiffAt (Ioi_mem_nhds hTt)
  have hh := L.norm_iteratedFDeriv_comp_left hs (by simp : (k : ℕ∞ω) ≤ ∞)
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Function.comp_def] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans_eq (by ring))

theorem pair {g : ℝ → B} (hf : HasLogJetBound σ f) (hg : HasLogJetBound σ g) :
    HasLogJetBound σ (fun t => (f t, g t)) := by
  have hp := (hf.map (ContinuousLinearMap.inl ℝ A B)).add
    (hg.map (ContinuousLinearMap.inr ℝ A B))
  simpa only [ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
    Prod.mk_add_mk, add_zero, zero_add] using hp

theorem conj {g : ℝ → ℂ} (hg : HasLogJetBound σ g) :
    HasLogJetBound σ (fun t => star (g t)) := by
  simpa only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, starRingEnd_apply] using
    hg.map Complex.conjCLE.toContinuousLinearMap

theorem const_mul {g : ℝ → ℂ} (hg : HasLogJetBound σ g) (c : ℂ) :
    HasLogJetBound σ (fun t => c * g t) := by
  simpa only [zero_add] using (HasLogJetBound.const c).mul hg

theorem pow {g : ℝ → ℂ} (hg : HasLogJetBound σ g) (m : ℕ) :
    HasLogJetBound ((m : ℝ) * σ) (fun t => (g t) ^ m) := by
  induction m with
  | zero => simpa only [Nat.cast_zero, zero_mul, pow_zero] using HasLogJetBound.const (1 : ℂ)
  | succ m ih =>
      have he : ((m + 1 : ℕ) : ℝ) * σ = (m : ℝ) * σ + σ := by push_cast; ring
      simpa only [he, pow_succ] using ih.mul hg

theorem twoColumns {u v : ℝ → ℂ × ℂ}
    (hu : HasLogJetBound σ u) (hv : HasLogJetBound σ v) :
    HasLogJetBound σ (fun t => spectralTwoColumns (u t) (v t)) := by
  exact (hu.map ((ContinuousLinearMap.smulRightL ℂ (ℂ × ℂ) (ℂ × ℂ)
    (ContinuousLinearMap.fst ℂ ℂ ℂ)).restrictScalars ℝ)).add
      (hv.map ((ContinuousLinearMap.smulRightL ℂ (ℂ × ℂ) (ℂ × ℂ)
        (ContinuousLinearMap.snd ℂ ℂ ℂ)).restrictScalars ℝ))

end HasLogJetBound

end DefocusingNLS

end OAI
