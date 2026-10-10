import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace OAI

/-!
# Finite-order transport of jets through frozen affine coordinates

The input linear map and every output normalization are fixed at the
testing point. Positive-order jets ignore output translations. The
dyadic result therefore applies in every order used by the iteration
without assuming any next-stage jet bound.
-/

open Filter Set
open scoped Topology BigOperators

noncomputable section

namespace RegularPointCoordinates

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Local finite differentiability suffices for exact linear input transport. -/
theorem iteratedFDeriv_comp_clm_at (L : G →L[ℝ] E) (f : E → F) (z : G) (m : ℕ)
    (hf : ContDiffAt ℝ m f (L z)) :
    iteratedFDeriv ℝ m (f ∘ L) z =
      (iteratedFDeriv ℝ m f (L z)).compContinuousLinearMap (fun _ => L) := by
  obtain ⟨u, hu, hfu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨s, hsu, hs, hx⟩ := mem_nhds_iff.mp hu
  have hsmooth := hfu.mono hsu
  have hpre := hs.preimage L.continuous
  have h := L.iteratedFDerivWithin_comp_right hsmooth hs.uniqueDiffOn
    hpre.uniqueDiffOn hx le_rfl
  rw [iteratedFDerivWithin_of_isOpen m hpre hx,
    iteratedFDerivWithin_of_isOpen m hs hx] at h
  exact h

/-- Exact affine input transport in every derivative order, including zero. -/
theorem iteratedFDeriv_comp_affine_at (L : G →L[ℝ] E) (f : E → F)
    (x : E) (z : G) (m : ℕ) (hf : ContDiffAt ℝ m f (x + L z)) :
    iteratedFDeriv ℝ m (fun y => f (x + L y)) z =
      (iteratedFDeriv ℝ m f (x + L z)).compContinuousLinearMap (fun _ => L) := by
  have hshift : ContDiffAt ℝ m (fun y => f (x + y)) (L z) :=
    hf.comp (L z) (contDiffAt_const.add contDiffAt_id)
  have h := iteratedFDeriv_comp_clm_at L (fun y => f (x + y)) z m hshift
  rw [iteratedFDeriv_comp_add_left] at h
  exact h

theorem iteratedFDeriv_comp_affine_apply (L : G →L[ℝ] E) (f : E → F)
    (x : E) (z : G) (m : ℕ) (hf : ContDiffAt ℝ m f (x + L z)) (xi : Fin m → G) :
    iteratedFDeriv ℝ m (fun y => f (x + L y)) z xi =
      iteratedFDeriv ℝ m f (x + L z) (fun i => L (xi i)) := by
  rw [iteratedFDeriv_comp_affine_at L f x z m hf]
  rfl

/-- The norm cost of affine input transport is exactly the product of
the input operator norms, with no extra combinatorial coefficient. -/
theorem norm_iteratedFDeriv_comp_affine_le (L : G →L[ℝ] E) (f : E → F)
    (x : E) (z : G) (m : ℕ) (hf : ContDiffAt ℝ m f (x + L z)) :
    ‖iteratedFDeriv ℝ m (fun y => f (x + L y)) z‖ ≤
      ‖iteratedFDeriv ℝ m f (x + L z)‖ * ‖L‖ ^ m := by
  rw [iteratedFDeriv_comp_affine_at L f x z m hf]
  simpa using (iteratedFDeriv ℝ m f (x + L z)).norm_compContinuousLinearMap_le
    (fun _ : Fin m => L)

/-- A fixed linear output map and a translation have the expected
positive-order derivative. -/
theorem iteratedFDeriv_affine_input_output (L : G →L[ℝ] E) (A : F →L[ℝ] H)
    (f : E → F) (x : E) (z : G) (b : H) {m : ℕ} (hm : 0 < m)
    (hf : ContDiffAt ℝ m f (x + L z)) :
    iteratedFDeriv ℝ m (fun y => A (f (x + L y)) + b) z =
      A.compContinuousMultilinearMap
        ((iteratedFDeriv ℝ m f (x + L z)).compContinuousLinearMap (fun _ => L)) := by
  have hcomp : ContDiffAt ℝ m (fun y => f (x + L y)) z :=
    hf.comp z (contDiffAt_const.add L.contDiff.contDiffAt)
  have hout : ContDiffAt ℝ m (fun y => A (f (x + L y))) z :=
    A.contDiff.contDiffAt.comp z hcomp
  change iteratedFDeriv ℝ m ((fun y => A (f (x + L y))) + fun _ => b) z = _
  rw [iteratedFDeriv_add_apply hout contDiffAt_const]
  simp only [iteratedFDeriv_const_of_ne (Nat.ne_of_gt hm), Pi.zero_apply, add_zero]
  rw [show (fun y => A (f (x + L y))) = A ∘ (fun y => f (x + L y)) from rfl,
    A.iteratedFDeriv_comp_left hcomp le_rfl,
    iteratedFDeriv_comp_affine_at L f x z m hf]

theorem norm_iteratedFDeriv_affine_input_output_le
    (L : G →L[ℝ] E) (A : F →L[ℝ] H) (f : E → F) (x : E) (z : G) (b : H)
    {m : ℕ} (hm : 0 < m) (hf : ContDiffAt ℝ m f (x + L z)) :
    ‖iteratedFDeriv ℝ m (fun y => A (f (x + L y)) + b) z‖ ≤
      ‖A‖ * ‖iteratedFDeriv ℝ m f (x + L z)‖ * ‖L‖ ^ m := by
  rw [iteratedFDeriv_affine_input_output L A f x z b hm hf]
  calc
    _ ≤ ‖A‖ * ‖(iteratedFDeriv ℝ m f (x + L z)).compContinuousLinearMap (fun _ => L)‖ :=
      A.norm_compContinuousMultilinearMap_le _
    _ ≤ ‖A‖ * (‖iteratedFDeriv ℝ m f (x + L z)‖ * ‖L‖ ^ m) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg A)
      simpa using (iteratedFDeriv ℝ m f (x + L z)).norm_compContinuousLinearMap_le
        (fun _ : Fin m => L)
    _ = _ := by ring

/-- Scalar output scaling, with arbitrary output translation. -/
theorem iteratedFDeriv_scaled_affine (L : G →L[ℝ] E) (f : E → F)
    (x : E) (z : G) (a : ℝ) (b : F) {m : ℕ} (hm : 0 < m)
    (hf : ContDiffAt ℝ m f (x + L z)) :
    iteratedFDeriv ℝ m (fun y => a • f (x + L y) + b) z =
      a • (iteratedFDeriv ℝ m f (x + L z)).compContinuousLinearMap (fun _ => L) := by
  have hcomp : ContDiffAt ℝ m (fun y => f (x + L y)) z :=
    hf.comp z (contDiffAt_const.add L.contDiff.contDiffAt)
  change iteratedFDeriv ℝ m ((fun y => a • f (x + L y)) + fun _ => b) z = _
  rw [iteratedFDeriv_add_apply (hcomp.const_smul a) contDiffAt_const]
  simp only [iteratedFDeriv_const_of_ne (Nat.ne_of_gt hm), Pi.zero_apply, add_zero]
  rw [iteratedFDeriv_const_smul_apply' hcomp,
    iteratedFDeriv_comp_affine_at L f x z m hf]

theorem norm_iteratedFDeriv_scaled_affine_le (L : G →L[ℝ] E) (f : E → F)
    (x : E) (z : G) (a : ℝ) (b : F) {m : ℕ} (hm : 0 < m)
    (hf : ContDiffAt ℝ m f (x + L z)) :
    ‖iteratedFDeriv ℝ m (fun y => a • f (x + L y) + b) z‖ ≤
      |a| * ‖iteratedFDeriv ℝ m f (x + L z)‖ * ‖L‖ ^ m := by
  rw [iteratedFDeriv_scaled_affine L f x z a b hm hf, norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ |a| * (‖iteratedFDeriv ℝ m f (x + L z)‖ * ‖L‖ ^ m) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg a)
      simpa using (iteratedFDeriv ℝ m f (x + L z)).norm_compContinuousLinearMap_le
        (fun _ : Fin m => L)
    _ = _ := by ring

/-- The actual normalization `hhat(z) = r⁻¹(h(x+r T⁻¹z)-h(x))`. -/
theorem normalized_jet_apply (T : E ≃L[ℝ] E) (h : E → F) (x z : E) (r : ℝ)
    {m : ℕ} (hm : 0 < m) (hh : ContDiffAt ℝ m h (x + r • T.symm z))
    (xi : Fin m → E) :
    iteratedFDeriv ℝ m (fun y => r⁻¹ • (h (x + r • T.symm y) - h x)) z xi =
      (r⁻¹ * r ^ m) • iteratedFDeriv ℝ m h (x + r • T.symm z)
        (fun i => T.symm (xi i)) := by
  let L : E →L[ℝ] E := r • (T.symm : E →L[ℝ] E)
  have hformula := iteratedFDeriv_scaled_affine L h x z r⁻¹ (-(r⁻¹ • h x)) hm hh
  have heq : (fun y => r⁻¹ • (h (x + r • T.symm y) - h x)) =
      (fun y => r⁻¹ • h (x + L y) + -(r⁻¹ • h x)) := by
    funext y
    simp [L, sub_eq_add_neg]
  rw [heq, hformula]
  simp only [smul_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply, L]
  change r⁻¹ • (iteratedFDeriv ℝ m h (x + r • T.symm z)
      (fun i => r • T.symm (xi i))) = _
  rw [(iteratedFDeriv ℝ m h (x + r • T.symm z)).map_smul_univ]
  simp [smul_smul]

/-- Operator-norm form of the same source normalization. -/
theorem normalized_jet_norm_le (T : E ≃L[ℝ] E) (h : E → F) (x z : E) (r : ℝ)
    {m : ℕ} (hm : 0 < m) (hh : ContDiffAt ℝ m h (x + r • T.symm z)) :
    ‖iteratedFDeriv ℝ m (fun y => r⁻¹ • (h (x + r • T.symm y) - h x)) z‖ ≤
      |r⁻¹| * ‖iteratedFDeriv ℝ m h (x + r • T.symm z)‖ *
        (|r| * ‖(T.symm : E →L[ℝ] E)‖) ^ m := by
  let L : E →L[ℝ] E := r • (T.symm : E →L[ℝ] E)
  have hbound := norm_iteratedFDeriv_scaled_affine_le L h x z r⁻¹ (-(r⁻¹ • h x)) hm hh
  have heq : (fun y => r⁻¹ • (h (x + r • T.symm y) - h x)) =
      (fun y => r⁻¹ • h (x + L y) + -(r⁻¹ • h x)) := by
    funext y
    simp [L, sub_eq_add_neg]
  rw [heq]
  simpa [L, norm_smul, Real.norm_eq_abs] using hbound

/-- The dyadic change of variables for a contracting change of frozen metric.
The harmless output constant is retained explicitly. -/
theorem norm_iteratedFDeriv_dyadic_metric_change_le (S : E →L[ℝ] E)
    (g : E → F) (b : F) {m : ℕ} (hm : 0 < m)
    (hS : ‖S‖ ≤ 1) (hg : ContDiffAt ℝ m g 0) :
    ‖iteratedFDeriv ℝ m (fun z => (2 : ℝ) • g ((1 / 2 : ℝ) • S z) + b) 0‖ ≤
      (2 / (2 : ℝ) ^ m) * ‖iteratedFDeriv ℝ m g 0‖ := by
  let L : E →L[ℝ] E := (1 / 2 : ℝ) • S
  have hL : ‖L‖ ≤ (1 / 2 : ℝ) := by
    simpa [L, norm_smul] using mul_le_mul_of_nonneg_left hS (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hg' : ContDiffAt ℝ m g (0 + L 0) := by simpa using hg
  have h := norm_iteratedFDeriv_scaled_affine_le L g 0 0 2 b hm hg'
  simp only [map_zero, zero_add, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  change ‖iteratedFDeriv ℝ m (fun z => (2 : ℝ) • g ((1 / 2 : ℝ) • S z) + b) 0‖ ≤ _ at h
  calc
    _ ≤ 2 * ‖iteratedFDeriv ℝ m g 0‖ * ‖L‖ ^ m := h
    _ ≤ 2 * ‖iteratedFDeriv ℝ m g 0‖ * (1 / 2 : ℝ) ^ m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg L) hL m) (by positivity)
    _ = _ := by rw [div_pow]; ring

end RegularPointCoordinates

end

end OAI
