import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TailSpaceIntegrableCompatible

namespace OAI

noncomputable section
namespace VelocityDetection.TailSpace.Jets
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open SpatialCalculus

theorem contDiff_partialD_infty {n : ℕ} {f : Coord n → ℝ}
    (hf : ContDiff ℝ ∞ f) (i : Fin n) : ContDiff ℝ ∞ (partialD i f) := by
  have he : partialD i f = JointCalculus.dAlong (Pi.single i 1) f :=
    funext (partialD_eq_fderiv i (hf.differentiable (by simp)))
  rw [he]
  exact JointCalculus.contDiff_dAlong _ hf

theorem contDiff_wordPartial {n k : ℕ} {f : Coord n → ℝ}
    (hf : ContDiff ℝ ∞ f) (w : Fin k → Fin n) : ContDiff ℝ ∞ (wordPartial w f) := by
  induction k with
  | zero => exact hf
  | succ k ih => exact contDiff_partialD_infty (ih (Fin.tail w)) (w 0)

theorem compactSupport_wordPartial {n k : ℕ} {f : Coord n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (w : Fin k → Fin n) :
    HasCompactSupport (wordPartial w f) := by
  induction k with
  | zero => exact hs
  | succ k ih =>
    exact compactSupport_partialD (w 0)
      ((contDiff_wordPartial hf (Fin.tail w)).differentiable (by simp)) (ih (Fin.tail w))

def ofSmoothCompact {n : ℕ} (a : ℕ) (f : Coord n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) : compatibleJets n a :=
  ⟨fun ⟨_,w⟩ => ofCompact (wordPartial w f)
      (contDiff_wordPartial hf w).continuous (compactSupport_wordPartial hf hs w), by
    intro k w X
    have hd := (contDiff_wordPartial hf w).differentiable (by simp)
    change HasFDerivAt (wordPartial w f)
      (∑ i : Fin n, wordPartial (Fin.cons i w) f X • ContinuousLinearMap.proj i) X
    have he : (∑ i : Fin n, wordPartial (Fin.cons i w) f X •
        (ContinuousLinearMap.proj i : Coord n →L[ℝ] ℝ)) = fderiv ℝ (wordPartial w f) X := by
      ext v
      simp only [sum_apply, smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply,
        wordPartial_cons, fderiv_apply_eq_sum hd]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [he]
    exact (hd X).hasFDerivAt⟩

@[simp] theorem value_ofSmoothCompact {n : ℕ} (a : ℕ) (f : Coord n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) :
    value (ofSmoothCompact a f hf hs) = f := rfl

@[simp] theorem entry_ofSmoothCompact {n : ℕ} (a : ℕ) (f : Coord n → ℝ)
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (k : ℕ) (hk : k ≤ a)
    (w : Fin k → Fin n) :
    entry (ofSmoothCompact a f hf hs) k hk w = ofCompact (wordPartial w f)
      (contDiff_wordPartial hf w).continuous (compactSupport_wordPartial hf hs w) := rfl

theorem contDiff_uncurry_spatialD {n : ℕ} {f : ScalarField n}
    (hf : ContDiff ℝ ∞ (uncurry f)) (i : Fin n) :
    ContDiff ℝ ∞ (uncurry (spatialD i f)) := by
  have he : uncurry (spatialD i f) = JointCalculus.dAlong (0, Pi.single i 1) (uncurry f) :=
    funext (fun p => JointCalculus.spatialD_eq hf i p.1 p.2)
  rw [he]
  exact JointCalculus.contDiff_dAlong _ hf

theorem contDiff_uncurry_wordPartial {n k : ℕ} {f : ScalarField n}
    (hf : ContDiff ℝ ∞ (uncurry f)) (w : Fin k → Fin n) :
    ContDiff ℝ ∞ (fun p : ℝ × Coord n => wordPartial w (f p.1) p.2) := by
  induction k with
  | zero => exact hf
  | succ k ih =>
    exact contDiff_uncurry_spatialD (f := fun t => wordPartial (Fin.tail w) (f t))
      (ih (Fin.tail w)) (w 0)

theorem localSupport_wordPartial {k : ℕ} {f : ScalarField 2}
    (hf : ContDiff ℝ ∞ (uncurry f)) (hs : LocalHorizontalSupport f) (w : Fin k → Fin 2) :
    LocalHorizontalSupport (fun t => wordPartial w (f t)) := by
  induction k with
  | zero => exact hs
  | succ k ih => exact (ih (Fin.tail w)).spatialD (contDiff_uncurry_wordPartial hf (Fin.tail w)) (w 0)

def ofSupportedCurve (a : ℕ) {f : ScalarField 2}
    (hf : ContDiff ℝ ∞ (uncurry f)) (hs : LocalHorizontalSupport f) (t : ℝ) :
    compatibleJets 2 a := ofSmoothCompact a (f t)
      (hf.comp (contDiff_const.prodMk contDiff_id)) (hs.slice t)

@[simp] theorem value_ofSupportedCurve (a : ℕ) {f : ScalarField 2}
    (hf : ContDiff ℝ ∞ (uncurry f)) (hs : LocalHorizontalSupport f) (t : ℝ) :
    value (ofSupportedCurve a hf hs t) = f t := rfl

theorem continuous_ofSupportedCurve (a : ℕ) {f : ScalarField 2}
    (hf : ContDiff ℝ ∞ (uncurry f)) (hs : LocalHorizontalSupport f) :
    Continuous (ofSupportedCurve a hf hs) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro ⟨k,w⟩
  exact continuous_ofCompact_curve (f := fun t => wordPartial w (f t))
    (contDiff_uncurry_wordPartial hf w).continuous
    (localSupport_wordPartial hf hs w)

theorem restrict_ofSupportedCurve {a b : ℕ} (hab : a ≤ b) {f : ScalarField 2}
    (hf : ContDiff ℝ ∞ (uncurry f)) (hs : LocalHorizontalSupport f) (t : ℝ) :
    restrict hab (ofSupportedCurve b hf hs t) = ofSupportedCurve a hf hs t := by
  apply value_injective
  rfl

end VelocityDetection.TailSpace.Jets
end

noncomputable section
namespace VelocityDetection.TailSpace.Jets
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology

@[simp] theorem restrictL_apply {n a b : ℕ} (hab : a ≤ b) (J : compatibleJets n b) :
    restrictL hab J = restrict hab J := rfl

@[simp] theorem restrict_average {n a b : ℕ} (hab : a ≤ b) {k : Coord n → ℝ}
    (hk : Integrable k) (s : ℝ) (J : compatibleJets n b) :
    restrict hab (average k s J) = average k s (restrict hab J) := by
  apply value_injective
  ext X
  simp only [restrict_value, value_average hk]

@[simp] theorem restrict_heat {a b : ℕ} (hab : a ≤ b) (ν t : ℝ)
    (J : compatibleJets 2 b) : restrict hab (heat ν t J) = heat ν t (restrict hab J) := by
  exact restrict_average hab (HeatKernels.integrable_normal 2) _ J

@[simp] theorem restrict_heatGradient {a b : ℕ} (hab : a ≤ b) (ν t : ℝ)
    (i : Fin 2) (J : compatibleJets 2 b) :
    restrict hab (heatGradient ν t i J) = heatGradient ν t i (restrict hab J) := by
  change restrictL hab ((-(Real.sqrt (2 * ν * t))⁻¹) •
    average (HeatKernels.momentKernel i) (-Real.sqrt (2 * ν * t)) J) = _
  rw [map_smul]
  change _ • restrict hab (average _ _ J) = _
  rw [restrict_average hab (HeatKernels.integrable_momentKernel i)]
  rfl

@[simp] theorem restrict_product {n a b : ℕ} (hab : a ≤ b) (J K : compatibleJets n b) :
    restrict hab (product J K) = product (restrict hab J) (restrict hab K) := by
  apply value_injective
  simp only [restrict_value, value_product]

end VelocityDetection.TailSpace.Jets
end

end OAI
