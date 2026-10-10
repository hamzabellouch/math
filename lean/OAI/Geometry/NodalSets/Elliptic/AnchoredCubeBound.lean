import Mathlib.Analysis.Calculus.Deriv.Pi
import OAI.Geometry.NodalSets.Elliptic.AnchoredIntervalBound

namespace OAI

namespace Yau.Analysis
open MeasureTheory Set Function
open scoped ENNReal ContDiff
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def InUnitCube (x : ι → ℝ) : Prop := ∀ i, |x i| ≤ 1

omit [Fintype ι] in
lemma inUnitCube_update {x : ι → ℝ} (hx : InUnitCube x)
    (i : ι) {t : ℝ} (ht : |t| ≤ 1) : InUnitCube (update x i t) := by
  intro j
  by_cases h : j = i
  · subst j; simpa using ht
  · simpa [update_of_ne h] using hx j

def cubeControl (f : List ι → (ι → ℝ) → ℝ) :
    List ι → List ι → (ι → ℝ) → ℝ≥0∞
  | [], ds, x => ‖f ds x‖ₑ
  | i :: is, ds, x => cubeControl f is ds (update x i 0) +
      ∫⁻ t in Icc (-1 : ℝ) 1, cubeControl f is (i :: ds) (update x i t)

lemma enorm_le_cubeControl (f : List ι → (ι → ℝ) → ℝ)
    (hs : ∀ ds, ContDiff ℝ 1 (f ds))
    (hd : ∀ ds i x, fderiv ℝ (f ds) x (Pi.single i 1) = f (i::ds) x)
    (is ds : List ι) (x : ι → ℝ) (hx : InUnitCube x) :
    ‖f ds x‖ₑ ≤ cubeControl f is ds x := by
  induction is generalizing ds x with
  | nil => exact le_rfl
  | cons i is ih =>
    have hder (t : ℝ) : deriv (fun t ↦ f ds (update x i t)) t =
        f (i::ds) (update x i t) := by
      change deriv (f ds ∘ update x i) t = _
      rw [((hs ds).differentiable one_ne_zero (update x i t)).hasFDerivAt.comp_hasDerivAt t
        (hasDerivAt_update x i t) |>.deriv]
      exact hd ds i _
    have hh := enorm_le_anchor_lintegral ((hs ds).comp (contDiff_update 1 x i))
      (abs_le.mp (hx i))
    change ‖f ds (update x i (x i))‖ₑ ≤ ‖f ds (update x i 0)‖ₑ +
      ∫⁻ t in Icc (-1:ℝ) 1, ‖deriv (fun t ↦ f ds (update x i t)) t‖ₑ at hh
    rw [update_eq_self] at hh
    simp_rw [hder] at hh
    apply hh.trans
    exact add_le_add (ih ds _ (inUnitCube_update hx i (by norm_num)))
      (lintegral_mono_ae (by
        filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
        exact ih (i::ds) _ (inUnitCube_update hx i (abs_le.mpr ht))))

omit [Fintype ι] in
lemma cubeControl_congr_base (f : List ι → (ι → ℝ) → ℝ)
    (is ds : List ι) (x y : ι → ℝ) (h : ∀ j, j ∉ is → x j = y j) :
    cubeControl f is ds x = cubeControl f is ds y := by
  induction is generalizing ds x y with
  | nil =>
    have he : x = y := funext (fun j ↦ h j (by simp))
    rw [he]
  | cons i is ih =>
    have he (t : ℝ) (j : ι) (hj : j ∉ is) : update x i t j = update y i t j := by
      by_cases hi : j = i
      · subst j; simp
      · simp only [update_of_ne hi]
        exact h j (by simp [hi,hj])
    simp only [cubeControl]
    rw [ih ds _ _ (he 0)]
    congr 1
    apply lintegral_congr
    intro t
    exact ih (i::ds) _ _ (he t)

lemma enorm_le_cubeControl_zero (f : List ι → (ι → ℝ) → ℝ)
    (hs : ∀ ds, ContDiff ℝ 1 (f ds))
    (hd : ∀ ds i x, fderiv ℝ (f ds) x (Pi.single i 1) = f (i::ds) x)
    (is ds : List ι) (hall : ∀ i, i ∈ is) (x : ι → ℝ) (hx : InUnitCube x) :
    ‖f ds x‖ₑ ≤ cubeControl f is ds 0 := by
  rw [← cubeControl_congr_base f is ds x 0 (fun j hj ↦ (hj (hall j)).elim)]
  exact enorm_le_cubeControl f hs hd is ds x hx

end
end Yau.Analysis

end OAI
