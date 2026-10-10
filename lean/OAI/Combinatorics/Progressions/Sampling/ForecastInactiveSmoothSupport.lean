import OAI.Combinatorics.Progressions.Sampling.ForecastContinuousRetainedExpansion

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X J : Type*} [Fintype G] [Fintype X]
  [Fintype J] [DecidableEq J]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]
variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
variable (R σ : Fin m → ℝ)
variable (s : Empty ↪ J) (root : J → ℤ) (D : Matrix Empty J ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

local notation "degree" => layerSamplerDegree I n
local notation "Active" => {a // ¬P a}
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree P
local notation "Input" => (Σ a : {a : LayerSamplerAxis I n // ¬P a},
  B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)

variable (hR : ∀ j, R j ≠ 0) (hB : ∀ a : {a : LayerSamplerAxis I n // ¬P a}, 4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬P a}, B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
  {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
  (hprincipal : ∀ j : {a : LayerSamplerAxis I n // ¬P a}, a ≤ unitProfilePrincipalSize (B := B) j.val)
  (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
  (r : ActiveProfileCoefficientIndex G B (layerSamplerDegree I n) P → ℝ) (hr : ∀ e, |r e| ≤ 1)

local notation "ContinuousCoord" => ((Spatial → ℝ) × (Output → ℝ))
local notation "density" => allocatedFixedPathForecastDensity (X := X) B P R σ s root D hp hW hL
  hB lower width r

attribute [local instance] ScalarSiteExpansion.termFinite

include hR ha hδ hprincipal hw hl hr

theorem forecastInactive_actual_smooth_factor_zero_off_ball
    (κ : ℝ) (hroot : (∑ j, |(root j : ℝ)|) ≤ W)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    {Inactive Cell Site : Type*} [Fintype Inactive]
    (e : Cell → Inactive → ScalarSiteExpansion Site)
    {Tsite Dsite Csite : Inactive → ℝ} {Hsite : ℝ} {Lsite : ℝ≥0}
    (he : ∀ cell a, (e cell a).Bounds (Tsite a) (Dsite a) (Csite a) Lsite Hsite)
    (t : Σ cell, ∀ a, (e cell a).Term) (site : Site)
    (res : ∀ a, ZMod ((e t.1 a).period (t.2 a))) (χ : ℂ) :
    let C := Real.toNNReal (anisotropicSpatialDensityCap s κ) + 1
    let Acap := allocatedFixedPathLiftRowCap P ha hδ
    let Cs := C ^ Fintype.card X
    let Cl := ∏ j, Acap j
    let H : ℝ := Cs * Cl + 1
    let F := fun y : ContinuousCoord × (Inactive → ℝ) => (density y.1 : ℂ) / (H : ℂ)
    let factor := fun y : ContinuousCoord × (Inactive → ℝ) =>
      (χ * F y) * siteFamilyFactor (e t.1) t.2 site res y.2
    ∀ y, max 3 Hsite < ‖y‖ → factor y = 0 := by
  intro C Acap Cs Cl H F factor y hy
  have hor : max 3 Hsite < ‖y.1‖ ∨ max 3 Hsite < ‖y.2‖ := by
    simpa only [Prod.norm_def, lt_max_iff] using hy
  rcases hor with hcontinuous | hinactive
  · have hzero := allocatedFixedPathForecastDensity_zero_off_ball (X := X)
      B P R σ s root D hp hW hL hR hB lower width ha hδ hprincipal hw hl r hr
      hroot hwidth y.1 ((le_max_left 3 Hsite).trans_lt hcontinuous)
    change (χ * ((density y.1 : ℂ) / (H : ℂ))) *
      siteFamilyFactor (e t.1) t.2 site res y.2 = 0
    rw [hzero, Complex.ofReal_zero, zero_div, mul_zero, zero_mul]
  · have hcoord : ∃ a, Hsite ≤ |y.2 a| := by
      by_contra hn
      have hb : ‖y.2‖ ≤ max 3 Hsite := by
        apply (pi_norm_le_iff_of_nonneg (show (0 : ℝ) ≤ max 3 Hsite from
          (by norm_num : (0 : ℝ) ≤ 3).trans (le_max_left _ _))).mpr
        intro a
        rw [Real.norm_eq_abs]
        exact (lt_of_not_ge (fun h => hn ⟨a, h⟩)).le.trans (le_max_right _ _)
      exact (not_le.mpr hinactive) hb
    exact forecastSiteMixture_factor_comp_support e he t site res F Prod.snd χ y hcoord

theorem forecastInactive_actual_smooth_factor_compact
    (κ : ℝ) (hroot : (∑ j, |(root j : ℝ)|) ≤ W)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    {Inactive Cell Site : Type*} [Fintype Inactive]
    (e : Cell → Inactive → ScalarSiteExpansion Site)
    {Tsite Dsite Csite : Inactive → ℝ} {Hsite : ℝ} {Lsite : ℝ≥0}
    (he : ∀ cell a, (e cell a).Bounds (Tsite a) (Dsite a) (Csite a) Lsite Hsite)
    (t : Σ cell, ∀ a, (e cell a).Term) (site : Site)
    (res : ∀ a, ZMod ((e t.1 a).period (t.2 a))) (χ : ℂ) :
    let C := Real.toNNReal (anisotropicSpatialDensityCap s κ) + 1
    let Acap := allocatedFixedPathLiftRowCap P ha hδ
    let Cs := C ^ Fintype.card X
    let Cl := ∏ j, Acap j
    let H : ℝ := Cs * Cl + 1
    let F := fun y : ContinuousCoord × (Inactive → ℝ) => (density y.1 : ℂ) / (H : ℂ)
    HasCompactSupport (fun y : ContinuousCoord × (Inactive → ℝ) =>
      (χ * F y) * siteFamilyFactor (e t.1) t.2 site res y.2) := by
  intro C Acap Cs Cl H F
  apply HasCompactSupport.intro
    (isCompact_closedBall (0 : ContinuousCoord × (Inactive → ℝ)) (max 3 Hsite))
  intro y hy
  exact forecastInactive_actual_smooth_factor_zero_off_ball (X := X)
    B P R σ s root D hp hW hL hR hB lower width ha hδ hprincipal hw hl r hr
    κ hroot hwidth e he t site res χ y
    (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hy)

end Erdos3.VectorPolynomial

end

end OAI
