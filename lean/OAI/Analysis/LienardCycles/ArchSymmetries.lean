import OAI.Analysis.LienardCycles.WidthTransport

namespace OAI

universe uP

open Set Filter MeasureTheory
open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ArchSymmetries
open ScalarArcs CanonicalVariation ArcEndpoints ArcFamilies WidthCoordinates WidthTransport

lemma affine_cancel {c : ℝ} (hc : c ≠ 0) (C y : ℝ) : (C+c*y-C)/c = y := by
  field_simp
  ring

theorem IsArch.affine {φ ψ u : ℝ → ℝ} {h t a b c H C : ℝ}
    (hu : IsArch φ u h t a b) (hc : 0 < c)
    (he : ∀ x, ψ (H+c^2*x) = C+c*φ x) :
    IsArch ψ (fun y => H+c^2*u ((y-C)/c))
      (H+c^2*h) (H+c^2*t) (C+c*a) (C+c*b) := by
  have hc2 : 0 < c^2 := sq_pos_of_pos hc
  have hpre {y : ℝ} (hy : y ∈ Icc (C+c*a) (C+c*b)) :
      (y-C)/c ∈ Icc a b := by
    constructor
    · apply (le_div_iff₀ hc).mpr
      nlinarith [hy.1]
    · apply (div_le_iff₀ hc).mpr
      nlinarith [hy.2]
  constructor
  · exact continuous_const.add (continuous_const.mul
      (hu.continuous.comp ((continuous_id.sub continuous_const).div_const c)))
  · rw [he]
    nlinarith [hu.lower_lt_peak]
  · rw [he]
    nlinarith [hu.peak_lt_upper]
  · rw [he,affine_cancel hc.ne',hu.peak]
  · rw [affine_cancel hc.ne',hu.lower]
  · rw [affine_cancel hc.ne',hu.upper]
  · rw [he]
    nlinarith [hu.lower_transverse]
  · rw [he]
    nlinarith [hu.upper_transverse]
  · intro y hy
    have hd := (((hu.equation _ (hpre hy)).comp y
      (((hasDerivAt_id y).sub_const C).div_const c)).const_mul (c^2)).const_add H
    have hd' : HasDerivAt (fun y => H+c^2*u ((y-C)/c))
        (c^2*((φ (u ((y-C)/c))-(y-C)/c)*(1/c))) y := by
      simpa using! hd
    convert hd' using 1
    rw [he]
    field_simp
    ring
  · intro y hy
    have hh := hu.range_mem _ (hpre hy)
    constructor <;> nlinarith [hh.1,hh.2]
  · intro y₁ hy₁ y₂ hy₂ hyy
    rw [he] at hy₁ hy₂
    have hm : (y₁-C)/c < (y₂-C)/c := (div_lt_div_iff_of_pos_right hc).mpr (by linarith)
    have hh := hu.inc (show (y₁-C)/c ∈ Icc a (φ t) from
      ⟨(le_div_iff₀ hc).mpr (by nlinarith [hy₁.1]), (div_le_iff₀ hc).mpr (by nlinarith [hy₁.2])⟩)
      (show (y₂-C)/c ∈ Icc a (φ t) from
      ⟨(le_div_iff₀ hc).mpr (by nlinarith [hy₂.1]), (div_le_iff₀ hc).mpr (by nlinarith [hy₂.2])⟩) hm
    nlinarith
  · intro y₁ hy₁ y₂ hy₂ hyy
    rw [he] at hy₁ hy₂
    have hm : (y₁-C)/c < (y₂-C)/c := (div_lt_div_iff_of_pos_right hc).mpr (by linarith)
    have hh := hu.dec (show (y₁-C)/c ∈ Icc (φ t) b from
      ⟨(le_div_iff₀ hc).mpr (by nlinarith [hy₁.1]), (div_le_iff₀ hc).mpr (by nlinarith [hy₁.2])⟩)
      (show (y₂-C)/c ∈ Icc (φ t) b from
      ⟨(le_div_iff₀ hc).mpr (by nlinarith [hy₂.1]), (div_le_iff₀ hc).mpr (by nlinarith [hy₂.2])⟩) hm
    nlinarith

theorem IsArch.reflect {φ u : ℝ → ℝ} {h t a b : ℝ}
    (hu : IsArch φ u h t a b) :
    IsArch (fun x => -φ x) (fun y => u (-y)) h t (-b) (-a) := by
  constructor
  · exact hu.continuous.comp continuous_neg
  · simpa using hu.peak_lt_upper
  · simpa using hu.lower_lt_peak
  · simpa using hu.peak
  · simpa using hu.upper
  · simpa using hu.lower
  · simpa using hu.upper_transverse
  · simpa using hu.lower_transverse
  · intro y hy
    have hd := (hu.equation (-y) (by constructor <;> linarith [hy.1,hy.2])).comp y (hasDerivAt_neg y)
    have hd' : HasDerivAt (fun y => u (-y)) ((φ (u (-y))- -y)*(-1)) y := by
      simpa using! hd
    convert hd' using 1
    ring
  · intro y hy
    exact hu.range_mem (-y) (by constructor <;> linarith [hy.1,hy.2])
  · intro y₁ hy₁ y₂ hy₂ hyy
    exact hu.dec (show -y₂ ∈ Icc (φ t) b by constructor <;> linarith [hy₂.1,hy₂.2])
      (show -y₁ ∈ Icc (φ t) b by constructor <;> linarith [hy₁.1,hy₁.2]) (by linarith)
  · intro y₁ hy₁ y₂ hy₂ hyy
    exact hu.inc (show -y₂ ∈ Icc a (φ t) by constructor <;> linarith [hy₂.1,hy₂.2])
      (show -y₁ ∈ Icc a (φ t) by constructor <;> linarith [hy₁.1,hy₁.2]) (by linarith)

theorem canonical_affine {φ ψ : ℝ → ℝ} {h t c H C : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hψ : ContDiff ℝ 1 ψ) (hht : h < t)
    (hc : 0 < c) (he : ∀ x, ψ (H+c^2*x) = C+c*φ x) :
    lower ψ (H+c^2*h) (H+c^2*t) = C+c*lower φ h t ∧
    upper ψ (H+c^2*h) (H+c^2*t) = C+c*upper φ h t := by
  have hu := chosen_arch (entire_arch_exists hφ hht)
  exact canonical_of_arch (IsArch.affine hu hc he) hψ (by nlinarith [sq_pos_of_pos hc])

theorem canonical_reflect {φ : ℝ → ℝ} {h t : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hht : h < t) :
    lower (fun x => -φ x) h t = -upper φ h t ∧
    upper (fun x => -φ x) h t = -lower φ h t :=
  canonical_of_arch (IsArch.reflect (chosen_arch (entire_arch_exists hφ hht))) hφ.neg hht

variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ContDiff ℝ ω Φ)
    (hloc : ∀ x : State P, ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
include hΦ hloc

omit hloc [FiniteDimensional ℝ P] in
lemma profile_C1 (p : P) : ContDiff ℝ 1 (fun u => Φ (p,u)) :=
  (hΦ.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)

omit hloc [FiniteDimensional ℝ P] in
theorem width_affine {p q : P} {h t c H C : ℝ} (hht : h < t) (hc : 0 < c)
    (he : ∀ x, Φ (q,H+c^2*x) = C+c*Φ (p,x)) :
    widthFamily Φ ((q,H+c^2*t),H+c^2*h) = c*widthFamily Φ ((p,t),h) := by
  have hh := canonical_affine (profile_C1 Φ hΦ p) (profile_C1 Φ hΦ q) hht hc he
  dsimp [widthFamily,width]
  rw [hh.1,hh.2]
  ring

omit hloc [FiniteDimensional ℝ P] in
theorem midpoint_affine {p q : P} {h t c H C : ℝ} (hht : h < t) (hc : 0 < c)
    (he : ∀ x, Φ (q,H+c^2*x) = C+c*Φ (p,x)) :
    midpointFamily Φ ((q,H+c^2*t),H+c^2*h) = c*midpointFamily Φ ((p,t),h) := by
  have hh := canonical_affine (profile_C1 Φ hΦ p) (profile_C1 Φ hΦ q) hht hc he
  dsimp [midpointFamily,ScalarArcs.midpoint]
  rw [hh.1,hh.2,he]
  ring

theorem fixed_width_affine {p q : P} {h r c H C : ℝ} (hr : 0 < r) (hc : 0 < c)
    (he : ∀ x, Φ (q,H+c^2*x) = C+c*Φ (p,x)) :
    peakAtWidth Φ ((q,H+c^2*h),c*r) = H+c^2*peakAtWidth Φ ((p,h),r) ∧
    midpointAtWidth Φ ((q,H+c^2*h),c*r) = c*midpointAtWidth Φ ((p,h),r) := by
  have hs := peak_spec Φ hΦ hloc (p := p) (h := h) hr
  have hw := width_affine Φ hΦ hs.1 hc he
  rw [hs.2] at hw
  have hp := peak_eq Φ hΦ hloc (mul_pos hc hr)
    (show H+c^2*h < H+c^2*peakAtWidth Φ ((p,h),r) by nlinarith [sq_pos_of_pos hc]) hw
  refine ⟨hp,?_⟩
  dsimp [midpointAtWidth]
  rw [hp]
  exact midpoint_affine Φ hΦ hs.1 hc he

theorem fixed_width_reflect {p q : P} {h r : ℝ} (hr : 0 < r)
    (he : ∀ x, Φ (q,x) = -Φ (p,x)) :
    peakAtWidth Φ ((q,h),r) = peakAtWidth Φ ((p,h),r) ∧
    midpointAtWidth Φ ((q,h),r) = -midpointAtWidth Φ ((p,h),r) := by
  have hs := peak_spec Φ hΦ hloc (p := p) (h := h) hr
  have hf : (fun x => Φ (q,x)) = (fun x => -Φ (p,x)) := funext he
  have hh := canonical_reflect (profile_C1 Φ hΦ p) hs.1
  have hw : widthFamily Φ ((q,peakAtWidth Φ ((p,h),r)),h) = r := by
    dsimp [widthFamily,width] at hs ⊢
    rw [hf,hh.1,hh.2]
    linarith [hs.2]
  have hp := peak_eq Φ hΦ hloc hr hs.1 hw
  refine ⟨hp,?_⟩
  dsimp [midpointAtWidth]
  rw [hp]
  dsimp [midpointFamily,ScalarArcs.midpoint]
  rw [hf,hh.1,hh.2,he]
  ring

end QuinticLienard.ArchSymmetries

end OAI
