import OAI.Analysis.CircleDomains.Topology.CollarExtension
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.OrderClosed

namespace OAI

/-!
# Compact smooth cutoffs and regular superlevel neighborhoods

This is the first half of the common contour construction in §1 of
the Koebe manuscript's small-disks proof. The cutoff is constructed
using Mathlib's smooth Urysohn theorem and a relatively compact open
neighborhood; its existence is unconditional.

Only the regular-value choice is conditional on a published input:
Arthur Sard, *The measure of the critical values of differentiable
maps*, Bull. Amer. Math. Soc. 48 (1942), 883--890, Theorem 7.2,
pp. 889--890, DOI: 10.1090/S0002-9904-1942-07811-6. We use only its
specialization to compactly supported smooth maps from the plane to
the real line. The assumption says that their actual critical-value
image has Lebesgue outer measure zero.
Original article: https://doi.org/10.1090/S0002-9904-1942-07811-6
Readable scan: https://webhomes.maths.ed.ac.uk/~v1ranick/papers/sard.pdf

No smooth Jordan disk or finite-component decomposition is assumed.
The constructed neighborhood has compact closure in the prescribed
open set and its boundary lies in a compact regular level set.
-/

open Set Filter Function MeasureTheory
open scoped Topology Manifold ContDiff

namespace CircleDomainRigidity

/-- An actual smooth compactly supported planar cutoff, equal to one
on a neighborhood of the given compact set. -/
theorem exists_smooth_planar_cutoff {A O : Set ℂ}
    (hA : IsCompact A) (hO : IsOpen O) (hAO : A ⊆ O) :
    ∃ f : ℂ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ O ∧ (∀ z, f z ∈ Icc 0 1) ∧
      ∀ᶠ z in 𝓝ˢ A, f z = 1 := by
  obtain ⟨V, hV, hAV, hVO, hVc⟩ :=
    exists_open_between_and_isCompact_closure hA hO hAO
  have hdisj : Disjoint Vᶜ A :=
    Set.disjoint_left.mpr (fun z hz hzA => hz (hAV hzA))
  obtain ⟨f, hzero, hone, hrange⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓘(ℝ, ℂ))
      hV.isClosed_compl hA.isClosed hdisj (n := (⊤ : ℕ∞))
  have hsupp : Function.support (f : ℂ → ℝ) ⊆ V := by
    intro z hz
    by_contra hzV
    exact hz (hzero.self_of_nhdsSet z hzV)
  have htsupp : tsupport (f : ℂ → ℝ) ⊆ closure V := closure_mono hsupp
  refine ⟨f, contMDiff_iff_contDiff.mp f.contMDiff, ?_, htsupp.trans hVO, hrange, hone⟩
  exact hVc.of_isClosed_subset isClosed_closure htsupp

/-- The actual differential is nonzero at every point of the level. -/
def IsPlanarRegularValue (f : ℂ → ℝ) (t : ℝ) : Prop :=
  ∀ z, f z = t → fderiv ℝ f z ≠ 0

/-- Published input: Sard (1942), Theorem 7.2, restricted to the smooth
compactly supported scalar planar case needed for contour selection.
This is a proposition parameter, not a global axiom. -/
def SmoothPlanarSard : Prop :=
  ∀ f : ℂ → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
    volume (f '' {z | fderiv ℝ f z = 0}) = 0

theorem exists_regular_value_in_interval (hsard : SmoothPlanarSard)
    {f : ℂ → ℝ} (hf : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f)
    {a b : ℝ} (hab : a < b) :
    ∃ t ∈ Ioo a b, IsPlanarRegularValue f t := by
  have hnull := hsard f hf hcompact
  have hpositive : 0 < volume (Ioo a b \ (f '' {z | fderiv ℝ f z = 0})) := by
    rw [measure_sdiff_null hnull, Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)
  obtain ⟨t, ht, htnot⟩ := nonempty_of_measure_ne_zero hpositive.ne'
  refine ⟨t, ht, ?_⟩
  intro z hz hcrit
  exact htnot ⟨z, hcrit, hz⟩

/-- A positive superlevel of a compactly supported continuous function
has compact closure inside its topological support. -/
theorem closure_superlevel_subset_tsupport {f : ℂ → ℝ} {t : ℝ} (ht : 0 < t) :
    closure {z | t < f z} ⊆ tsupport f := by
  apply closure_mono
  intro z hz
  exact ne_of_gt (ht.trans hz)

theorem isCompact_nonzero_level {f : ℂ → ℝ} (hf : Continuous f)
    (hcompact : HasCompactSupport f) {t : ℝ} (ht : t ≠ 0) :
    IsCompact {z | f z = t} := by
  apply hcompact.of_isClosed_subset (isClosed_eq hf continuous_const)
  intro z hz
  apply subset_tsupport
  change f z ≠ 0
  rwa [hz]

/-- The regular superlevel neighborhood used before taking outer
contours. The cutoff, compact support and neighborhood control are
constructed; only critical-value nullity is supplied by Sard. -/
theorem exists_smooth_regular_superlevel_neighborhood
    (hsard : SmoothPlanarSard) {A O : Set ℂ}
    (hA : IsCompact A) (hO : IsOpen O) (hAO : A ⊆ O) :
    ∃ (f : ℂ → ℝ) (t : ℝ), ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      tsupport f ⊆ O ∧ (∀ z, f z ∈ Icc 0 1) ∧ t ∈ Ioo 0 1 ∧
      IsOpen {z | t < f z} ∧ A ⊆ {z | t < f z} ∧
      IsCompact (closure {z | t < f z}) ∧ closure {z | t < f z} ⊆ O ∧
      IsCompact {z | f z = t} ∧ IsPlanarRegularValue f t ∧
      frontier {z | t < f z} ⊆ {z | f z = t} := by
  obtain ⟨f, hf, hcompact, hsupp, hrange, hone⟩ := exists_smooth_planar_cutoff hA hO hAO
  obtain ⟨t, ht, hregular⟩ := exists_regular_value_in_interval hsard hf hcompact zero_lt_one
  have hclosure := closure_superlevel_subset_tsupport (f := f) ht.1
  refine ⟨f, t, hf, hcompact, hsupp, hrange, ht, isOpen_lt continuous_const hf.continuous,
    ?_, hcompact.of_isClosed_subset isClosed_closure hclosure, hclosure.trans hsupp,
    isCompact_nonzero_level hf.continuous hcompact ht.1.ne', hregular, ?_⟩
  · intro z hz
    change t < f z
    rw [hone.self_of_nhdsSet z hz]
    exact ht.2
  · intro z hz
    exact (frontier_lt_subset_eq continuous_const hf.continuous hz).symm

/-- Isolate a compact relatively clopen piece of an obstacle by a
regular superlevel neighborhood. `IsClosed (F \ A)` is precisely the
closedness needed to exclude the other obstacle points. The positive
level, hence also the boundary, misses the whole obstacle. -/
theorem exists_regular_superlevel_isolating_obstacle
    (hsard : SmoothPlanarSard) {A F V : Set ℂ}
    (hA : IsCompact A) (hAF : A ⊆ F) (hFA : IsClosed (F \ A))
    (hV : IsOpen V) (hAV : A ⊆ V) :
    ∃ (f : ℂ → ℝ) (t : ℝ), ContDiff ℝ ∞ f ∧ t ∈ Ioo 0 1 ∧
      IsOpen {z | t < f z} ∧ A ⊆ {z | t < f z} ∧
      IsCompact (closure {z | t < f z}) ∧ closure {z | t < f z} ⊆ V ∧
      closure {z | t < f z} ∩ F = A ∧ IsCompact {z | f z = t} ∧
      IsPlanarRegularValue f t ∧ Disjoint {z | f z = t} F ∧
      Disjoint (frontier {z | t < f z}) F := by
  let O : Set ℂ := V ∩ (F \ A)ᶜ
  have hO : IsOpen O := hV.inter hFA.isOpen_compl
  have hAO : A ⊆ O := fun z hz => ⟨hAV hz, fun hbad => hbad.2 hz⟩
  obtain ⟨f, t, hf, _, hsupp, _, ht, hopen, hAU, hcompact, hclO,
    hlevel, hregular, hfront⟩ := exists_smooth_regular_superlevel_neighborhood hsard hA hO hAO
  have hclF : closure {z | t < f z} ∩ F = A := by
    apply Set.Subset.antisymm
    · intro z hz
      have hnot : z ∉ F \ A := (hclO hz.1).2
      by_contra hzA
      exact hnot ⟨hz.2, hzA⟩
    · intro z hz
      exact ⟨subset_closure (hAU hz), hAF hz⟩
  have hdisj : Disjoint {z | f z = t} F := by
    apply Set.disjoint_left.mpr
    intro z hz hzF
    have hzSupp : z ∈ tsupport f := subset_tsupport f (by
      change f z ≠ 0
      rw [hz]
      exact ht.1.ne')
    have hzA : z ∈ A := by
      by_contra hnot
      exact (hsupp hzSupp).2 ⟨hzF, hnot⟩
    have := hAU hzA
    change t < f z at this
    rw [hz] at this
    exact lt_irrefl _ this
  exact ⟨f, t, hf, ht, hopen, hAU, hcompact, fun z hz => (hclO hz).1,
    hclF, hlevel, hregular, hdisj, hdisj.mono_left hfront⟩

end CircleDomainRigidity

end OAI
