import OAI.Probability.InvariantIsing.Magnetic.MagneticSquareInitial
import OAI.Probability.InvariantIsing.Magnetic.MagneticContinuationComparison

namespace OAI

/-! Radial order for the actual conditional square means in inverse
magnetization coordinates, including a final ordinary Gaussian level. -/

noncomputable section
open Filter Set
open scoped NNReal Topology

namespace InvariantIsing

private lemma magneticScaledSquareContinuation_mono_of_initial (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {α β : ℝ≥0} (hα : 0 < α) (hαβ : α ≤ β) (i : Fin (L.length + 1))
    {ζ : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hinit : ∀ u ∈ Icc (-1 : ℝ) 1,
      magneticScaledSquareContinuation L hL α i ζ (0, u) ≤
        magneticScaledSquareContinuation L hL β i ζ (0, u))
    {v s : ℝ} (hv : 0 ≤ v) (hs : s ∈ Icc (-1 : ℝ) 1) :
    magneticScaledSquareContinuation L hL α i ζ (v, s) ≤
      magneticScaledSquareContinuation L hL β i ζ (v, s) := by
  have hβ : 0 < β := hα.trans_le hαβ
  have hall := magnetic_continuation_coefficient_comparison hv
    (magneticScaledSquareContinuation L hL α i ζ) (magneticScaledSquareTime L hL α i ζ)
    (magneticScaledSquareSlope L hL α i ζ) (magneticScaledSquareSecond L hL α i ζ)
    (magneticScaledSquareContinuation L hL β i ζ) (magneticScaledSquareTime L hL β i ζ)
    (magneticScaledSquareSlope L hL β i ζ) (magneticScaledSquareSecond L hL β i ζ)
    (magneticScaledClosedCurvature L hL α ζ) (magneticScaledClosedCurvature L hL β ζ)
    ((magneticScaledSquareContinuation_continuousOn L hL α i hζ).mono
      (fun p hp => ⟨mem_univ _, hp.2⟩))
    ((magneticScaledSquareContinuation_continuousOn L hL β i hζ).mono
      (fun p hp => ⟨mem_univ _, hp.2⟩)) hinit
    (fun t ht u _ => (magneticScaledSquareContinuation_hasDerivAt_time L hL hα i hζ ht.1 u).hasDerivWithinAt)
    (fun t ht u _ => (magneticScaledSquareContinuation_hasDerivAt_time L hL hβ i hζ ht.1 u).hasDerivWithinAt)
    (fun t _ u hu => magneticScaledSquareContinuation_hasDerivAt_spin L hL α i hζ (abs_lt.mpr hu) t)
    (fun t _ u hu => magneticScaledSquareContinuation_hasDerivAt_spin L hL β i hζ (abs_lt.mpr hu) t)
    (fun t _ u hu => magneticScaledSquareSlope_hasDerivAt_spin L hL α i hζ (abs_lt.mpr hu) t)
    (fun t _ u hu => magneticScaledSquareSlope_hasDerivAt_spin L hL β i hζ (abs_lt.mpr hu) t)
    (fun p hp => (magneticScaledClosedCurvature_mem_interval L hL hL1 α hζ hζ1 p hp.2).1)
    (fun p hp => magneticScaledClosedCurvature_mono L hL hL1 hα hαβ hζ hζ1 hp.1.1 hp.2)
    (fun p hp => magneticScaledSquareSecond_nonneg L hL hL1 α i hζ hζ1 hp.1.1.le p.2)
    (fun t _ => magneticScaledClosedCurvature_endpoints L hL β ζ t)
    (fun _ _ => rfl) (fun _ _ => rfl)
  exact hall (v, s) ⟨⟨hv, le_rfl⟩, hs⟩

theorem magneticScaledSquareContinuation_mono (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hL1 : ∀ av ∈ L, av.1 ≤ 1)
    {α β : ℝ≥0} (hα : 0 < α) (hαβ : α ≤ β) (i : Fin (L.length + 1))
    {ζ v s : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hv : 0 ≤ v) (hs : s ∈ Icc (-1 : ℝ) 1) :
    magneticScaledSquareContinuation L hL α i ζ (v, s) ≤
      magneticScaledSquareContinuation L hL β i ζ (v, s) := by
  induction L generalizing ζ v s with
  | nil =>
    have hi : i = 0 := by
      apply Fin.ext
      change i.val = 0
      have h := i.isLt
      change i.val < 1 at h
      omega
    subst i
    apply magneticScaledSquareContinuation_mono_of_initial [] hL hL1 hα hαβ 0 hζ hζ1 ?_ hv hs
    intro u hu
    rw [magneticScaledSquareContinuation_zero_initial [] hL α hζ hu,
      magneticScaledSquareContinuation_zero_initial [] hL β hζ hu]
  | cons av L ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · apply magneticScaledSquareContinuation_mono_of_initial (av :: L) hL hL1 hα hαβ 0 hζ hζ1 ?_ hv hs
      intro u hu
      rw [magneticScaledSquareContinuation_zero_initial (av :: L) hL α hζ hu,
        magneticScaledSquareContinuation_zero_initial (av :: L) hL β hζ hu]
    · apply magneticScaledSquareContinuation_mono_of_initial (av :: L) hL hL1 hα hαβ j.succ hζ hζ1 ?_ hv hs
      intro u hu
      rw [magneticScaledSquareContinuation_cons_initial,
        magneticScaledSquareContinuation_cons_initial]
      exact ih (fun bv hb => hL bv (List.mem_cons_of_mem av hb))
        (fun bv hb => hL1 bv (List.mem_cons_of_mem av hb)) j
        (hL av List.mem_cons_self).le (hL1 av List.mem_cons_self) av.2.property hu

end InvariantIsing

end

end OAI
