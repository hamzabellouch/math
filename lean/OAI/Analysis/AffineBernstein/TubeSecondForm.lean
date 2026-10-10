import Mathlib

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Euler and the angular gradient identity give the genuine tangent conormal. -/
omit [CompleteSpace E] in
lemma support_tangent_identity {H : S × E → ℝ} {Y : S × E → E} {x : S × E}
    (hH : DifferentiableAt ℝ H x) (hY : DifferentiableAt ℝ Y x)
    (heul : H =ᶠ[𝓝 x] (fun q => inner ℝ q.2 (Y q)))
    (hgrad : ∀ w : E, fderiv ℝ H x (0,w) = inner ℝ (Y x) w) (v : S × E) :
    inner ℝ x.2 (fderiv ℝ Y x v) = fderiv ℝ H x (v.1,0) := by
  have hd := (hasFDerivAt_snd (p := x)).inner ℝ hY.hasFDerivAt
  have hh := (hd.congr_of_eventuallyEq heul).unique hH.hasFDerivAt
  have he := congrArg (fun A : (S × E) →L[ℝ] ℝ => A v) hh
  have he' : inner ℝ x.2 (fderiv ℝ Y x v) + inner ℝ v.2 (Y x) = fderiv ℝ H x v := by
    simpa using he
  have hs : fderiv ℝ H x v = fderiv ℝ H x (v.1,0) + inner ℝ (Y x) v.2 := by
    rw [← hgrad, ← map_add]
    simp
  rw [hs, real_inner_comm v.2] at he'
  linarith

/- Raw Gauss parametrization, before restricting the angular variable to a chart. -/
def supportParam (Y : S × E → E) (q : S × E) : S × E := (q.1, Y q)

def supportConormal (H : S × E → ℝ) (x : S × E) : (S × E) →L[ℝ] ℝ :=
  (fderiv ℝ H x).comp ((ContinuousLinearMap.id ℝ S).prodMap (0 : E →L[ℝ] E)) -
    (InnerProductSpace.toDual ℝ E x.2).comp (ContinuousLinearMap.snd ℝ S E)

omit [CompleteSpace E] in
lemma supportParam_fderiv {Y : S × E → E} {x : S × E}
    (hY : DifferentiableAt ℝ Y x) (v : S × E) :
    fderiv ℝ (supportParam Y) x v = (v.1, fderiv ℝ Y x v) := by
  unfold supportParam
  rw [((hasFDerivAt_fst (p := x)).prodMk hY.hasFDerivAt).fderiv]
  rfl

omit [CompleteSpace E] in
lemma supportParam_second {Y : S × E → E} {x : S × E}
    (hY : ContDiffAt ℝ ∞ Y x) (v w : S × E) :
    fderiv ℝ (fderiv ℝ (supportParam Y)) x v w =
      (0, fderiv ℝ (fderiv ℝ Y) x v w) := by
  have hX : ContDiffAt ℝ ∞ (supportParam Y) x := contDiffAt_fst.prodMk hY
  have hl := ((hX.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.clm_apply
    (hasFDerivAt_const w x)
  have hr := (hasFDerivAt_const w.1 x).prodMk
    (((hY.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt.clm_apply
      (hasFDerivAt_const w x))
  have heq : (fun q => fderiv ℝ (supportParam Y) q w) =ᶠ[𝓝 x]
      (fun q => (w.1, fderiv ℝ Y q w)) := by
    filter_upwards [(hY.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp)]
      with q hq
    exact supportParam_fderiv (hq.differentiableAt (by norm_num)) w
  have he := (hl.congr_of_eventuallyEq heq.symm).unique hr
  simpa using congrArg (fun A : (S × E) →L[ℝ] (S × E) => A v) he

lemma supportConormal_tangent {H : S × E → ℝ} {Y : S × E → E} {x : S × E}
    (hH : DifferentiableAt ℝ H x) (hY : DifferentiableAt ℝ Y x)
    (heul : H =ᶠ[𝓝 x] (fun q => inner ℝ q.2 (Y q)))
    (hgrad : ∀ w : E, fderiv ℝ H x (0,w) = inner ℝ (Y x) w) (v : S × E) :
    supportConormal H x (fderiv ℝ (supportParam Y) x v) = 0 := by
  rw [supportParam_fderiv hY]
  change fderiv ℝ H x (v.1,0) - inner ℝ x.2 (fderiv ℝ Y x v) = 0
  rw [support_tangent_identity hH hY heul hgrad, sub_self]

/- Differentiating the two literal support identities eliminates both mixed
blocks. No stationarity or curvature formula is assumed. -/
omit [CompleteSpace E] in
lemma support_second_inner {H : S × E → ℝ} {Y : S × E → E} {x : S × E}
    (hH : ContDiffAt ℝ ∞ H x) (hY : ContDiffAt ℝ ∞ Y x)
    (heul : H =ᶠ[𝓝 x] (fun q => inner ℝ q.2 (Y q)))
    (hgrad : ∀ᶠ q in 𝓝 x, ∀ w : E, fderiv ℝ H q (0,w) = inner ℝ (Y q) w)
    (v w : S × E) :
    inner ℝ x.2 (fderiv ℝ (fderiv ℝ Y) x v w) =
      fderiv ℝ (fderiv ℝ H) x (v.1,0) (w.1,0) -
        fderiv ℝ (fderiv ℝ H) x (0,v.2) (0,w.2) := by
  have hddH := (hH.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hddY := (hY.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have htan : (fun q => inner ℝ q.2 (fderiv ℝ Y q w)) =ᶠ[𝓝 x]
      (fun q => fderiv ℝ H q (w.1,0)) := by
    filter_upwards [eventually_eventually_nhds.mpr heul, hgrad,
      (hH.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp),
      (hY.of_le (show (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by simp)).eventually (by simp)]
      with q hqe hqg hqH hqY
    exact support_tangent_identity (hqH.differentiableAt (by norm_num))
      (hqY.differentiableAt (by norm_num)) hqe hqg w
  have hl := (hasFDerivAt_snd (p := x)).inner ℝ
    (hddY.hasFDerivAt.clm_apply (hasFDerivAt_const w x))
  have hr := hddH.hasFDerivAt.clm_apply (hasFDerivAt_const (w.1,0) x)
  have h1 := congrArg (fun A : (S × E) →L[ℝ] ℝ => A v)
    ((hl.congr_of_eventuallyEq htan.symm).unique hr)
  have h1' : inner ℝ x.2 (fderiv ℝ (fderiv ℝ Y) x v w) +
      inner ℝ v.2 (fderiv ℝ Y x w) = fderiv ℝ (fderiv ℝ H) x v (w.1,0) := by
    simpa using h1
  have hg : (fun q => fderiv ℝ H q (0,v.2)) =ᶠ[𝓝 x]
      (fun q => inner ℝ (Y q) v.2) := hgrad.mono (fun q hq => hq v.2)
  have hl2 := hddH.hasFDerivAt.clm_apply (hasFDerivAt_const (0,v.2) x)
  have hr2 := (hY.differentiableAt (by simp)).hasFDerivAt.inner ℝ (hasFDerivAt_const v.2 x)
  have h2 := congrArg (fun A : (S × E) →L[ℝ] ℝ => A w)
    ((hl2.congr_of_eventuallyEq hg.symm).unique hr2)
  have h2' : fderiv ℝ (fderiv ℝ H) x w (0,v.2) = inner ℝ v.2 (fderiv ℝ Y x w) := by
    simpa [real_inner_comm] using h2
  have hsym := hH.isSymmSndFDerivAt (by simp)
  have hsplit1 : fderiv ℝ (fderiv ℝ H) x v (w.1,0) =
      fderiv ℝ (fderiv ℝ H) x (v.1,0) (w.1,0) +
        fderiv ℝ (fderiv ℝ H) x (0,v.2) (w.1,0) := by
    rw [← add_apply, ← map_add]
    simp
  have hsplit2 : fderiv ℝ (fderiv ℝ H) x w (0,v.2) =
      fderiv ℝ (fderiv ℝ H) x (0,v.2) (w.1,0) +
        fderiv ℝ (fderiv ℝ H) x (0,v.2) (0,w.2) := by
    rw [hsym.eq w (0,v.2), ← map_add]
    simp
  rw [hsplit1] at h1'
  rw [hsplit2] at h2'
  linarith

/- Source (tube-second-form), as an identity of actual conormal second jets.
It is valid before angular chart restriction, including the radial null line. -/
lemma supportConormal_second {H : S × E → ℝ} {Y : S × E → E} {x : S × E}
    (hH : ContDiffAt ℝ ∞ H x) (hY : ContDiffAt ℝ ∞ Y x)
    (heul : H =ᶠ[𝓝 x] (fun q => inner ℝ q.2 (Y q)))
    (hgrad : ∀ᶠ q in 𝓝 x, ∀ w : E, fderiv ℝ H q (0,w) = inner ℝ (Y q) w)
    (v w : S × E) :
    supportConormal H x (fderiv ℝ (fderiv ℝ (supportParam Y)) x v w) =
      -fderiv ℝ (fderiv ℝ H) x (v.1,0) (w.1,0) +
        fderiv ℝ (fderiv ℝ H) x (0,v.2) (0,w.2) := by
  rw [supportParam_second hY]
  change fderiv ℝ H x (0,0) - inner ℝ x.2 (fderiv ℝ (fderiv ℝ Y) x v w) = _
  rw [show ((0,0) : S × E) = 0 from rfl, map_zero,
    support_second_inner hH hY heul hgrad]
  ring

end AffineBernstein
end

end OAI
