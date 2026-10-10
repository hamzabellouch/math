import Mathlib
import OAI.Geometry.PrescribedPotential.AnalyticSupport
import OAI.Geometry.PrescribedPotential.CircleRadialCalculus

namespace OAI

/-! Contact Set A B P. -/

section

 

noncomputable section
open Set Filter Topology Metric MeasureTheory
open scoped ContDiff InnerProductSpace
namespace PotentialABP
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

 
def contacts (u : E → ℝ) (c : E) (r a : ℝ) : Set E :=
  {x | x ∈ closedBall c r ∧ ‖gradient u x‖ ≤ a ∧
    ∀ y ∈ closedBall c r, u x + inner ℝ (gradient u x) (y-x) ≤ u y}

lemma gradient_continuous {u : E → ℝ} (hu : ContDiff ℝ ∞ u) :
    Continuous (gradient u) := by
  exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp
    (hu.continuous_fderiv (by simp))

lemma contacts_isClosed {u : E → ℝ} (hu : ContDiff ℝ ∞ u) (c : E) (r a : ℝ) :
    IsClosed (contacts u c r a) := by
  have hg := gradient_continuous hu
  change IsClosed (closedBall c r ∩ ({x | ‖gradient u x‖ ≤ a} ∩
    {x | ∀ y ∈ closedBall c r, u x + inner ℝ (gradient u x) (y-x) ≤ u y}))
  apply isClosed_closedBall.inter
  apply IsClosed.inter (isClosed_le hg.norm continuous_const)
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro y
  apply isClosed_iInter
  intro _
  exact isClosed_le (hu.continuous.add (hg.inner (continuous_const.sub continuous_id)))
    continuous_const

lemma contacts_sublevel {u : E → ℝ} {c : E} {r a : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a)
    {x : E} (hx : x ∈ contacts u c r a) : u x ≤ u c + a*r := by
  have h := hx.2.2 c (mem_closedBall_self hr)
  have hinner : - (a*r) ≤ inner ℝ (gradient u x) (c-x) := by
    have hnorm : ‖c-x‖ ≤ r := by simpa [dist_eq_norm, norm_sub_rev] using hx.1
    have hb := abs_real_inner_le_norm (gradient u x) (c-x)
    have hc := mul_le_mul hx.2.1 hnorm (norm_nonneg _) ha
    exact le_trans (neg_le_neg hc) ((abs_le.mp hb).1)
  linarith

lemma contacts_interior {u : E → ℝ} {c : E} {r a b : ℝ}
    (hr : 0 < r) (ha : 0 ≤ a) (hgap : a*r < b)
    (hboundary : ∀ x, dist x c = r → u c + b ≤ u x) :
    contacts u c r a ⊆ ball c r := by
  intro x hx
  have hs := contacts_sublevel hr.le ha hx
  have hd : dist x c ≤ r := hx.1
  apply lt_of_le_of_ne hd
  intro he
  linarith [hboundary x he]

lemma tilted_minimum_gradient {u : E → ℝ} (hu : ContDiff ℝ ∞ u)
    {c : E} {r : ℝ} {x p : E} (hx : x ∈ ball c r)
    (hm : IsMinOn (fun y => u y - inner ℝ p (y-c)) (closedBall c r) x) :
    gradient u x = p := by
  have hloc : IsLocalMin (fun y => u y - inner ℝ p (y-c)) x := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact hm (ball_subset_closedBall hy)
  have hp : HasFDerivAt (fun y : E => inner ℝ p (y-c))
      (InnerProductSpace.toDual ℝ E p) x := by
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq, InnerProductSpace.toDual_apply_apply] using
      (InnerProductSpace.toDual ℝ E p).hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub_const c)
  have hd := ((hu.differentiable (by simp) x).hasFDerivAt.sub hp).fderiv
  change fderiv ℝ (fun y => u y - inner ℝ p (y-c)) x = _ at hd
  rw [hloc.fderiv_eq_zero] at hd
  apply (InnerProductSpace.toDual ℝ E).injective
  rw [toDual_gradient]
  exact sub_eq_zero.mp hd.symm

 

lemma gradient_image_contacts {u : E → ℝ} (hu : ContDiff ℝ ∞ u)
    {c : E} {r a b : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (hgap : a*r < b)
    (hboundary : ∀ x, dist x c = r → u c + b ≤ u x) :
    closedBall (0:E) a ⊆ gradient u '' contacts u c r a := by
  intro p hp
  have hp' : ‖p‖ ≤ a := by simpa using hp
  have hcont : Continuous (fun y => u y - inner ℝ p (y-c)) :=
    hu.continuous.sub (continuous_const.inner (continuous_id.sub continuous_const))
  obtain ⟨x,hx,hm⟩ := (isCompact_closedBall c r).exists_isMinOn
    ⟨c,mem_closedBall_self hr.le⟩
    hcont.continuousOn
  have hmin : u x - inner ℝ p (x-c) ≤ u c - inner ℝ p (c-c) :=
    hm (mem_closedBall_self hr.le)
  have hupper : u x ≤ u c + a*r := by
    have hh := (real_inner_le_norm p (x-c)).trans
      (mul_le_mul hp' (by simpa [dist_eq_norm] using hx) (norm_nonneg _) ha)
    simp only [sub_self, inner_zero_right, sub_zero] at hmin
    linarith
  have hxi : x ∈ ball c r := by
    change dist x c < r
    apply lt_of_le_of_ne (show dist x c ≤ r from hx)
    intro he
    linarith [hboundary x he]
  have hg := tilted_minimum_gradient hu hxi hm
  refine ⟨x,⟨hx,by simpa [hg] using hp',?_⟩,hg⟩
  intro y hy
  have he : u x - inner ℝ p (x-c) ≤ u y - inner ℝ p (y-c) := hm hy
  rw [hg]
  have hi : inner ℝ p (y-x) = inner ℝ p (y-c) - inner ℝ p (x-c) := by
    rw [← inner_sub_right]
    congr 1
    abel
  rw [hi]
  linarith

lemma gradient_contDiff {u : E → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (gradient u) := by
  exact (InnerProductSpace.toDual ℝ E).symm.contDiff.comp
    (hu.fderiv_right (by simp))

 

lemma contact_measure_estimate [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {u : E → ℝ} (hu : ContDiff ℝ ∞ u) {c : E} {r a b C : ℝ}
    (hr : 0 < r) (ha : 0 ≤ a) (hgap : a*r < b)
    (hboundary : ∀ x, dist x c = r → u c + b ≤ u x)
    (hdet : ∀ x ∈ contacts u c r a,
      |(fderiv ℝ (gradient u) x).det| ≤ C) :
    μ (closedBall (0:E) a) ≤ ENNReal.ofReal C * μ (contacts u c r a) := by
  have hs := (contacts_isClosed hu c r a).measurableSet
  calc
    μ (closedBall (0:E) a) ≤ μ (gradient u '' contacts u c r a) :=
      measure_mono (gradient_image_contacts hu hr ha hgap hboundary)
    _ ≤ ∫⁻ x in contacts u c r a, ENNReal.ofReal |(fderiv ℝ (gradient u) x).det| ∂μ :=
      addHaar_image_le_lintegral_abs_det_fderiv μ hs
        (fun x _ => ((gradient_contDiff hu).differentiable (by simp) x).hasFDerivAt.hasFDerivWithinAt)
    _ ≤ ∫⁻ _ in contacts u c r a, ENNReal.ofReal C ∂μ :=
      setLIntegral_mono' hs (fun x hx => ENNReal.ofReal_le_ofReal (hdet x hx))
    _ = ENNReal.ofReal C * μ (contacts u c r a) := by simp

 
lemma contacts_hessian_nonneg {u : E → ℝ} (hu : ContDiff ℝ ∞ u)
    {c : E} {r a : ℝ} {x : E} (hx : x ∈ contacts u c r a)
    (hxi : x ∈ ball c r) (v : E) :
    0 ≤ fderiv ℝ (fderiv ℝ u) x v v := by
  let p := gradient u x
  let l : E → ℝ := fun y => u x + inner ℝ p (y-x)
  have hl : HasFDerivAt l (InnerProductSpace.toDual ℝ E p) x := by
    simpa [l, ContinuousLinearMap.comp_id, Function.comp_def, id_eq,
      InnerProductSpace.toDual_apply_apply] using
      ((InnerProductSpace.toDual ℝ E p).hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub_const x)).const_add (u x)
  have hld (y : E) : fderiv ℝ l y = InnerProductSpace.toDual ℝ E p := by
    simpa [l, ContinuousLinearMap.comp_id, Function.comp_def, id_eq,
      InnerProductSpace.toDual_apply_apply] using
      ((InnerProductSpace.toDual ℝ E p).hasFDerivAt.comp y
        ((hasFDerivAt_id y).sub_const x)).const_add (u x) |>.fderiv
  have hlc : ContDiff ℝ ∞ l := contDiff_const.add
    (ContDiff.inner ℝ contDiff_const (contDiff_id.sub contDiff_const))
  have hmax : IsLocalMax (fun y => l y - u y) x := by
    filter_upwards [isOpen_ball.mem_nhds hxi] with y hy
    have hh := hx.2.2 y (ball_subset_closedBall hy)
    simpa [l, p] using (sub_nonpos.mpr hh)
  have hs := EllipticKernel.second_fderiv_nonpos_at_localMax
    (hlc.sub hu).contDiffAt hmax v
  have he : fderiv ℝ (fun y => l y - u y) =
      fun y => InnerProductSpace.toDual ℝ E p - fderiv ℝ u y := by
    funext y
    change fderiv ℝ (l - u) y = _
    rw [fderiv_sub (hlc.differentiable (by simp) y) (hu.differentiable (by simp) y), hld]
  rw [he, fderiv_const_sub] at hs
  simpa using hs

end PotentialABP

end
end

end OAI
