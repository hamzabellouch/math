import Mathlib
import OAI.Analysis.AffineBernstein.ModelCentering
import OAI.Analysis.AffineBernstein.NormedInteriorLimits

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open Filter Metric
open scoped Topology Pointwise
open scoped Pointwise
open scoped Pointwise

section NormedCompactInterior
open Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/- Compact inner containment for the literal (possibly non-Hilbert) ambient
norm. In particular the product coordinate norm creates no hidden instance. -/
theorem LocalDistanceConverges.eventually_normed_compact_subset
    {Cj : ℕ → Set E} {C S : Set E} (h : LocalDistanceConverges Cj C)
    (hclj : ∀ j, IsClosed (Cj j)) (hcvj : ∀ j, Convex ℝ (Cj j))
    (hnej : ∀ j, (Cj j).Nonempty) (hS : IsCompact S)
    (hSC : S ⊆ interior C) : ∀ᶠ j in atTop, S ⊆ Cj j := by
  classical
  have hex : ∀ x : S, ∃ r > 0, Metric.closedBall (x : E) r ⊆ C := by
    intro x
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior (x : E) (hSC x.2)
    exact ⟨r / 2, half_pos hr, (Metric.closedBall_subset_ball (by linarith)).trans
      (hball.trans interior_subset)⟩
  choose r hr hball using hex
  obtain ⟨t, ht⟩ := hS.elim_nhds_subcover' (fun x hx => Metric.ball x (r ⟨x, hx⟩ / 4))
    (fun x hx => Metric.ball_mem_nhds x (div_pos (hr ⟨x,hx⟩) (by norm_num)))
  have he : ∀ x ∈ t, ∀ᶠ j in atTop, Metric.ball (x : E) (r x / 4) ⊆ Cj j :=
    fun x _ => h.eventually_normed_ball_subset hclj hcvj hnej (hr x) (hball x)
  filter_upwards [(t.eventually_all).mpr he] with j hj
  intro x hx
  obtain ⟨y, hyt, hxy⟩ := mem_iUnion₂.mp (ht hx)
  exact hj y hyt hxy
end NormedCompactInterior
open Filter Metric
open scoped Topology Pointwise

/- The lower inclusion in geometry.tex (normalized-fiber-box), with the
source's exact radius a*r. It is a convexity/recession consequence. -/
lemma IsModelShape.fiber_small_ball {k m : ℕ} {C : Set (Space k × Space m)}
    (hC : IsModelShape C) {r a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hin : closedBall (0 : Space m) r ⊆
      modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))))
    {s : Space k} (hs : ∀ i, a ≤ s i) :
    closedBall (0 : Space m) (a*r) ⊆ modelFiber C s := by
  intro y hy
  have hny : ‖y‖ ≤ a*r := by simpa only [mem_closedBall,dist_zero_right] using hy
  have hz : a⁻¹ • y ∈ closedBall (0 : Space m) r := by
    rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha)]
    exact (inv_mul_le_iff₀ ha).mpr hny
  have hc := hC.convex.smul_mem_of_zero_mem hC.zero_mem (hin hz) ⟨ha.le,ha1⟩
  have hc' : y ∈ modelFiber C (a • WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) := by
    simpa only [modelFiber,mem_ofPred_eq,Prod.smul_mk,smul_smul,
      mul_inv_cancel₀ ha.ne',one_smul] using hc
  exact hC.fiber_mono (fun i => by simpa using hs i) hc'

lemma IsModelShape.normalized_fiber_box {k m : ℕ} {C : Set (Space k × Space m)}
    (hC : IsModelShape C) {r R a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hb : 1 ≤ b)
    (hin : closedBall (0 : Space m) r ⊆
      modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))))
    (hout : modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))) ⊆ closedBall 0 R)
    {s : Space k} (hs : ∀ i, s i ∈ Icc a b) :
    closedBall (0 : Space m) (a*r) ⊆ modelFiber C s ∧
      modelFiber C s ⊆ closedBall 0 (b*R) := by
  refine ⟨hC.fiber_small_ball ha ha1 hin (fun i => (hs i).1),?_⟩
  intro y hy
  exact mem_closedBall_zero_iff.mpr (hC.fiber_box_bound hb hout (fun i => (hs i).2) hy)

/- Strictly smaller transverse balls over a positive box lie in the actual
ambient interior; this is what local convex-set convergence transfers. -/
lemma IsModelShape.normalized_fiber_interior {k m : ℕ} {C : Set (Space k × Space m)}
    (hC : IsModelShape C) {r a : ℝ} (hr : 0 < r) (ha : 0 < a) (ha1 : a ≤ 1)
    (hin : closedBall (0 : Space m) r ⊆
      modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ))))
    {s : Space k} (hs : ∀ i, a ≤ s i) {y : Space m} (hy : ‖y‖ ≤ a*r/2) :
    (s,y) ∈ interior C := by
  let U : Set (Space k × Space m) := {p | (∀ i, 3*a/4 < p.1 i) ∧ ‖p.2‖ < 3*a*r/4}
  have hU : IsOpen U := by
    have hi (i : Fin k) : IsOpen {p : Space k × Space m | 3*a/4 < p.1 i} :=
      isOpen_lt continuous_const
        ((PiLp.continuous_apply 2 (fun _ : Fin k => ℝ) i).comp continuous_fst)
    have he : U = (⋂ i : Fin k, {p : Space k × Space m | 3*a/4 < p.1 i}) ∩
        {p : Space k × Space m | ‖p.2‖ < 3*a*r/4} := by ext p; simp [U]
    rw [he]
    exact (isOpen_iInter_of_finite hi).inter
      (isOpen_lt (continuous_snd.norm) continuous_const)
  have hz : (s,y) ∈ U := by
    refine ⟨fun i => by dsimp; linarith [hs i],?_⟩
    dsimp
    nlinarith
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (hU.mem_nhds hz)
  intro p hp
  exact hC.fiber_small_ball (a := 3*a/4) (by positivity) (by linarith) hin
    (fun i => (hp.1 i).le) (mem_closedBall_zero_iff.mpr (by nlinarith [hp.2]))

/- Centering gives the exact normalization constants before the model and
positive fiber are selected. No compactness modulus or analytic estimate is
assumed. This is the first part of the manuscript's normalized-fibers corollary. -/
theorem uniform_model_fiber_normalization {k m : ℕ} (hm : 1 ≤ m)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {D : Set E} (hD : IsClosed D) (hneD : D.Nonempty)
    (hmax : ∀ (d : ℕ), m = d+1 → ∀ C' : Set (Space (k+1) × Space d),
      IsModelShape C' → InAffineLimitFamily D C' → False) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ C : Set (Space k × Space m),
      IsModelShape C → InAffineLimitFamily D C → ∀ s : Space k, ∀ hs : ∀ i, 0 < s i,
      ∃ A : Space m ≃L[ℝ] Space m,
        let C' := ((positiveBaseEquiv s hs).prodCongr A) '' C
        IsModelShape C' ∧ InAffineLimitFamily D C' ∧
        closedBall 0 (2/(c+1)) ⊆ modelFiber C' (WithLp.toLp 2 (fun _ => (1:ℝ))) ∧
        modelFiber C' (WithLp.toLp 2 (fun _ => (1:ℝ))) ⊆ closedBall 0 (2*m) := by
  obtain ⟨c,hc,hcenter⟩ := uniform_centering hD hneD hmax
  refine ⟨c,hc,?_⟩
  intro C hC hf s hs
  obtain ⟨A,hin,hout⟩ := centered_body_normalization hm
    (hC.fiber_compact (fun i => (hs i).le)) (hC.fiber_convex s)
    (hC.fiber_interior_nonempty hs) (hC.fiber_zero (fun i => (hs i).le)) hc
    (hcenter C hC hf s hs)
  refine ⟨A,?_⟩
  let C₁ := ((positiveBaseEquiv s hs).prodCongr (ContinuousLinearEquiv.refl ℝ (Space m))) '' C
  have he : ((ContinuousLinearEquiv.refl ℝ (Space k)).prodCongr A) '' C₁ =
      ((positiveBaseEquiv s hs).prodCongr A) '' C := by
    dsimp only [C₁]
    rw [Set.image_image]
    rfl
  have hfib : modelFiber (((positiveBaseEquiv s hs).prodCongr A) '' C)
      (WithLp.toLp 2 (fun _ => (1:ℝ))) = A '' modelFiber C s := by
    rw [← he,fiber_transverse_image]
    congr 1
    exact fiber_positive_base_image s hs
  refine ⟨?_,hf.affine_image hD hneD
    (((positiveBaseEquiv s hs).prodCongr A).toContinuousAffineEquiv),?_,?_⟩
  · rw [← he]
    exact (hC.positive_base_image s hs).transverse_image A
  · simpa only [hfib] using hin
  · simpa only [hfib] using hout

/- The lower-box bound transfers to every approximant simultaneously over
that box, not separately at each s. The radius is uniform in the model. -/
theorem LocalDistanceConverges.eventually_normalized_fiber_inner
    {k m : ℕ} {Cj : ℕ → Set (Space k × Space m)} {C : Set (Space k × Space m)}
    (h : LocalDistanceConverges Cj C) (hC : IsModelShape C)
    (hclj : ∀ j, IsClosed (Cj j)) (hcvj : ∀ j, Convex ℝ (Cj j))
    (hnej : ∀ j, (Cj j).Nonempty) {r a b : ℝ}
    (hr : 0 < r) (ha : 0 < a) (ha1 : a ≤ 1)
    (hin : closedBall (0 : Space m) r ⊆
      modelFiber C (WithLp.toLp 2 (fun _ : Fin k => (1:ℝ)))) :
    ∀ᶠ j in atTop, ∀ s : Space k, (∀ i, s i ∈ Icc a b) →
      closedBall (0 : Space m) (a*r/2) ⊆ modelFiber (Cj j) s := by
  let Q : Set (Space k) := {s | ∀ i, s i ∈ Icc a b}
  have hQ : IsCompact Q := by
    convert! (PiLp.homeomorph 2 (fun _ : Fin k => ℝ)).isCompact_preimage.mpr
      (isCompact_univ_pi fun _ : Fin k => (isCompact_Icc : IsCompact (Icc a b))) using 1
    ext s
    simp only [Q, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_univ_pi, Set.mem_Icc]
    rfl
  have hi : Q ×ˢ closedBall (0 : Space m) (a*r/2) ⊆ interior C := by
    rintro ⟨s,y⟩ ⟨hs,hy⟩
    exact hC.normalized_fiber_interior hr ha ha1 hin (fun i => (hs i).1)
      (mem_closedBall_zero_iff.mp hy)
  filter_upwards [h.eventually_normed_compact_subset hclj hcvj hnej
    (hQ.prod (isCompact_closedBall _ _)) hi] with j hj s hs y hy
  exact hj ⟨hs,hy⟩

end AffineBernstein
end

end OAI
