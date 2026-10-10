import OAI.Geometry.SurfaceImmersion.Geometry.C1LocalizedComposition
import OAI.Geometry.SurfaceImmersion.Correction.SmoothingC1Approximation
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasWeightedBounds

namespace OAI

/-! Smoothing C1 maps on the fixed finite surface atlas. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma localize_C1 (p : M) {ψ : M → ℝ} (hψ : ContMDiff planeModel 𝓘(ℝ) ∞ ψ)
    (hsupp : tsupport ψ ⊆ (chart p).source) {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ, V) 1 f) : ContDiff ℝ 1 (localize p ψ f) := by
  have hchart := (chart_symm_smooth p).of_le (by simp : (1 : ℕ∞ω) ≤ ∞)
  have hlocal : ContDiffOn ℝ 1
      (fun x => (ψ ((chart p).symm x)) ^ 2 • f ((chart p).symm x)) (chart p).target :=
    ((((hψ.of_le (by simp)).comp_contMDiffOn hchart).pow 2).smul
      (hf.comp_contMDiffOn hchart)).contDiffOn
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport (localize p ψ f)
  · obtain ⟨y,hy,hxy⟩ := localize_tsupport p hsupp f hx
    have hxT : x ∈ (chart p).target := hxy ▸ (chart p).map_source (hsupp hy)
    apply (hlocal.contDiffAt ((chart p).open_target.mem_nhds hxT)).congr_of_eventuallyEq
    filter_upwards [(chart p).open_target.mem_nhds hxT] with z hz
    exact indicator_of_mem hz _
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hx)

omit [CompactSpace M] in
lemma restore_C1 (p : M) {χ : M → ℝ} (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ)
    (hs : tsupport χ ⊆ (chart p).source) {h : Base → V} (hh : ContDiff ℝ 1 h) :
    ContMDiff planeModel 𝓘(ℝ, V) 1 (restore p χ h) := by
  have heq : restore p χ h = fun x => χ x • h (chart p x) := by
    funext x
    by_cases hx : x ∈ (chart p).source
    · simp [restore,hx]
    · have hz : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
      simp [restore,hx,hz]
  rw [heq]
  apply contMDiff_of_tsupport
  intro x hx
  have hxχ : x ∈ tsupport χ := tsupport_smul_subset_left χ (fun y => h (chart p y)) hx
  have hxs := hs hxχ
  have hlocal : ContMDiffOn planeModel 𝓘(ℝ,V) 1
      (fun x => χ x • h (chart p x)) (chart p).source :=
    (hχ.of_le (by simp)).contMDiffOn.smul
      (hh.contMDiff.comp_contMDiffOn ((chart_smooth p).of_le (by simp)))
  exact (hlocal x hxs).contMDiffAt ((chart p).open_source.mem_nhds hxs)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- The already defined first-order finite smoother is smooth even when its
input map has only one derivative. -/
lemma smooth_C1_input {s : ℝ} (hs : 0 < s) {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ, V) 1 f) :
    ContMDiff planeModel 𝓘(ℝ, V) ∞ (A.smooth 1 s f) := by
  have heq : A.smooth 1 s f = fun x => ∑ i : A.centers,
      restore (i : M) (A.outer i) (finiteSmooth 1 s (localize (i : M) (A.weight i) f)) x := by
    funext x
    simp only [smooth,Finset.sum_apply]
  rw [heq]
  apply ContMDiff.sum
  intro i _
  apply restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
  have hi := localize_C1 (i : M) (A.weight_smooth i) (A.weight_support i) hf
  simpa only [finiteSmooth,Finset.sum_range_one,residual] using
    (FiniteOrderSmoothing.smooth_smooth 0 hs hi.continuous.locallyIntegrable)

/-- The value and derivative bounds used to preserve immersion under smoothing. -/
def C1Bound (C : ℝ) (f : M → V) : Prop :=
  ∀ i : A.centers, ∀ x : Base,
    ‖localize (i : M) (A.weight i) f x‖ ≤ C ∧
    ‖fderiv ℝ (localize (i : M) (A.weight i) f) x‖ ≤ C

theorem restoration_C1_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ (h : A.centers → Base → V) (C : ℝ), 0 ≤ C →
      (∀ i, ContDiff ℝ 1 (h i)) →
      (∀ i x, ‖h i x‖ ≤ C ∧ ‖fderiv ℝ (h i) x‖ ≤ C) →
      A.C1Bound (D*C) (∑ i : A.centers, restore (i : M) (A.outer i) (h i)) := by
  classical
  choose D hD hb using fun i j : A.centers => compact_localized_C1_bound (V := V)
    (transition (i : M) (j : M)).open_source (A.pairSupport_compact i j)
    (A.pairSupport_transition i j) (A.pairWeight_smooth i j) (A.pairWeight_support i j)
    (transition_smooth (i : M) (j : M))
  let S := ∑ i : A.centers, ∑ j : A.centers, D i j
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hD i j))
  refine ⟨1+S,by linarith,?_⟩
  intro h C hC hh hnorm i x
  let H : A.centers → Base → V := fun j =>
    localize (i : M) (A.weight i) (restore (j : M) (A.outer j) (h j))
  have hH (j : A.centers) : ContDiff ℝ 1 (H j) := by
    dsimp [H]
    rw [A.localize_restore]
    exact localizedComposition_C1 (transition (i : M) (j : M)).open_source
      (A.pairWeight_smooth i j) ((A.pairWeight_support i j).trans (A.pairSupport_transition i j))
      (transition_smooth (i : M) (j : M)) (hh j)
  have hHb (j : A.centers) : ‖H j x‖ ≤ D i j*C ∧ ‖fderiv ℝ (H j) x‖ ≤ D i j*C := by
    dsimp [H]
    rw [A.localize_restore]
    exact hb i j (h j) C hC (hh j) (hnorm j) x
  have hsum : (∑ j : A.centers, D i j)*C ≤ (1+S)*C := by
    apply mul_le_mul_of_nonneg_right _ hC
    have ht : (∑ j : A.centers, D i j) ≤ S :=
      Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun j _ => hD k j)) (Finset.mem_univ i)
    linarith
  change ‖localize (i : M) (A.weight i) (∑ j : A.centers, restore (j : M) (A.outer j) (h j)) x‖ ≤ _ ∧ _
  rw [localize_sum]
  constructor
  · exact ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => (hHb j).1))).trans
      (by simpa only [Finset.sum_mul] using hsum)
  · rw [fderiv_fun_sum (fun j _ => (hH j).differentiable one_ne_zero x)]
    exact ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => (hHb j).2))).trans
      (by simpa only [Finset.sum_mul] using hsum)

variable [CompleteSpace V]

/-- The fixed atlas smoother converges in C1 for C1 input maps. -/
theorem smooth_C1_approximation {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ,V) 1 f) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 0 < s → s < η →
      ContMDiff planeModel 𝓘(ℝ,V) ∞ (A.smooth 1 s f) ∧
      A.C1Bound ε (A.smooth 1 s f-f) := by
  classical
  obtain ⟨D,hD,hrestore⟩ := A.restoration_C1_bound (V := V)
  let l : A.centers → Base → V := fun i => localize (i : M) (A.weight i) f
  have hl (i : A.centers) : ContDiff ℝ 1 (l i) :=
    localize_C1 (i : M) (A.weight_smooth i) (A.weight_support i) hf
  have hlc (i : A.centers) : HasCompactSupport (l i) :=
    localize_compact (i : M) (A.weight_support i) f
  choose η hη hb using fun i : A.centers =>
    FiniteOrderSmoothing.smooth_C1_approximation 0 (hl i) (hlc i) (div_pos hε hD)
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ i : A.centers, s < η i :=
    Filter.eventually_all.mpr (fun i => gt_mem_nhds (hη i))
  obtain ⟨r,hr,hrb⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨r,hr,?_⟩
  intro s hs hsr
  have hsi (i : A.centers) : s < η i :=
    hrb (by simpa only [Real.dist_eq,sub_zero,abs_of_pos hs] using hsr) i
  let e : A.centers → Base → V := fun i => FiniteOrderSmoothing.smooth 0 s (l i)-l i
  have he (i : A.centers) : ContDiff ℝ 1 (e i) :=
    ((hb i s hs (hsi i)).1.of_le (by simp)).sub (hl i)
  have heb (i : A.centers) (x : Base) :
      ‖e i x‖ ≤ ε/D ∧ ‖fderiv ℝ (e i) x‖ ≤ ε/D := by
    have hh := (hb i s hs (hsi i)).2 x
    refine ⟨hh.1,?_⟩
    change ‖fderiv ℝ (FiniteOrderSmoothing.smooth 0 s (l i)-l i) x‖ ≤ _
    rw [fderiv_sub ((hb i s hs (hsi i)).1.differentiable (by simp) x)
      ((hl i).differentiable one_ne_zero x)]
    exact hh.2
  have hsum := hrestore e (ε/D) (div_nonneg hε.le hD.le) he heb
  have heq : (∑ i : A.centers, restore (i : M) (A.outer i) (e i)) = A.smooth 1 s f-f := by
    simp only [e,restore_sub,Finset.sum_sub_distrib]
    change (∑ i : A.centers, restore (i : M) (A.outer i)
      (FiniteOrderSmoothing.smooth 0 s (l i))) -
      (∑ i : A.centers, restore (i : M) (A.outer i)
        (localize (i : M) (A.weight i) f)) = _
    rw [A.sum_restore_localize]
    congr 1
    simp only [l,smooth,finiteSmooth,Finset.sum_range_one,residual]
  refine ⟨A.smooth_C1_input hs hf,?_⟩
  rw [heq] at hsum
  simpa only [mul_div_cancel₀ _ hD.ne'] using hsum

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
