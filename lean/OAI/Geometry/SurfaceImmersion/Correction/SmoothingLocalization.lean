import OAI.Geometry.SurfaceImmersion.Correction.SmoothingAtlas

namespace OAI

/-! Compactly supported coordinate representatives for smoothing. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

def localize (p : M) (ψ : M → ℝ) (f : M → V) : Base → V :=
  (chart p).target.indicator (fun x => (ψ ((chart p).symm x)) ^ 2 • f ((chart p).symm x))

lemma localize_chart (p : M) (ψ : M → ℝ) (f : M → V) {x : M}
    (hx : x ∈ (chart p).source) :
    localize p ψ f (chart p x) = (ψ x) ^ 2 • f x := by
  rw [localize, indicator_of_mem ((chart p).map_source hx), (chart p).left_inv hx]

lemma localize_zero_off_image (p : M) (ψ : M → ℝ) (f : M → V) {x : Base}
    (hx : x ∉ (chart p) '' tsupport ψ) : localize p ψ f x = 0 := by
  by_cases ht : x ∈ (chart p).target
  · have hψ : ψ ((chart p).symm x) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hp
      exact hx ⟨(chart p).symm x, hp, (chart p).right_inv ht⟩
    simp only [localize, indicator_of_mem ht, hψ, zero_pow (by decide : 2 ≠ 0), zero_smul]
  · exact indicator_of_notMem ht _

variable [CompactSpace M]

lemma localize_tsupport (p : M) {ψ : M → ℝ} (hψ : tsupport ψ ⊆ (chart p).source)
    (f : M → V) : tsupport (localize p ψ f) ⊆ (chart p) '' tsupport ψ := by
  have hK : IsCompact ((chart p) '' tsupport ψ) :=
    (isClosed_tsupport ψ).isCompact.image_of_continuousOn ((chart p).continuousOn.mono hψ)
  apply closure_minimal _ hK.isClosed
  intro x hx
  by_contra hn
  exact hx (localize_zero_off_image p ψ f hn)

lemma localize_compact (p : M) {ψ : M → ℝ} (hψ : tsupport ψ ⊆ (chart p).source)
    (f : M → V) : HasCompactSupport (localize p ψ f) :=
  ((isClosed_tsupport ψ).isCompact.image_of_continuousOn
    ((chart p).continuousOn.mono hψ)).of_isClosed_subset (isClosed_tsupport _) (localize_tsupport p hψ f)

/-- Both scalar localization and input support are retained in coordinates. -/
lemma localize_tsupport_inter (p : M) {ψ : M → ℝ}
    (hψ : tsupport ψ ⊆ (chart p).source) (f : M → V) :
    tsupport (localize p ψ f) ⊆ (chart p) '' (tsupport ψ ∩ tsupport f) := by
  have hsub : tsupport ψ ∩ tsupport f ⊆ (chart p).source := fun _ hx => hψ hx.1
  have hK : IsCompact ((chart p) '' (tsupport ψ ∩ tsupport f)) :=
    ((isClosed_tsupport ψ).inter (isClosed_tsupport f)).isCompact.image_of_continuousOn
      ((chart p).continuousOn.mono hsub)
  apply closure_minimal _ hK.isClosed
  intro x hx
  by_cases ht : x ∈ (chart p).target
  · by_contra hn
    have heq : localize p ψ f x = 0 := by
      by_cases ha : ψ ((chart p).symm x) = 0
      · simp [localize, ht, ha]
      by_cases hb : f ((chart p).symm x) = 0
      · simp [localize, ht, hb]
      exact False.elim (hn ⟨(chart p).symm x,
        ⟨subset_tsupport ψ ha, subset_tsupport f hb⟩, (chart p).right_inv ht⟩)
    exact hx heq
  · exact False.elim (hx (indicator_of_notMem ht _))

variable [IsManifold planeModel ∞ M]

/-- Extension by zero is smooth because the localization support lies in a
compact subset of the chart target. -/
lemma localize_smooth (p : M) {ψ : M → ℝ} (hψ : ContMDiff planeModel 𝓘(ℝ) ∞ ψ)
    (hsupp : tsupport ψ ⊆ (chart p).source) {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ, V) ∞ f) : ContDiff ℝ ∞ (localize p ψ f) := by
  have hlocal : ContDiffOn ℝ ∞
      (fun x => (ψ ((chart p).symm x)) ^ 2 • f ((chart p).symm x)) (chart p).target := by
    exact (((hψ.comp_contMDiffOn (chart_symm_smooth p)).pow 2).smul
      (hf.comp_contMDiffOn (chart_symm_smooth p))).contDiffOn
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport (localize p ψ f)
  case neg => exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hx)
  have hxI := localize_tsupport p hsupp f hx
  obtain ⟨y, hy, hxy⟩ := hxI
  have hxT : x ∈ (chart p).target := hxy ▸ (chart p).map_source (hsupp hy)
  apply (hlocal.contDiffAt ((chart p).open_target.mem_nhds hxT)).congr_of_eventuallyEq
  filter_upwards [(chart p).open_target.mem_nhds hxT] with z hz
  exact indicator_of_mem hz _

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
