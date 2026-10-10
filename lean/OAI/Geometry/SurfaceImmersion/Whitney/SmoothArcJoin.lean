import OAI.Geometry.SurfaceImmersion.Geometry.LocalMonotoneTransition
import OAI.Geometry.SurfaceImmersion.Correction.SmoothingAtlas

namespace OAI

/-! Smooth joining at a common germ, with regularity and injectivity
retained on the two ordered pieces of the parameter interval. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*}

def joinedCurve (a : ℝ) (γ δ : ℝ → M) (t : ℝ) : M := if t ≤ a then γ t else δ t

lemma joinedCurve_germ_left (a : ℝ) (γ δ : ℝ → M) {t : ℝ} (ht : t < a) :
    joinedCurve a γ δ =ᶠ[𝓝 t] γ := by
  filter_upwards [eventually_lt_nhds ht] with s hs
  simp only [joinedCurve,ite_eq_left hs.le]

lemma joinedCurve_germ_right (a : ℝ) (γ δ : ℝ → M) {t : ℝ} (ht : a < t) :
    joinedCurve a γ δ =ᶠ[𝓝 t] δ := by
  filter_upwards [eventually_gt_nhds ht] with s hs
  simp only [joinedCurve,ite_eq_right (not_le.mpr hs)]

lemma joinedCurve_germ_center (a : ℝ) {γ δ : ℝ → M} (he : γ =ᶠ[𝓝 a] δ) :
    joinedCurve a γ δ =ᶠ[𝓝 a] γ := by
  filter_upwards [he] with s hs
  dsimp only [joinedCurve]
  split_ifs
  · rfl
  · exact hs.symm

section Smooth
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem joinedCurve_smooth_on (a : ℝ) {γ δ : ℝ → M} {U : Set ℝ}
    (hγ : ∀ t ∈ U, t ≤ a → ContMDiffAt 𝓘(ℝ) I ∞ γ t)
    (hδ : ∀ t ∈ U, a ≤ t → ContMDiffAt 𝓘(ℝ) I ∞ δ t)
    (he : γ =ᶠ[𝓝 a] δ) :
    ContMDiffOn 𝓘(ℝ) I ∞ (joinedCurve a γ δ) U := by
  intro t ht
  rcases lt_trichotomy t a with h | heq | h
  · exact ((hγ t ht h.le).congr_of_eventuallyEq (joinedCurve_germ_left a γ δ h)).contMDiffWithinAt
  · subst t
    exact ((hγ a ht le_rfl).congr_of_eventuallyEq (joinedCurve_germ_center a he)).contMDiffWithinAt
  · exact ((hδ t ht h.le).congr_of_eventuallyEq (joinedCurve_germ_right a γ δ h)).contMDiffWithinAt

theorem joinedCurve_regular_on (a : ℝ) {γ δ : ℝ → M} {U : Set ℝ}
    (hγ : ∀ t ∈ U, t ≤ a → Function.Injective (mfderiv 𝓘(ℝ) I γ t))
    (hδ : ∀ t ∈ U, a ≤ t → Function.Injective (mfderiv 𝓘(ℝ) I δ t))
    (he : γ =ᶠ[𝓝 a] δ) :
    ∀ t ∈ U, Function.Injective (mfderiv 𝓘(ℝ) I (joinedCurve a γ δ) t) := by
  intro t ht
  rcases lt_trichotomy t a with h | heq | h
  · rw [(joinedCurve_germ_left a γ δ h).mfderiv_eq]
    exact hγ t ht h.le
  · subst t
    rw [(joinedCurve_germ_center a he).mfderiv_eq]
    exact hγ a ht le_rfl
  · rw [(joinedCurve_germ_right a γ δ h).mfderiv_eq]
    exact hδ t ht h.le

end Smooth

theorem joinedCurve_injective_on (a : ℝ) (γ δ : ℝ → M) (U : Set ℝ)
    (hγ : (U ∩ Iic a).InjOn γ) (hδ : (U ∩ Ioi a).InjOn δ)
    (hcross : ∀ s ∈ U, s ≤ a → ∀ t ∈ U, a < t → γ s ≠ δ t) :
    U.InjOn (joinedCurve a γ δ) := by
  intro s hs t ht he
  by_cases hsa : s ≤ a <;> by_cases hta : t ≤ a
  · exact hγ ⟨hs,hsa⟩ ⟨ht,hta⟩ (by simpa [joinedCurve,hsa,hta] using he)
  · exact False.elim (hcross s hs hsa t ht (lt_of_not_ge hta) (by simpa [joinedCurve,hsa,hta] using he))
  · exact False.elim (hcross t ht hta s hs (lt_of_not_ge hsa) (by simpa [joinedCurve,hsa,hta] using he.symm))
  · exact hδ ⟨hs,lt_of_not_ge hsa⟩ ⟨ht,lt_of_not_ge hta⟩ (by simpa [joinedCurve,hsa,hta] using he)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
