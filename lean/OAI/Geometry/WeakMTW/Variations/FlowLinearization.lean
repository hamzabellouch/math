import Mathlib
import OAI.Geometry.WeakMTW.Variations.CurveCalculus

namespace OAI

namespace WeakMTWGlobalSupport

section
open Set Filter
open scoped Topology ContDiff
open Set Filter InnerProductSpace
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
namespace FlowLinearization
open Set Filter
open scoped Topology ContDiff
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem unique_Icc {f : E → E} {u v : ℝ → E} {a b : ℝ}
    (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hf : ∀ z ∈ u '' Icc a b ∪ v '' Icc a b, ContDiffAt ℝ 1 f z)
    (hdu : ∀ t ∈ Icc a b, HasDerivWithinAt u (f (u t)) (Icc a b) t)
    (hdv : ∀ t ∈ Icc a b, HasDerivWithinAt v (f (v t)) (Icc a b) t)
    (h0 : u a = v a) : EqOn u v (Icc a b) := by
  let S := u '' Icc a b ∪ v '' Icc a b
  have hS : IsCompact S := (isCompact_Icc.image_of_continuousOn hu).union
    (isCompact_Icc.image_of_continuousOn hv)
  have hloc : LocallyLipschitzOn S f := by
    intro z hz
    obtain ⟨K, A, hA, hLip⟩ := (hf z hz).exists_lipschitzOnWith
    exact ⟨K, A, mem_nhdsWithin_of_mem_nhds hA, hLip⟩
  obtain ⟨K, hK⟩ := hloc.exists_lipschitzOnWith_of_compact hS
  exact ODE_solution_unique_of_mem_Icc_right (fun _ _ => hK) hu
    (fun t ht => (hdu t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))
    (fun t ht => Or.inl (mem_image_of_mem _ (Ico_subset_Icc_self ht))) hv
    (fun t ht => (hdv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))
    (fun t ht => Or.inr (mem_image_of_mem _ (Ico_subset_Icc_self ht))) h0

theorem equilibrium {f : E → E} {Φ : ℝ × E → E} {U : Set (ℝ × E)} {S : Set E}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ 2 Φ U) (hS : IsOpen S)
    (hf : ContDiffOn ℝ 1 f S)
    (hzero : ∀ q, (0, q) ∈ U → Φ (0, q) = q)
    (hode : ∀ q ∈ U, Φ q ∈ S ∧ HasDerivAt (fun t => Φ (t, q.2)) (f (Φ q)) q.1)
    {x : E} (hx : x ∈ S) (hfx : f x = 0) {T : ℝ} (hT : 0 ≤ T)
    (hseg : ∀ t ∈ Icc (0 : ℝ) T, (t, x) ∈ U) :
    ∀ t ∈ Icc (0 : ℝ) T, Φ (t, x) = x := by
  let u : ℝ → E := fun t => Φ (t, x)
  have hdu : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt u (f (u t)) t :=
    fun t ht => (hode _ (hseg t ht)).2
  have heq := unique_Icc (u := u) (v := fun _ => x)
    (fun time htime => ((hΦ _ (hseg time htime)).contDiffAt
      (hU.mem_nhds (hseg time htime))).continuousAt.comp_continuousWithinAt
        (f := fun time : ℝ => (time, x))
        (continuousWithinAt_id.prodMk continuousWithinAt_const)) continuousOn_const
    (fun z hz => by
      have hzs : z ∈ S := by
        rcases hz with ⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩
        · exact (hode _ (hseg t ht)).1
        · exact hx
      exact (hf z hzs).contDiffAt (hS.mem_nhds hzs))
    (fun t ht => (hdu t ht).hasDerivWithinAt)
    (fun t ht => by simpa only [hfx] using (hasDerivWithinAt_const t (Icc (0 : ℝ) T) x))
    (hzero x (hseg 0 ⟨le_rfl, hT⟩))
  exact fun t ht => heq ht

theorem initial_variation {Φ : ℝ × E → E} {U : Set (ℝ × E)}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ 1 Φ U)
    (hzero : ∀ q, (0, q) ∈ U → Φ (0, q) = q) {x w : E} (hx : (0, x) ∈ U) :
    fderiv ℝ Φ (0, x) (0, w) = w := by
  have hdΦ := ((hΦ _ hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hd := hdΦ.hasFDerivAt.comp x
    ((hasFDerivAt_const (0 : ℝ) x).prodMk (hasFDerivAt_id x))
  have heq : (fun y => Φ (0, y)) =ᶠ[𝓝 x] id := by
    have hmem : ∀ᶠ y in 𝓝 x, (0, y) ∈ U :=
      (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hU.mem_nhds hx)
    filter_upwards [hmem] with y hy
    exact hzero y hy
  have huniq := hd.unique ((hasFDerivAt_id x).congr_of_eventuallyEq heq)
  have hh := congrArg (fun L : E →L[ℝ] E => L w) huniq
  simpa using hh

theorem nilpotent_variation {f : E → E} {Φ : ℝ × E → E} {U : Set (ℝ × E)}
    (hU : IsOpen U) (hΦ : ContDiffOn ℝ 2 Φ U)
    (hzero : ∀ q, (0, q) ∈ U → Φ (0, q) = q)
    (hode : ∀ q ∈ U, HasDerivAt (fun t => Φ (t, q.2)) (f (Φ q)) q.1)
    {x : E} {A : E →L[ℝ] E} (hf : HasFDerivAt f A x)
    (hA : ∀ w, A (A w) = 0) {T : ℝ} (hT : 0 ≤ T)
    (hseg : ∀ t ∈ Icc (0 : ℝ) T, (t, x) ∈ U)
    (heq : ∀ t ∈ Icc (0 : ℝ) T, Φ (t, x) = x) (w : E) :
    ∀ t ∈ Icc (0 : ℝ) T, fderiv ℝ Φ (t, x) (0, w) = w + t • A w := by
  let J : ℝ → E := fun t => fderiv ℝ Φ (t, x) (0, w)
  let K : ℝ → E := fun t => w + t • A w
  have hdJ : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt J (A (J t)) t := by
    intro t ht
    have hdiff : DifferentiableAt ℝ f (Φ (t, x)) := by rw [heq t ht]; exact hf.differentiableAt
    have hd := VariationCalculus.variation_hasDerivAt hU hΦ hode (hseg t ht) hdiff (w := w)
    simpa only [heq t ht, hf.fderiv] using hd
  have hdK : ∀ t : ℝ, HasDerivAt K (A (K t)) t := by
    intro t
    simpa [K, hA] using ((hasDerivAt_id t).smul_const (A w)).const_add w
  have he := unique_Icc (u := J) (v := K)
    (fun t ht => (hdJ t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hdK t).continuousAt.continuousWithinAt)
    (fun _ _ => A.contDiff.contDiffAt)
    (fun t ht => (hdJ t ht).hasDerivWithinAt)
    (fun t ht => (hdK t).hasDerivWithinAt) (by
      simpa [J, K] using initial_variation hU (hΦ.of_le (by norm_num)) hzero (hseg 0 ⟨le_rfl, hT⟩) (w := w))
  exact fun t ht => he ht

end
end FlowLinearization

end

end WeakMTWGlobalSupport

end OAI
