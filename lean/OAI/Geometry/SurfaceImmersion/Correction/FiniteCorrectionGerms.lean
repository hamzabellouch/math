import OAI.Geometry.SurfaceImmersion.Geometry.NormalizedSphericalGerm
import OAI.Geometry.SurfaceImmersion.Atlas.QuadraticCutoffBounds

namespace OAI

/-! Finite disjoint corrections retain each prescribed local jet. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.SphericalJets

lemma finite_sum_germ_of_disjoint_supports {E V ι : Type*}
    [TopologicalSpace E] [AddCommMonoid V] [DecidableEq ι]
    (s : Finset ι) (q : ι → E → V) (K : ι → Set E)
    (hs : ∀ i ∈ s, tsupport (q i) ⊆ K i)
    (hdisj : (↑s : Set ι).Pairwise fun i j => Disjoint (K i) (K j))
    {i : ι} (hi : i ∈ s) {p : E} (hp : p ∈ K i) :
    (fun x => ∑ j ∈ s, q j x) =ᶠ[𝓝 p] q i := by
  have he : ∀ᶠ x in 𝓝 p, ∀ j ∈ s, j ≠ i → q j x = 0 := by
    apply (eventually_all_finset s).mpr
    intro j hj
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall fun _ hn => False.elim (hn hji)
    · have hnot : p ∉ tsupport (q j) := by
        intro hq
        exact Set.disjoint_left.mp (hdisj hj hi hji) (hs j hj hq) hp
      exact (notMem_tsupport_iff_eventuallyEq.mp hnot).mono (fun _ hx _ => hx)
  filter_upwards [he] with x hx
  exact Finset.sum_eq_single i (fun j hj hji => hx j hj hji) (by simp [hi])

lemma scaledQuadraticCutoff_jets (B : SecondTensor) (hB : ∀ v w, B v w = B w v)
    (p : Plane) {r : ℝ} (hr : 0 < r) :
    scaledQuadraticCutoff B p r p = 0 ∧
      fderiv ℝ (scaledQuadraticCutoff B p r) p = 0 ∧
      ∀ v w, fderiv ℝ (fderiv ℝ (scaledQuadraticCutoff B p r)) p v w = -B v w := by
  have he := scaledQuadraticCutoff_germ B p hr
  refine ⟨?_,?_,?_⟩
  · rw [he.eq_of_nhds]
    simp [quadraticCorrection]
  · rw [he.fderiv_eq,quadraticCorrection_fderiv B hB]
    simp
  · intro v w
    rw [he.fderiv.fderiv_eq,quadraticCorrection_second B hB]

theorem finite_quadratic_flattening_jets (P : Finset Plane) (F : Plane → Space)
    (hF : ContDiff ℝ ∞ F) (hunit : ∀ p : P, ∀ᶠ x in 𝓝 (p : Plane), ‖F x‖ = 1)
    (r : P → ℝ) (hr : ∀ p, 0 < r p)
    (hdisj : Pairwise fun p q : P => Disjoint (closedBall (p : Plane) (r p))
      (closedBall (q : Plane) (r q))) :
    let Q := fun x => ∑ p : P, scaledQuadraticCutoff (sphericalSecondFormCLM F p) p (r p) x
    let G := radialNormalize ∘ (F+Q)
    ContDiff ℝ ∞ Q ∧ ∀ p : P, G p = F p ∧ fderiv ℝ G p = fderiv ℝ F p ∧
      ∀ v w, sphericalSecondForm G p v w = 0 := by
  classical
  let q (p : P) := scaledQuadraticCutoff (sphericalSecondFormCLM F p) p (r p)
  let Q := fun x => ∑ p : P, q p x
  have hQ : ContDiff ℝ ∞ Q := ContDiff.sum fun p _ => scaledQuadraticCutoff_smooth _ _ _
  refine ⟨hQ,?_⟩
  intro p
  have he : Q =ᶠ[𝓝 (p : Plane)] q p :=
    finite_sum_germ_of_disjoint_supports Finset.univ q
      (fun p => closedBall (p : Plane) (r p))
      (fun p _ => scaledQuadraticCutoff_tsupport _ _ (hr p))
      (fun p _ q _ hpq => hdisj hpq) (Finset.mem_univ p)
      (mem_closedBall_self (hr p).le)
  obtain ⟨hq0,hq1,hq2⟩ := scaledQuadraticCutoff_jets (sphericalSecondFormCLM F p)
    (fun v w => sphericalSecondForm_symmetric hF p v w) p (hr p)
  apply normalized_spherical_flattening hF hQ (hunit p)
  · exact he.eq_of_nhds.trans hq0
  · exact he.fderiv_eq.trans hq1
  · intro v w
    exact congrArg (fun L : Plane →L[ℝ] Plane →L[ℝ] Space => L v w)
      he.fderiv.fderiv_eq |>.trans (hq2 v w)

end ClosedSurfaceR4.SphericalJets

end

end OAI
