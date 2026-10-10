import OAI.Analysis.CircleDomains.Uniformization.LimitConformality
import OAI.Analysis.CircleDomains.Uniformization.ConformalInverse

namespace OAI

/-!
# The normalized limit as a sphere conformal equivalence

The source includes infinity. The inverse on the image is constructed
by the local inverse theorem, so the limiting map satisfies the same
two-sided conformal predicate as the final circle-domain target.
-/

open Set Filter Function Asymptotics Bornology
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem isOpen_finite_domain_with_infty
    {D : Set ℂ} (hD : IsOpen D) {R : ℝ}
    (hext : {z : ℂ | R ≤ ‖z‖} ⊆ D) :
    IsOpen (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}) := by
  have hc : IsCompact Dᶜ := by
    apply (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset hD.isClosed_compl
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hn
    exact hz (hext (le_of_lt (lt_of_not_ge hn)))
  apply (OnePoint.isOpen_iff_of_mem' (by simp)).mpr
  simpa only [preimage_union, OnePoint.coe_injective.preimage_image,
    OnePoint.coe_preimage_infty, union_empty] using And.intro hc hD

theorem injOn_extendAtInfinity
    {D : Set ℂ} {F : ℂ → ℂ} (hF : InjOn F D) :
    InjOn (extendAtInfinity F) (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}) := by
  rintro p (⟨z, hz, rfl⟩ | hp) q (⟨w, hw, rfl⟩ | hq) he
  · exact congrArg ((↑) : ℂ → Sphere) (hF hz hw (OnePoint.coe_injective he))
  · rw [mem_singleton_iff] at hq
    subst q
    exact (OnePoint.coe_ne_infty (F z) he).elim
  · rw [mem_singleton_iff] at hp
    subst p
    exact (OnePoint.coe_ne_infty (F w) he.symm).elim
  · rw [mem_singleton_iff] at hp hq
    exact hp.trans hq.symm

theorem normalized_limit_conformal_equivalence
    {D : Set ℂ} {F : ℂ → ℂ} (hD : IsOpen D)
    (hF : DifferentiableOn ℂ F D) (hFi : InjOn F D)
    (hd : ∀ z ∈ D, deriv F z ≠ 0)
    (hnorm : (fun z => F z - z) =O[cobounded ℂ] (fun z => z⁻¹))
    {R : ℝ} (hext : {z : ℂ | R ≤ ‖z‖} ⊆ D) :
    IsConformalEquivalence (extendAtInfinity F)
      (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty})
      (extendAtInfinity F '' (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty})) :=
  isConformalEquivalence_of_injOn (isConformalOn_extendAtInfinity hD hF hd hnorm)
    (isOpen_finite_domain_with_infty hD hext) (injOn_extendAtInfinity hFi)

theorem exists_conformal_limit_of_sphere_models
    (harea : ExteriorCoefficientAreaTheorem)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit)
    (hzero : HurwitzZeroFreeLimit)
    (f fi : ℕ → Sphere → Sphere) (Q V : ℕ → Set Sphere)
    (heq : ∀ n, IsSmoothSphereEquivalence (f n) (fi n) (Q n) (V n))
    (hV : ∀ n, IsOpen (V n))
    {D : ℕ → Set ℂ} (hD : ∀ n, IsOpen (D n))
    (hconn : ∀ n, IsConnected (D n)) (hmono : Monotone D)
    (hDQ : ∀ n z, z ∈ D n → (z : Sphere) ∈ Q n)
    (hcore : ∀ n, IsConformalOn (f n) (((↑) : ℂ → Sphere) '' D n))
    {R : ℝ} (hR : 0 < R)
    (hsource : ∀ n, ((((↑) : ℂ → Sphere) '' Metric.ball 0 R)ᶜ) ⊆ Q n)
    (hconf : ∀ n, IsConformalOn (f n)
      ((((↑) : ℂ → Sphere) '' Metric.closedBall 0 R)ᶜ))
    (hnorm : ∀ n, IsPrincipalNormalized (f n))
    (hext : {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D 0) :
    ∃ (s : ℕ → ℕ) (F : ℂ → ℂ), StrictMono s ∧
      TendstoLocallyUniformlyOn (fun n (z : ℂ) => finiteCoord (f (s n) (z : Sphere))) F
        atTop (⋃ n, D n) ∧
      IsPrincipalNormalized (extendAtInfinity F) ∧
      IsConformalEquivalence (extendAtInfinity F)
        (((↑) : ℂ → Sphere) '' (⋃ n, D n) ∪ {OnePoint.infty})
        (extendAtInfinity F '' (((↑) : ℂ → Sphere) '' (⋃ n, D n) ∪ {OnePoint.infty})) := by
  obtain ⟨s, F, hs, hlim, hF, hFi, hFnorm, hdecay⟩ :=
    exists_normalized_limit_of_sphere_models harea hmontel hhurwitz f fi Q V heq hV
      hD hconn hmono hDQ hcore hR hsource hconf hnorm hext
  have hinf (n : ℕ) : OnePoint.infty ∈ Q n := hsource n (by simp)
  have hdiff (n : ℕ) :
      DifferentiableOn ℂ (fun z : ℂ => finiteCoord (f n (z : Sphere))) (D n) :=
    finite_part_differentiableOn (heq n) (hinf n) (hnorm n).1 (hD n) (hDQ n) (hcore n)
  have hnonzero (n : ℕ) (z : ℂ) (hz : z ∈ D n) :
      deriv (fun w : ℂ => finiteCoord (f n (w : Sphere))) z ≠ 0 :=
    finite_part_deriv_ne_zero (hcore n _ (mem_image_of_mem _ hz))
      ((heq n).finite_forward (hinf n) (hnorm n).1 (hDQ n z hz))
  have hnonconst (n : ℕ) : ¬ ∃ c : ℂ, ∀ z ∈ D n, F z = c :=
    not_constant_of_exterior_decay hR (hext.trans (hmono (Nat.zero_le n))) hdecay
  have hd := deriv_ne_zero_on_exhaustion hzero hD hconn hmono hdiff hnonzero hs hlim hnonconst
  refine ⟨s, F, hs, hlim, isPrincipalNormalized_extendAtInfinity hFnorm, ?_⟩
  exact normalized_limit_conformal_equivalence (isOpen_iUnion hD) hF hFi hd hFnorm
    (hext.trans (subset_iUnion D 0))

end CircleDomainRigidity

end

end OAI
