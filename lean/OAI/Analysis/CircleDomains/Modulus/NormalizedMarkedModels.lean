import OAI.Analysis.CircleDomains.Modulus.NormalizedLimitEquivalence
import OAI.Analysis.CircleDomains.Uniformization.OmittedLimits

namespace OAI

/-!
# Normalized limits with actual marked complementary disks

The marked components may only appear eventually in the finite models.
A common subsequence yields their round Hausdorff limits and a two-sided
conformal sphere limit. Hurwitz puts every limiting disk in the complement
of that image. Assignment to a particular end is a separate geometric step.
-/

open Set Filter Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem not_constant_on_open_of_conformal_extension
    {D : Set ℂ} {F : ℂ → ℂ} (hD : IsOpen D) (hne : D.Nonempty)
    (hconf : IsConformalOn (extendAtInfinity F) (((↑) : ℂ → Sphere) '' D)) :
    ¬ ∃ c : ℂ, ∀ z ∈ D, F z = c := by
  rintro ⟨c, hc⟩
  obtain ⟨z, hz⟩ := hne
  have hd := finite_part_deriv_ne_zero (hconf _ (mem_image_of_mem _ hz))
    (OnePoint.coe_ne_infty (F z))
  have he : F =ᶠ[𝓝 z] (fun _ => c) := by
    filter_upwards [hD.mem_nhds hz] with w hw
    exact hc w hw
  apply hd
  simpa only [extendAtInfinity_coe, finiteCoord_coe, deriv_const] using he.deriv_eq

theorem exists_normalized_marked_sphere_limit_with_parameters
    (harea : ExteriorCoefficientAreaTheorem)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit)
    (hzero : HurwitzZeroFreeLimit)
    (f fi : ℕ → Sphere → Sphere) (Q V : ℕ → Set Sphere)
    (heq : ∀ n, IsSmoothSphereEquivalence (f n) (fi n) (Q n) (V n))
    (hV : ∀ n, IsCircleDomain (V n))
    {D : ℕ → Set ℂ} (hD : ∀ n, IsOpen (D n))
    (hconn : ∀ n, IsConnected (D n)) (hmono : Monotone D)
    (hDQ : ∀ n z, z ∈ D n → (z : Sphere) ∈ Q n)
    (hcore : ∀ n, IsConformalOn (f n) (((↑) : ℂ → Sphere) '' D n))
    {R : ℝ} (hR : 0 < R)
    (hsource : ∀ n, ((((↑) : ℂ → Sphere) '' ball 0 R)ᶜ) ⊆ Q n)
    (hconf : ∀ n, IsConformalOn (f n)
      ((((↑) : ℂ → Sphere) '' closedBall 0 R)ᶜ))
    (hnorm : ∀ n, IsPrincipalNormalized (f n))
    (hext : {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D 0)
    {B : Type*} [Countable B] (p : ℕ → B → Sphere)
    (hp : ∀ b, ∀ᶠ n in atTop, p n b ∈ (V n)ᶜ) :
    ∃ (s : ℕ → ℕ) (F : ℂ → ℂ) (c : B → ℂ) (r : B → ℝ),
      StrictMono s ∧
      TendstoLocallyUniformlyOn (fun n (z : ℂ) => finiteCoord (f (s n) (z : Sphere))) F
        atTop (⋃ n, D n) ∧
      IsPrincipalNormalized (extendAtInfinity F) ∧
      IsConformalEquivalence (extendAtInfinity F)
        (((↑) : ℂ → Sphere) '' (⋃ n, D n) ∪ {OnePoint.infty})
        (extendAtInfinity F '' (((↑) : ℂ → Sphere) '' (⋃ n, D n) ∪ {OnePoint.infty})) ∧
      (∀ b, ‖c b‖ ≤ 3 * R ∧ r b ∈ Icc 0 (3 * R)) ∧
      (∀ b, Tendsto (fun n => hausdorffDist
        (finiteCoord '' connectedComponentIn (V (s n))ᶜ (p (s n) b))
        (closedBall (c b) (r b))) atTop (𝓝 0)) ∧
      (∀ b, ((↑) : ℂ → Sphere) '' closedBall (c b) (r b) ⊆
        (extendAtInfinity F '' (((↑) : ℂ → Sphere) '' (⋃ n, D n) ∪ {OnePoint.infty}))ᶜ) ∧
      ∃ (cn : ℕ → B → ℂ) (rn : ℕ → B → ℝ),
        (∀ n b, ‖cn n b‖ ≤ 3 * R ∧ rn n b ∈ Icc 0 (3 * R)) ∧
        (∀ b, ∀ᶠ n in atTop,
          connectedComponentIn (V (s n))ᶜ (p (s n) b) =
            ((↑) : ℂ → Sphere) '' closedBall (cn n b) (rn n b)) ∧
        (∀ b, Tendsto (fun n => cn n b) atTop (𝓝 (c b))) ∧
        (∀ b, Tendsto (fun n => rn n b) atTop (𝓝 (r b))) := by
  have hinfQ (n : ℕ) : OnePoint.infty ∈ Q n := hsource n (by simp)
  have hinfV (n : ℕ) : OnePoint.infty ∈ V n := by
    simpa only [(hnorm n).1] using (heq n).mapsTo (hinfQ n)
  have hbound (n : ℕ) : (V n)ᶜ ⊆ ((↑) : ℂ → Sphere) '' closedBall 0 (3 * R) :=
    (normalized_model_uniform_bound harea (heq n) (hV n).1 hR
      (hsource n) (hconf n) (hnorm n)).1
  obtain ⟨s, F, hs, hlim, hFnorm, hFeq⟩ :=
    exists_conformal_limit_of_sphere_models harea hmontel hhurwitz hzero f fi Q V heq
      (fun n => (hV n).1) hD hconn hmono hDQ hcore hR hsource hconf hnorm hext
  obtain ⟨t, c, r, c₀, r₀, ht, hlim', hb, hb₀, he, hc, hr⟩ :=
    exists_eventual_marked_component_limits (fun n => V (s n)) (fun n => hV (s n))
      (fun n => hinfV (s n)) (by positivity : 0 ≤ 3 * R) (fun n => hbound (s n))
      (fun n b => p (s n) b) (fun b => hs.tendsto_atTop (hp b)) hlim
  have hnonconst (m : ℕ) : ¬ ∃ a : ℂ, ∀ z ∈ D m, F z = a :=
    not_constant_on_open_of_conformal_extension (hD m) (hconn m).nonempty
      (hFeq.1.mono ((image_mono (subset_iUnion D m)).trans subset_union_left))
  have hmaps (m : ℕ) : ∀ᶠ n in atTop,
      DifferentiableOn ℂ (fun z : ℂ => finiteCoord (f (s (t n)) (z : Sphere))) (D m) ∧
      ∀ z ∈ D m, (finiteCoord (f (s (t n)) (z : Sphere)) : Sphere) ∈ V (s (t n)) := by
    filter_upwards [(hs.comp ht).tendsto_atTop.eventually_ge_atTop m] with n hn
    refine ⟨(finite_part_differentiableOn (heq (s (t n))) (hinfQ (s (t n)))
      (hnorm (s (t n))).1 (hD (s (t n))) (hDQ (s (t n)))
      (hcore (s (t n)))).mono (hmono hn), ?_⟩
    intro z hz
    have hzQ := hDQ (s (t n)) z (hmono hn hz)
    rw [coe_finiteCoord ((heq (s (t n))).finite_forward
      (hinfQ (s (t n))) (hnorm (s (t n))).1 hzQ)]
    exact (heq (s (t n))).mapsTo hzQ
  refine ⟨s ∘ t, F, c₀, r₀, hs.comp ht, hlim', hFnorm, hFeq, hb₀, ?_, ?_, c, r, hb, he, hc, hr⟩
  · intro b
    have hball := tendsto_hausdorffDist_closedBall (fun n => (hb n b).2.1)
      (hb₀ b).2.1 (hc b) (hr b)
    apply hball.congr'
    filter_upwards [he b] with n hn
    simp only [Function.comp_apply, hn, image_image, finiteCoord_coe, image_id']
  · intro b
    exact marked_component_limit_omitted hzero hD hconn hmaps (he b)
      (fun n => (hb n b).2.1) (hb₀ b).2.1 hlim' (hc b) (hr b) hnonconst

theorem exists_normalized_marked_sphere_limit
    (harea : ExteriorCoefficientAreaTheorem)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit)
    (hzero : HurwitzZeroFreeLimit)
    (f fi : ℕ → Sphere → Sphere) (Q V : ℕ → Set Sphere)
    (heq : ∀ n, IsSmoothSphereEquivalence (f n) (fi n) (Q n) (V n))
    (hV : ∀ n, IsCircleDomain (V n))
    {D : ℕ → Set ℂ} (hD : ∀ n, IsOpen (D n))
    (hconn : ∀ n, IsConnected (D n)) (hmono : Monotone D)
    (hDQ : ∀ n z, z ∈ D n → (z : Sphere) ∈ Q n)
    (hcore : ∀ n, IsConformalOn (f n) (((↑) : ℂ → Sphere) '' D n))
    {R : ℝ} (hR : 0 < R)
    (hsource : ∀ n, ((((↑) : ℂ → Sphere) '' ball 0 R)ᶜ) ⊆ Q n)
    (hconf : ∀ n, IsConformalOn (f n)
      ((((↑) : ℂ → Sphere) '' closedBall 0 R)ᶜ))
    (hnorm : ∀ n, IsPrincipalNormalized (f n))
    (hext : {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D 0)
    {B : Type*} [Countable B] (p : ℕ → B → Sphere)
    (hp : ∀ b, ∀ᶠ n in atTop, p n b ∈ (V n)ᶜ) :
    ∃ (s : ℕ → ℕ) (F : ℂ → ℂ) (c : B → ℂ) (r : B → ℝ),
      StrictMono s ∧
      TendstoLocallyUniformlyOn (fun n (z : ℂ) => finiteCoord (f (s n) (z : Sphere))) F
        atTop (⋃ n, D n) ∧
      IsPrincipalNormalized (extendAtInfinity F) ∧
      IsConformalEquivalence (extendAtInfinity F)
        (((↑) : ℂ → Sphere) '' (⋃ n, D n) ∪ {OnePoint.infty})
        (extendAtInfinity F '' (((↑) : ℂ → Sphere) '' (⋃ n, D n) ∪ {OnePoint.infty})) ∧
      (∀ b, ‖c b‖ ≤ 3 * R ∧ r b ∈ Icc 0 (3 * R)) ∧
      (∀ b, Tendsto (fun n => hausdorffDist
        (finiteCoord '' connectedComponentIn (V (s n))ᶜ (p (s n) b))
        (closedBall (c b) (r b))) atTop (𝓝 0)) ∧
      ∀ b, ((↑) : ℂ → Sphere) '' closedBall (c b) (r b) ⊆
        (extendAtInfinity F '' (((↑) : ℂ → Sphere) '' (⋃ n, D n) ∪ {OnePoint.infty}))ᶜ := by
  obtain ⟨s, F, c, r, hs, hl, hn, he, hb, hh, ho, _⟩ :=
    exists_normalized_marked_sphere_limit_with_parameters harea hmontel hhurwitz hzero
      f fi Q V heq hV hD hconn hmono hDQ hcore hR hsource hconf hnorm hext p hp
  exact ⟨s, F, c, r, hs, hl, hn, he, hb, hh, ho⟩

end CircleDomainRigidity

end

end OAI
