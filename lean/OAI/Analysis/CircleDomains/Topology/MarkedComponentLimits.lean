import OAI.Analysis.CircleDomains.Topology.CircleComponentCoordinates
import OAI.Analysis.CircleDomains.Modulus.NormalizedLimits

namespace OAI

/-!
# Marked complementary-component limits

The center/radius sequences are selected from actual circle-domain
components. Their Hausdorff-convergent subsequence preserves a previously
constructed locally uniform map limit.
-/

open Set Filter Function Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem exists_marked_component_limits
    {B : Type*} [Countable B] (V : ℕ → Set Sphere)
    (hV : ∀ n, IsCircleDomain (V n)) (hinf : ∀ n, OnePoint.infty ∈ V n)
    {L : ℝ} (hbound : ∀ n, (V n)ᶜ ⊆ ((↑) : ℂ → Sphere) '' closedBall 0 L)
    (p : ℕ → B → Sphere) (hp : ∀ n b, p n b ∈ (V n)ᶜ)
    {D : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hlim : TendstoLocallyUniformlyOn F f atTop D) :
    ∃ (s : ℕ → ℕ) (c₀ : B → ℂ) (r₀ : B → ℝ), StrictMono s ∧
      TendstoLocallyUniformlyOn (fun n => F (s n)) f atTop D ∧
      (∀ b, ‖c₀ b‖ ≤ L ∧ r₀ b ∈ Icc 0 L) ∧
      ∀ b, Tendsto (fun n => hausdorffDist
        (finiteCoord '' connectedComponentIn (V (s n))ᶜ (p (s n) b))
        (closedBall (c₀ b) (r₀ b))) atTop (𝓝 0) := by
  have hex : ∀ n b, ∃ (c : ℂ) (r : ℝ), ‖c‖ ≤ L ∧ r ∈ Icc 0 L ∧
      connectedComponentIn (V n)ᶜ (p n b) = ((↑) : ℂ → Sphere) '' closedBall c r := by
    intro n b
    exact bounded_circleDomain_component_parameters (hV n) (hinf n) (hbound n) (hp n b)
  choose c r hc hr he using hex
  obtain ⟨s, c₀, r₀, hs, hb, hdisks⟩ := exists_marked_disk_hausdorff_limits c r hc hr
  refine ⟨s, c₀, r₀, hs, locally_uniform_subsequence hlim hs, hb, ?_⟩
  intro b
  have hcoords (n : ℕ) : finiteCoord '' connectedComponentIn (V n)ᶜ (p n b) =
      closedBall (c n b) (r n b) := by
    rw [he n b, image_image]
    simp only [finiteCoord_coe, image_id']
  simpa only [hcoords] using hdisks b

/-- A mark need only be included eventually. Dummy radius-zero disks at
its earlier stages do not affect the simultaneous parameter limits. -/
theorem exists_eventual_marked_component_limits
    {B : Type*} [Countable B] (V : ℕ → Set Sphere)
    (hV : ∀ n, IsCircleDomain (V n)) (hinf : ∀ n, OnePoint.infty ∈ V n)
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ n, (V n)ᶜ ⊆ ((↑) : ℂ → Sphere) '' closedBall 0 L)
    (p : ℕ → B → Sphere) (hp : ∀ b, ∀ᶠ n in atTop, p n b ∈ (V n)ᶜ)
    {D : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hlim : TendstoLocallyUniformlyOn F f atTop D) :
    ∃ (s : ℕ → ℕ) (c : ℕ → B → ℂ) (r : ℕ → B → ℝ)
      (c₀ : B → ℂ) (r₀ : B → ℝ),
      StrictMono s ∧ TendstoLocallyUniformlyOn (fun n => F (s n)) f atTop D ∧
      (∀ n b, ‖c n b‖ ≤ L ∧ r n b ∈ Icc 0 L) ∧
      (∀ b, ‖c₀ b‖ ≤ L ∧ r₀ b ∈ Icc 0 L) ∧
      (∀ b, ∀ᶠ n in atTop,
        connectedComponentIn (V (s n))ᶜ (p (s n) b) =
          ((↑) : ℂ → Sphere) '' closedBall (c n b) (r n b)) ∧
      (∀ b, Tendsto (fun n => c n b) atTop (𝓝 (c₀ b))) ∧
      (∀ b, Tendsto (fun n => r n b) atTop (𝓝 (r₀ b))) := by
  classical
  have hex : ∀ n b, ∃ (c : ℂ) (r : ℝ), ‖c‖ ≤ L ∧ r ∈ Icc 0 L ∧
      (p n b ∈ (V n)ᶜ → connectedComponentIn (V n)ᶜ (p n b) =
        ((↑) : ℂ → Sphere) '' closedBall c r) := by
    intro n b
    by_cases hb : p n b ∈ (V n)ᶜ
    · obtain ⟨c, r, hc, hr, he⟩ :=
        bounded_circleDomain_component_parameters (hV n) (hinf n) (hbound n) hb
      exact ⟨c, r, hc, hr, fun _ => he⟩
    · exact ⟨0, 0, by simpa using hL, ⟨le_rfl, hL⟩, fun h => (hb h).elim⟩
  choose c r hc hr he using hex
  obtain ⟨s, c₀, r₀, hs, hb, hclim, hrlim⟩ :=
    exists_marked_disk_parameter_limits c r hc hr
  refine ⟨s, (fun n => c (s n)), (fun n => r (s n)), c₀, r₀, hs,
    locally_uniform_subsequence hlim hs, (fun n b => ⟨hc (s n) b, hr (s n) b⟩),
    hb, ?_, hclim, hrlim⟩
  intro b
  filter_upwards [hs.tendsto_atTop (hp b)] with n hn
  exact he (s n) b hn

end CircleDomainRigidity

end

end OAI
