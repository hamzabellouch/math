import OAI.Analysis.CircleDomains.Uniformization.LimitConformality
import OAI.Analysis.CircleDomains.Topology.MarkedComponentLimits

namespace OAI

/-!
# Limits of omitted points and disks

Hurwitz applied to `Fₙ - wₙ` keeps every convergent sequence of omitted
points out of a nonconstant locally uniform limit's image. The argument
works on each retained core. Convergence of disk parameters then keeps
the whole limiting closed disk in the complement.
-/

open Set Filter Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem omitted_point_limit
    (hhurwitz : HurwitzZeroFreeLimit)
    {D : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {w : ℕ → ℂ} {w₀ : ℂ}
    (hD : IsOpen D) (hconn : IsConnected D)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) D ∧ ∀ z ∈ D, F n z ≠ w n)
    (hlim : TendstoLocallyUniformlyOn F f atTop D)
    (hw : Tendsto w atTop (𝓝 w₀))
    (hnonconst : ¬ ∃ c : ℂ, ∀ z ∈ D, f z = c) :
    ∀ z ∈ D, f z ≠ w₀ := by
  have hconst : TendstoLocallyUniformlyOn (fun n (_ : ℂ) => w n)
      (fun _ => w₀) atTop D := (hw.tendstoUniformlyOn_const D).tendstoLocallyUniformlyOn
  have hsub : TendstoLocallyUniformlyOn (fun n z => F n z - w n)
      (fun z => f z - w₀) atTop D := by
    exact uniformContinuous_sub.comp_tendstoLocallyUniformlyOn (hlim.prodMk hconst)
  have hsubF : ∀ᶠ n in atTop,
      DifferentiableOn ℂ (fun z => F n z - w n) D ∧ ∀ z ∈ D, F n z - w n ≠ 0 := by
    filter_upwards [hF] with n hn
    exact ⟨hn.1.sub_const _, fun z hz => sub_ne_zero.mpr (hn.2 z hz)⟩
  rcases hhurwitz D (fun n z => F n z - w n) (fun z => f z - w₀)
      hD hconn hsubF hsub with hz | hn
  · exact (hnonconst ⟨w₀, fun z hzD => sub_eq_zero.mp (hz z hzD)⟩).elim
  · exact fun z hz => sub_ne_zero.mp (hn z hz)

/-- The disks may depend on the index, and need be omitted only eventually
on a fixed connected open source set. -/
theorem omitted_closedBall_limit
    (hhurwitz : HurwitzZeroFreeLimit)
    {D : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    {c : ℕ → ℂ} {r : ℕ → ℝ} {c₀ : ℂ} {r₀ : ℝ}
    (hD : IsOpen D) (hconn : IsConnected D)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) D ∧
      ∀ z ∈ D, F n z ∉ Metric.closedBall (c n) (r n))
    (hr : ∀ n, 0 ≤ r n) (hr₀ : 0 ≤ r₀)
    (hlim : TendstoLocallyUniformlyOn F f atTop D)
    (hc : Tendsto c atTop (𝓝 c₀)) (hrlim : Tendsto r atTop (𝓝 r₀))
    (hnonconst : ¬ ∃ a : ℂ, ∀ z ∈ D, f z = a) :
    Metric.closedBall c₀ r₀ ⊆ (f '' D)ᶜ := by
  intro w hw
  rw [closedBall_eq_affine_image hr₀ c₀] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  let v : ℕ → ℂ := fun n => c n + r n • u
  have hv (n : ℕ) : v n ∈ Metric.closedBall (c n) (r n) := by
    rw [closedBall_eq_affine_image (hr n) (c n)]
    exact mem_image_of_mem _ hu
  have hvlim : Tendsto v atTop (𝓝 (c₀ + r₀ • u)) :=
    hc.add (hrlim.smul tendsto_const_nhds)
  have hzero : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) D ∧
      ∀ z ∈ D, F n z ≠ v n := by
    filter_upwards [hF] with n hn
    exact ⟨hn.1, fun z hz he => hn.2 z hz (he ▸ hv n)⟩
  rintro ⟨z, hz, he⟩
  exact omitted_point_limit hhurwitz hD hconn hzero hlim hvlim hnonconst z hz he

/-- Eventual holomorphy and omission on each retained core suffice;
no single finite map has to be defined on the full union. -/
theorem omitted_closedBall_limit_on_eventual_cores
    (hhurwitz : HurwitzZeroFreeLimit)
    {D : ℕ → Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    {c : ℕ → ℂ} {r : ℕ → ℝ} {c₀ : ℂ} {r₀ : ℝ}
    (hD : ∀ m, IsOpen (D m)) (hconn : ∀ m, IsConnected (D m))
    (hF : ∀ m, ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) (D m) ∧
      ∀ z ∈ D m, F n z ∉ Metric.closedBall (c n) (r n))
    (hr : ∀ n, 0 ≤ r n) (hr₀ : 0 ≤ r₀)
    (hlim : TendstoLocallyUniformlyOn F f atTop (⋃ m, D m))
    (hc : Tendsto c atTop (𝓝 c₀)) (hrlim : Tendsto r atTop (𝓝 r₀))
    (hnonconst : ∀ m, ¬ ∃ a : ℂ, ∀ z ∈ D m, f z = a) :
    Metric.closedBall c₀ r₀ ⊆ (f '' (⋃ m, D m))ᶜ := by
  rintro w hw ⟨z, hz, he⟩
  obtain ⟨m, hm⟩ := mem_iUnion.mp hz
  exact omitted_closedBall_limit hhurwitz (hD m) (hconn m) (hF m) hr hr₀
    (hlim.mono (subset_iUnion D m)) hc hrlim (hnonconst m) hw ⟨z, hm, he⟩

theorem omitted_point_limit_on_exhaustion
    (hhurwitz : HurwitzZeroFreeLimit)
    {D : ℕ → Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {w : ℕ → ℂ} {w₀ : ℂ}
    (hD : ∀ n, IsOpen (D n)) (hconn : ∀ n, IsConnected (D n)) (hmono : Monotone D)
    (hF : ∀ n, DifferentiableOn ℂ (F n) (D n))
    (hmiss : ∀ n z, z ∈ D n → F n z ≠ w n)
    (hlim : TendstoLocallyUniformlyOn F f atTop (⋃ n, D n))
    (hw : Tendsto w atTop (𝓝 w₀))
    (hnonconst : ∀ n, ¬ ∃ c : ℂ, ∀ z ∈ D n, f z = c) :
    w₀ ∉ f '' (⋃ n, D n) := by
  rintro ⟨z, hz, heq⟩
  obtain ⟨m, hm⟩ := mem_iUnion.mp hz
  have he := omitted_point_limit hhurwitz (hD m) (hconn m) ?_
    (hlim.mono (subset_iUnion D m)) hw (hnonconst m) z hm
  · exact he heq
  · filter_upwards [eventually_ge_atTop m] with n hn
    exact ⟨(hF n).mono (hmono hn), fun x hx => hmiss n x (hmono hn hx)⟩

theorem omitted_closedBall_limit_on_exhaustion
    (hhurwitz : HurwitzZeroFreeLimit)
    {D : ℕ → Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    {c : ℕ → ℂ} {r : ℕ → ℝ} {c₀ : ℂ} {r₀ : ℝ}
    (hD : ∀ n, IsOpen (D n)) (hconn : ∀ n, IsConnected (D n)) (hmono : Monotone D)
    (hF : ∀ n, DifferentiableOn ℂ (F n) (D n))
    (hr : ∀ n, 0 ≤ r n) (hr₀ : 0 ≤ r₀)
    (hmiss : ∀ n z, z ∈ D n → F n z ∉ Metric.closedBall (c n) (r n))
    (hlim : TendstoLocallyUniformlyOn F f atTop (⋃ n, D n))
    (hc : Tendsto c atTop (𝓝 c₀)) (hrlim : Tendsto r atTop (𝓝 r₀))
    (hnonconst : ∀ n, ¬ ∃ a : ℂ, ∀ z ∈ D n, f z = a) :
    Metric.closedBall c₀ r₀ ⊆ (f '' (⋃ n, D n))ᶜ := by
  intro w hw
  rw [closedBall_eq_affine_image hr₀ c₀] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  let v : ℕ → ℂ := fun n => c n + r n • u
  have hv (n : ℕ) : v n ∈ Metric.closedBall (c n) (r n) := by
    rw [closedBall_eq_affine_image (hr n) (c n)]
    exact mem_image_of_mem _ hu
  have hvlim : Tendsto v atTop (𝓝 (c₀ + r₀ • u)) :=
    hc.add (hrlim.smul tendsto_const_nhds)
  apply omitted_point_limit_on_exhaustion hhurwitz hD hconn hmono hF ?_ hlim hvlim hnonconst
  intro n z hz heq
  exact hmiss n z hz (heq ▸ hv n)

/-- Passing to the normalized sphere extension introduces only infinity,
so a finite omitted disk remains omitted. -/
theorem sphere_disk_omitted_of_plane_disk
    {D : Set ℂ} {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (h : Metric.closedBall c r ⊆ (f '' D)ᶜ) :
    ((↑) : ℂ → Sphere) '' Metric.closedBall c r ⊆
      (extendAtInfinity f '' (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}))ᶜ := by
  rintro _ ⟨w, hw, rfl⟩ ⟨p, hp, he⟩
  rcases hp with ⟨z, hz, rfl⟩ | hp
  · exact h hw ⟨z, hz, OnePoint.coe_injective he⟩
  · rw [mem_singleton_iff] at hp
    subst p
    exact OnePoint.coe_ne_infty w he.symm

/-- Actual complementary components of the approximating circle domains
remain omitted in the normalized limiting sphere image. -/
theorem marked_component_limit_omitted
    (hhurwitz : HurwitzZeroFreeLimit)
    {D : ℕ → Set ℂ} {V : ℕ → Set Sphere} {p : ℕ → Sphere}
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    {c : ℕ → ℂ} {r : ℕ → ℝ} {c₀ : ℂ} {r₀ : ℝ}
    (hD : ∀ m, IsOpen (D m)) (hconn : ∀ m, IsConnected (D m))
    (hF : ∀ m, ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) (D m) ∧
      ∀ z ∈ D m, (F n z : Sphere) ∈ V n)
    (he : ∀ᶠ n in atTop, connectedComponentIn (V n)ᶜ (p n) =
      ((↑) : ℂ → Sphere) '' Metric.closedBall (c n) (r n))
    (hr : ∀ n, 0 ≤ r n) (hr₀ : 0 ≤ r₀)
    (hlim : TendstoLocallyUniformlyOn F f atTop (⋃ m, D m))
    (hc : Tendsto c atTop (𝓝 c₀)) (hrlim : Tendsto r atTop (𝓝 r₀))
    (hnonconst : ∀ m, ¬ ∃ a : ℂ, ∀ z ∈ D m, f z = a) :
    ((↑) : ℂ → Sphere) '' Metric.closedBall c₀ r₀ ⊆
      (extendAtInfinity f '' (((↑) : ℂ → Sphere) '' (⋃ m, D m) ∪ {OnePoint.infty}))ᶜ := by
  apply sphere_disk_omitted_of_plane_disk
  apply omitted_closedBall_limit_on_eventual_cores hhurwitz hD hconn ?_
    hr hr₀ hlim hc hrlim hnonconst
  intro m
  filter_upwards [hF m, he] with n hn hen
  refine ⟨hn.1, ?_⟩
  intro z hz hball
  have hcomp : (F n z : Sphere) ∈ connectedComponentIn (V n)ᶜ (p n) := by
    rw [hen]
    exact mem_image_of_mem _ hball
  exact connectedComponentIn_subset (V n)ᶜ (p n) hcomp (hn.2 z hz)

end CircleDomainRigidity

end

end OAI
