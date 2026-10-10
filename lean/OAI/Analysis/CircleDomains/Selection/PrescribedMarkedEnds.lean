import OAI.Analysis.CircleDomains.Selection.FiniteMarkedTrapping
import OAI.Analysis.CircleDomains.Modulus.NormalizedMarkedModels
import OAI.Analysis.CircleDomains.Selection.TerminalContainment

namespace OAI

/-!
# Marked disk limits lie in their prescribed complementary components

Local uniform convergence on the source gives uniform convergence on each
retained circle. The finite terminal assignment and the nested target end
description then place the entire limiting round disk in the prescribed
component, including a zero-radius limit.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem marked_limit_subset_corresponding_component
    {I : ℕ → Type*} (T : (n : ℕ) → I n → ℂ ≃ₜ ℂ)
    (f fi : ℕ → Sphere → Sphere) (V : ℕ → Set Sphere)
    (ha : ∀ n, TerminalComponentAssignment (T n) (f n) (V n))
    (heq : ∀ n, IsSmoothSphereEquivalence (f n) (fi n) (openCompletedRegion (T n)) (V n))
    (hfix : ∀ n, f n OnePoint.infty = OnePoint.infty)
    {G : Set Sphere} (C : ℕ → SmoothJordanCore G)
    (b : (j : ℕ) → Fin (C j).count) (H : ℕ → ℂ ≃ₜ ℂ)
    (hret : ∀ j, ∀ᶠ n in atTop, (C j).carrier ⊆ openCompletedRegion (T n))
    (t : (n : ℕ) → I n)
    {q : Sphere} (hq : ∀ j, q ∈ ((↑) : ℂ → Sphere) '' jordanInterior ((C j).disk (b j)))
    (hmark : ∀ᶠ n in atTop, q ∈ closedTerminalCap (T n (t n)))
    (F : ℂ → ℂ) (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G))
    (hlim : TendstoLocallyUniformlyOn (fun n (z : ℂ) => finiteCoord (f n (z : Sphere)))
      F atTop (((↑) : ℂ → Sphere) ⁻¹' G))
    (hboundary : ∀ j, extendAtInfinity F ''
      (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C j).disk (b j)))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior (H j)))
    {p : Sphere}
    (hcomponent : connectedComponentIn (extendAtInfinity F '' G)ᶜ p =
      ⋂ j, closedTerminalCap (H j))
    {c : ℕ → ℂ} {r : ℕ → ℝ} {c₀ : ℂ} {r₀ : ℝ}
    (hr : ∀ n, 0 ≤ r n) (hr₀ : 0 ≤ r₀)
    (hc : Tendsto c atTop (𝓝 c₀)) (hrlim : Tendsto r atTop (𝓝 r₀))
    (hdisks : ∀ᶠ n in atTop,
      connectedComponentIn (V n)ᶜ ((ha n).point (t n)) =
        ((↑) : ℂ → Sphere) '' closedBall (c n) (r n)) :
    ((↑) : ℂ → Sphere) '' closedBall c₀ r₀ ⊆
      connectedComponentIn (extendAtInfinity F '' G)ᶜ p := by
  have hphysical (j : ℕ) : ∀ᶠ n in atTop, closedTerminalCap (T n (t n)) ⊆
      ((↑) : ℂ → Sphere) '' jordanInterior ((C j).disk (b j)) := by
    filter_upwards [hret j, hmark] with n hn hqn
    exact terminal_subset_retained_side (T n) (C j) hn hqn (hq j)
  have hcurveG (j : ℕ) (s : Circle) : ((C j).curve (b j) s : Sphere) ∈ G := by
    apply (C j).boundary_subset_domain (b j)
    refine ⟨(C j).curve (b j) s, ?_, rfl⟩
    rw [(C j).boundary (b j)]
    exact mem_range_self s
  have hcontain (j : ℕ) : closedBall c₀ r₀ ⊆ closure (jordanInterior (H j)) := by
    have hγ : Continuous ((C j).curve (b j)) := ((C j).embedding (b j)).continuous
    have hFγ : Continuous (F ∘ (C j).curve (b j)) :=
      hF.comp_continuous hγ (hcurveG j)
    have hγlim : TendstoUniformly
        (fun n s => finiteCoord (f n (((C j).curve (b j) s : ℂ) : Sphere)))
        (F ∘ (C j).curve (b j)) atTop := by
      apply tendstoUniformlyOn_univ.mp
      apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_univ).mp
      exact hlim.comp ((C j).curve (b j)) (fun s _ => hcurveG j s) hγ.continuousOn
    have hfront : range (F ∘ (C j).curve (b j)) = frontier (jordanInterior (H j)) := by
      simpa only [extendAtInfinity_coe, finiteCoord_coe, Function.comp_def] using
        range_finite_image_boundary ((C j).boundary (b j)) (hboundary j)
          (fun s => by simp only [extendAtInfinity_coe]; exact OnePoint.coe_ne_infty _)
    exact marked_limit_subset_retained_fill T f fi V ha heq hfix (C j) (b j)
      (hret j) t (hphysical j) F (H j) hFγ hfront hγlim hr hr₀ hc hrlim hdisks
  rw [hcomponent]
  rintro _ ⟨z, hz, rfl⟩
  exact mem_iInter.mpr fun j => ⟨z, hcontain j hz, rfl⟩

end CircleDomainRigidity

end

end OAI
