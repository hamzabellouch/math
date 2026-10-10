import OAI.Analysis.CircleDomains.Uniformization.FiniteModelEnds
import OAI.Analysis.CircleDomains.Selection.MarkedEndTrapping

namespace OAI

/-!
# Marked-disk trapping for the actual finite terminal assignment

The assignment is constructed from a finite model. Once a fixed source
core is retained, a terminal inside one of its holes has its target disk
inside the corresponding image contour. Uniform convergence on that
contour passes this containment to the limiting closed disk.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

structure TerminalComponentAssignment {I : Type*} (T : I → ℂ ≃ₜ ℂ)
    (f : Sphere → Sphere) (V : Set Sphere) where
  point : I → Sphere
  outside : ∀ i, point i ∈ Vᶜ
  disjoint : Pairwise (Disjoint on fun i => connectedComponentIn Vᶜ (point i))
  covers : ∀ y ∈ Vᶜ, ∃ i, connectedComponentIn Vᶜ y = connectedComponentIn Vᶜ (point i)
  cluster : ∀ i q, q ∈ closedTerminalCap (T i) → ∀ x : ℕ → Sphere,
    Tendsto x atTop (𝓝 q) → (∀ᶠ n in atTop, x n ∈ openCompletedRegion T) →
    ∀ y, Tendsto (f ∘ x) atTop (𝓝 y) → y ∈ connectedComponentIn Vᶜ (point i)
  retained : ∀ A : SmoothJordanCore (openCompletedRegion T),
    ∃ L : Fin A.count → ℂ ≃ₜ ℂ,
      (∀ j, f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (A.disk j))) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior (L j))) ∧
      ∀ i j, closedTerminalCap (T i) ⊆ ((↑) : ℂ → Sphere) '' jordanInterior (A.disk j) →
        connectedComponentIn Vᶜ (point i) ⊆ ((↑) : ℂ → Sphere) '' jordanInterior (L j)

theorem exists_terminal_component_assignment
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {I : Type*} [Finite I] (T : I → ℂ ≃ₜ ℂ)
    (hTd : Pairwise (Disjoint on fun i => closure (jordanInterior (T i))))
    {f fi : Sphere → Sphere} {V : Set Sphere}
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (hV : IsOpen V) (hfix : f OnePoint.infty = OnePoint.infty) :
    Nonempty (TerminalComponentAssignment T f V) := by
  obtain ⟨p, hp, hd, hc, hcl, hr⟩ := exists_finite_model_terminal_assignment
    hsard hschoenflies T hTd hf hV hfix
  exact ⟨⟨p, hp, hd, hc, hcl, hr⟩⟩

def SmoothJordanCore.inDomain {G Q : Set Sphere} (A : SmoothJordanCore G)
    (h : A.carrier ⊆ Q) : SmoothJordanCore Q where
  count := A.count
  disk := A.disk
  curve := A.curve
  disjoint := A.disjoint
  subset_domain := h
  smooth := A.smooth
  embedding := A.embedding
  boundary := A.boundary

theorem range_finite_image_boundary
    {f : Sphere → Sphere} {γ : Circle → ℂ} {H L : ℂ ≃ₜ ℂ}
    (hγ : frontier (jordanInterior H) = range γ)
    (hb : f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior L))
    (hfinite : ∀ t, f ((γ t : ℂ) : Sphere) ≠ OnePoint.infty) :
    range (fun t => finiteCoord (f ((γ t : ℂ) : Sphere))) = frontier (jordanInterior L) := by
  apply OnePoint.coe_injective.image_injective
  rw [← hb, hγ, image_image, ← range_comp, ← range_comp]
  congr 1
  funext t
  exact coe_finiteCoord (hfinite t)

theorem marked_limit_subset_retained_fill
    {I : ℕ → Type*} (T : (n : ℕ) → I n → ℂ ≃ₜ ℂ)
    (f fi : ℕ → Sphere → Sphere) (V : ℕ → Set Sphere)
    (ha : ∀ n, TerminalComponentAssignment (T n) (f n) (V n))
    (heq : ∀ n, IsSmoothSphereEquivalence (f n) (fi n) (openCompletedRegion (T n)) (V n))
    (hfix : ∀ n, f n OnePoint.infty = OnePoint.infty)
    {G : Set Sphere} (A : SmoothJordanCore G) (j : Fin A.count)
    (hret : ∀ᶠ n in atTop, A.carrier ⊆ openCompletedRegion (T n))
    (t : (n : ℕ) → I n)
    (hphysical : ∀ᶠ n in atTop, closedTerminalCap (T n (t n)) ⊆
      ((↑) : ℂ → Sphere) '' jordanInterior (A.disk j))
    (F : ℂ → ℂ) (H : ℂ ≃ₜ ℂ)
    (hF : Continuous (F ∘ A.curve j))
    (hH : range (F ∘ A.curve j) = frontier (jordanInterior H))
    (hlim : TendstoUniformly (fun n s => finiteCoord (f n ((A.curve j s : ℂ) : Sphere)))
      (F ∘ A.curve j) atTop)
    {c : ℕ → ℂ} {r : ℕ → ℝ} {c₀ : ℂ} {r₀ : ℝ}
    (hr : ∀ n, 0 ≤ r n) (hr₀ : 0 ≤ r₀)
    (hc : Tendsto c atTop (𝓝 c₀)) (hrlim : Tendsto r atTop (𝓝 r₀))
    (hdisks : ∀ᶠ n in atTop,
      connectedComponentIn (V n)ᶜ ((ha n).point (t n)) =
        ((↑) : ℂ → Sphere) '' closedBall (c n) (r n)) :
    closedBall c₀ r₀ ⊆ closure (jordanInterior H) := by
  classical
  have hex (n : ℕ) : ∃ L : Fin A.count → ℂ ≃ₜ ℂ,
      A.carrier ⊆ openCompletedRegion (T n) →
        (∀ k, f n '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (A.disk k))) =
          ((↑) : ℂ → Sphere) '' frontier (jordanInterior (L k))) ∧
        ∀ i k, closedTerminalCap (T n i) ⊆
          ((↑) : ℂ → Sphere) '' jordanInterior (A.disk k) →
          connectedComponentIn (V n)ᶜ ((ha n).point i) ⊆
            ((↑) : ℂ → Sphere) '' jordanInterior (L k) := by
    by_cases hn : A.carrier ⊆ openCompletedRegion (T n)
    · obtain ⟨L, hL⟩ := (ha n).retained (A.inDomain hn)
      exact ⟨L, fun _ => hL⟩
    · exact ⟨fun _ => H, fun h => (hn h).elim⟩
  choose L hL using hex
  have hfront : ∀ᶠ n in atTop,
      range (fun s => finiteCoord (f n ((A.curve j s : ℂ) : Sphere))) =
        frontier (jordanInterior (L n j)) := by
    filter_upwards [hret] with n hn
    apply range_finite_image_boundary (A.boundary j) ((hL n hn).1 j)
    intro s
    apply finite_image_of_fixes_infty (heq n).bijOn.injOn
      ((A.inDomain hn).subset (interior_subset A.infty_interior)) (hfix n)
    apply (A.inDomain hn).boundary_subset_domain j
    refine ⟨A.curve j s, ?_, rfl⟩
    dsimp only [SmoothJordanCore.inDomain]
    rw [A.boundary j]
    exact mem_range_self s
  have htrap : ∀ᶠ n in atTop, closedBall (c n) (r n) ⊆ closure (jordanInterior (L n j)) := by
    filter_upwards [hret, hphysical, hdisks] with n hn hpn hdn
    intro z hz
    have hzcomp : (z : Sphere) ∈ connectedComponentIn (V n)ᶜ ((ha n).point (t n)) := by
      rw [hdn]
      exact mem_image_of_mem _ hz
    have hzside := (hL n hn).2 (t n) j hpn hzcomp
    exact subset_closure (OnePoint.coe_injective.mem_set_image.mp hzside)
  exact limit_disk_subset_jordan_fill H (fun n => L n j) _ _ hF hH hfront hlim
    hr hr₀ hc hrlim htrap

end CircleDomainRigidity

end

end OAI
