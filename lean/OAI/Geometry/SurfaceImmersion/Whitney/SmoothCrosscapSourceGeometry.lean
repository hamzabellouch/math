import OAI.Geometry.SurfaceImmersion.Whitney.SmoothCrosscapSourceArc
import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapSourceEndpoint

namespace OAI

/-! The smooth embedded source connection retains both actual kernel
axes near its singular endpoints, in the original crosscap coordinates. -/
noncomputable section
open Set Filter Manifold unitInterval
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]
variable {f : M → ProjectionTarget 3} {p q : M}

theorem smooth_crosscap_source_geometry
    (hf : ContMDiff planeModel 𝓘(ℝ,ProjectionTarget 3) ∞ f)
    (hreg : ∀ x y, x ≠ y → f x = f y → Function.Surjective (surfacePairDerivative f x y))
    (cp : SurfaceCrosscapCoordinates f p) (cq : SurfaceCrosscapCoordinates f q)
    (hp : ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f p))
    (hq : ¬ Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f q))
    {Γ : I → M × M} (hΓ : Continuous Γ) (hi : Function.Injective Γ)
    (hzero : Γ 0 = (p,p)) (hone : Γ 1 = (q,q))
    (heq : ∀ u, f (Γ u).1 = f (Γ u).2)
    (hgood : ∀ u : I, 0 < (u:ℝ) → (u:ℝ) < 1 → (Γ u).1 ≠ (Γ u).2 ∧
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (Γ u).1) ∧
      Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (Γ u).2))
    (hsingp : ∀ x, f x = f p → x = p) (hsingq : ∀ x, f x = f q → x = q) :
    ∃ (P : SmoothCompactArc planeModel M) (V W : Set M),
      IsOpen V ∧ p ∈ V ∧ IsOpen W ∧ q ∈ W ∧
      P.curve P.start = p ∧ P.curve P.finish = q ∧
      (∀ t ∈ Ioo P.start P.finish,
        Function.Injective (mfderiv planeModel 𝓘(ℝ,ProjectionTarget 3) f (P.curve t))) ∧
      (∀ t ∈ Icc P.start P.finish, P.curve t ∈ V →
        P.curve t ∈ cp.source.source ∧ cp.source (P.curve t) 0 = 0) ∧
      (∀ t ∈ Icc P.start P.finish, P.curve t ∈ W →
        P.curve t ∈ cq.source.source ∧ cq.source (P.curve t) 0 = 0) := by
  obtain ⟨P,K,hK,hKO,hPs,hPf,hPi,hPr⟩ := smooth_crosscap_source_arc hf hreg cp cq
    hΓ hi hzero hone heq hgood hsingp
  have hne := fun u h0 h1 => (hgood u h0 h1).1
  obtain ⟨V,hV,hpV,hVp⟩ := crosscap_source_endpoint_neighborhood cp hΓ hi hzero hone
    heq hne hsingp hK (fun hk => hp (hKO hk))
  let Δ := Γ ∘ unitInterval.symm
  have hΔ : Continuous Δ := hΓ.comp continuous_symm
  have hΔi : Function.Injective Δ := hi.comp symm_bijective.injective
  have hΔ0 : Δ 0 = (q,q) := by simpa [Δ] using hone
  have hΔ1 : Δ 1 = (p,p) := by simpa [Δ] using hzero
  have hΔe : ∀ u, f (Δ u).1 = f (Δ u).2 := fun u => heq (unitInterval.symm u)
  have hΔn : ∀ u : I, 0 < (u:ℝ) → (u:ℝ) < 1 → (Δ u).1 ≠ (Δ u).2 := by
    intro u h0 h1
    apply hne
    · change 0 < 1-(u:ℝ); linarith
    · change 1-(u:ℝ) < 1; linarith
  have hrange : range Δ = range Γ := by
    ext z
    constructor
    · rintro ⟨u,rfl⟩
      exact ⟨unitInterval.symm u,rfl⟩
    · rintro ⟨u,rfl⟩
      refine ⟨unitInterval.symm u,?_⟩
      simp [Δ]
  obtain ⟨W,hW,hqW,hWq⟩ := crosscap_source_endpoint_neighborhood cq hΔ hΔi hΔ0 hΔ1
    hΔe hΔn hsingq hK (fun hk => hq (hKO hk))
  refine ⟨P,V,W,hV,hpV,hW,hqW,hPs,hPf,hPr,?_,?_⟩
  · intro t ht htv
    exact hVp _ htv (hPi ⟨t,ht,rfl⟩)
  · intro t ht htw
    apply hWq _ htw
    rw [hrange]
    exact hPi ⟨t,ht,rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
