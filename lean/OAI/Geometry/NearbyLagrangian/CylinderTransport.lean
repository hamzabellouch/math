import Mathlib
import OAI.Geometry.NearbyLagrangian.CylinderEquations
import OAI.Geometry.NearbyLagrangian.SupportedEvolution

namespace OAI

/-! Symplectic cylinder charts and transport of their central images. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.RadialExtension
open Set Filter Function TopologicalSpace Transport
open scoped Manifold ContDiff Topology NNReal
variable {V A M F G : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace A] {I : ModelWithCorners ℝ V A}
  [TopologicalSpace M] [ChartedSpace A M]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

theorem exists_cylinderEvolution (U : Opens (F × F)) (W : Opens (G × G))
    (e : Diffeomorph (I.prod 𝓘(ℝ,F × F)) 𝓘(ℝ,G × G) (M × U) W ∞)
    {H : ℝ → M → ℝ} {ζ ξ : F → ℝ} {C : Set M}
    (hC : IsCompact C) (hS : ∀ t ∈ Icc (0:ℝ) 1, Function.support (H t) ⊆ C)
    (hH : ContMDiffOn (𝓘(ℝ,ℝ).prod I) 𝓘(ℝ,ℝ) ∞
      (fun z : ℝ × M => H z.1 z.2) (Icc (0:ℝ) 1 ×ˢ univ))
    (hζ : ContDiff ℝ ∞ ζ) (hξ : ContDiff ℝ ∞ ξ)
    (hζc : HasCompactSupport ζ) (hξc : HasCompactSupport ξ)
    (hU : tsupport ζ ×ˢ tsupport ξ ⊆ (U:Set (F × F))) :
    Nonempty (SupportedHamiltonianEvolution W (cylinderHamiltonian U W e H ζ ξ)) := by
  obtain ⟨hd,hc,C,hC,hCW,hCs⟩ := cylinderHamiltonian_regular U W e hC hS hH hζ hξ hζc hξc hU
  exact exists_supportedHamiltonianEvolution W hd hc hC hCW hCs

end NearbyLagrangian.RadialExtension

namespace NearbyLagrangian.RadialExtension
open Set Filter Function TopologicalSpace Transport SmoothFlow
open scoped Manifold ContDiff Topology NNReal
variable {V A M R E : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace A] {I : ModelWithCorners ℝ V A}
  [TopologicalSpace M] [ChartedSpace A M]
  [NormedAddCommGroup R] [InnerProductSpace ℝ R] [CompleteSpace R]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def IsSymplecticCylinderChart (U : Opens (R × R)) (W : Opens (E × E))
    (e : Diffeomorph (I.prod 𝓘(ℝ,R × R)) 𝓘(ℝ,E × E) (M × U) W ∞)
    (form : M → V → V → ℝ) : Prop :=
  ∀ z u v,
    inner ℝ (mfderiv (I.prod 𝓘(ℝ,R × R)) 𝓘(ℝ,E × E) e z u).2
      (mfderiv (I.prod 𝓘(ℝ,R × R)) 𝓘(ℝ,E × E) e z v).1 -
    inner ℝ (mfderiv (I.prod 𝓘(ℝ,R × R)) 𝓘(ℝ,E × E) e z v).2
      (mfderiv (I.prod 𝓘(ℝ,R × R)) 𝓘(ℝ,E × E) e z u).1 =
      form z.1 u.1 v.1 + inner ℝ u.2.2 v.2.1 - inner ℝ v.2.2 u.2.1

theorem supported_motion_radial (U : Opens (R × R)) (W : Opens (E × E))
    (e : Diffeomorph (I.prod 𝓘(ℝ,R × R)) 𝓘(ℝ,E × E) (M × U) W ∞)
    (form : M → V → V → ℝ) (hω : ∀ x u, form x u 0 = 0)
    (he : IsSymplecticCylinderChart U W e form)
    {H : ℝ → M → ℝ} {ζ ξ : R → ℝ} {K : ℝ × (E × E) → ℝ}
    (F : SupportedHamiltonianEvolution W K)
    (hKH : ∀ t ∈ Icc (0:ℝ) 1, ∀ x : W,
      K (t,(x:E × E)) = (cutoffHamiltonian (H t) ζ ξ ∘ radialInclusion U) (e.symm x))
    (hH : ∀ t ∈ Icc (0:ℝ) 1, MDifferentiable I 𝓘(ℝ,ℝ) (H t))
    (hζd : Differentiable ℝ ζ) (hξd : Differentiable ℝ ξ)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hbound : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, |H t x| ≤ B)
    (hζ : ∀ a, ‖gradient ζ a‖ ≤ C)
    (hξ : ∀ w, ξ w ∈ Icc (0:ℝ) 1)
    (hplateau : ∀ w, ‖w‖ ≤ B*C+1 → ξ w = 1)
    (q : M) {a : R} (ha : (a,0) ∈ U) :
    ∀ t ∈ Icc (0:ℝ) 1,
      ‖((F.motion e 0 t (q,⟨(a,0),ha⟩)).2:R × R).2‖ ≤ B*C ∧
      ξ ((F.motion e 0 t (q,⟨(a,0),ha⟩)).2:R × R).2 = 1 ∧
      gradient ξ ((F.motion e 0 t (q,⟨(a,0),ha⟩)).2:R × R).2 = 0 ∧
      ((F.motion e 0 t (q,⟨(a,0),ha⟩)).2:R × R).1 = a := by
  let x : M × U := (q,⟨(a,0),ha⟩)
  have hK (t : ℝ) : Differentiable ℝ (fun x => K (t,x)) :=
    (F.smooth.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hc (t : ℝ) : MDifferentiableWithinAt 𝓘(ℝ,ℝ) (I.prod 𝓘(ℝ,R × R))
      (fun u => F.motion e 0 u x) (Icc (0:ℝ) 1) t :=
    ((F.motion_curve_smooth e 0 x).mdifferentiableAt (by simp)).mdifferentiableWithinAt
  have h := ambient_hamiltonian_radial_trapping U W e form hω he hKH
    (fun t _ => hK t) (fun t _ => hc t) (fun t ht => hH t ht _) hζd hξd
    (fun t ht v => F.motion_equation e 0 x ht v) hB hC
    (fun t ht => hbound t ht _) hζ hξ hplateau (by rw [F.motion_initial])
  simpa only [F.motion_initial] using h

omit [CompleteSpace R] in

theorem supported_motion_central (U : Opens (R × R)) (W : Opens (E × E))
    (e : Diffeomorph (I.prod 𝓘(ℝ,R × R)) 𝓘(ℝ,E × E) (M × U) W ∞)
    (form : M → V → V → ℝ) (he : IsSymplecticCylinderChart U W e form)
    {H : ℝ → M → ℝ} {ζ ξ : R → ℝ} {K : ℝ × (E × E) → ℝ}
    (F : SupportedHamiltonianEvolution W K)
    (hKH : ∀ t ∈ Icc (0:ℝ) 1, ∀ x : W,
      K (t,(x:E × E)) = (cutoffHamiltonian (H t) ζ ξ ∘ radialInclusion U) (e.symm x))
    {b : ℝ → M} {a : R} (ha : (a,0) ∈ U)
    (hζ : ζ =ᶠ[𝓝 a] fun _ => (1:ℝ)) (hξ : ξ =ᶠ[𝓝 (0:R)] fun _ => (1:ℝ))
    (hb : ∀ t ∈ Icc (0:ℝ) 1, MDifferentiableWithinAt 𝓘(ℝ,ℝ) I b (Icc (0:ℝ) 1) t)
    (hH : ∀ t ∈ Icc (0:ℝ) 1, MDifferentiableAt I 𝓘(ℝ,ℝ) (H t) (b t))
    (hbH : ∀ t ∈ Icc (0:ℝ) 1, ∀ v,
      form (b t) (mfderivWithin 𝓘(ℝ,ℝ) I b (Icc (0:ℝ) 1) t 1) v =
        -mfderiv I 𝓘(ℝ,ℝ) (H t) (b t) v) :
    ∀ t ∈ Icc (0:ℝ) 1, F.motion e 0 t (b 0,⟨(a,0),ha⟩) = (b t,⟨(a,0),ha⟩) := by
  let x : M × U := (b 0,⟨(a,0),ha⟩)
  have hK (t : ℝ) : Differentiable ℝ (fun x => K (t,x)) :=
    (F.smooth.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hc (t : ℝ) : MDifferentiableWithinAt 𝓘(ℝ,ℝ) (I.prod 𝓘(ℝ,R × R))
      (fun u => F.motion e 0 u x) (Icc (0:ℝ) 1) t :=
    ((F.motion_curve_smooth e 0 x).mdifferentiableAt (by simp)).mdifferentiableWithinAt
  exact central_radial_curve_unique U W e form he ha hζ hξ hKH
    (fun t _ => hK t) (field_lipschitz_spatial F.lipschitz) hb hH hbH
    (fun t _ => hc t) (fun t ht v => F.motion_equation e 0 x ht v)
    (F.motion_initial e 0 x)

end NearbyLagrangian.RadialExtension

namespace NearbyLagrangian.Transport
open Set Function
variable {M R P : Type*} [Zero P]

theorem central_open_cylinder_image {U : Set (R × P)} {L N : Set M} {C : Set R}
    {f : M × U → M × U} {g : M → M}
    (hrad : ∀ q ∈ L, ∀ u : U, (u:R × P).2 = 0 →
      ((f (q,u)).2:R × P).1 = (u:R × P).1)
    (hcentral : ∀ q ∈ L, ∀ u : U, (u:R × P).2 = 0 → (u:R × P).1 ∈ C →
      f (q,u) = (g q,u))
    (himage : g '' L = N) :
    f '' {z : M × U | z.1 ∈ L ∧ (z.2:R × P).2 = 0} ∩
        {z | (z.2:R × P).1 ∈ C} =
      {z | z.1 ∈ N ∧ (z.2:R × P).1 ∈ C ∧ (z.2:R × P).2 = 0} := by
  ext z
  constructor
  · rintro ⟨⟨⟨q,u⟩,⟨hq,hu⟩,rfl⟩,hz⟩
    have ha : (u:R × P).1 ∈ C := (hrad q hq u hu) ▸ hz
    rw [hcentral q hq u hu ha]
    exact ⟨himage ▸ mem_image_of_mem g hq,ha,hu⟩
  · rintro ⟨hz,hc,hp⟩
    obtain ⟨q,hq,heq⟩ := himage.symm ▸ hz
    refine ⟨⟨(q,z.2),⟨hq,hp⟩,?_⟩,hc⟩
    rw [hcentral q hq z.2 hp hc,heq]

theorem central_open_cylinder_image_chart {A : Type*} {U : Set (R × P)}
    (e : M × U → A) (he : Injective e) {L N : Set M} {C : Set R}
    {f : M × U → M × U} {g : M → M}
    (hrad : ∀ q ∈ L, ∀ u : U, (u:R × P).2 = 0 →
      ((f (q,u)).2:R × P).1 = (u:R × P).1)
    (hcentral : ∀ q ∈ L, ∀ u : U, (u:R × P).2 = 0 → (u:R × P).1 ∈ C →
      f (q,u) = (g q,u))
    (himage : g '' L = N) :
    (e ∘ f) '' {z : M × U | z.1 ∈ L ∧ (z.2:R × P).2 = 0} ∩
        e '' {z | (z.2:R × P).1 ∈ C} =
      e '' {z | z.1 ∈ N ∧ (z.2:R × P).1 ∈ C ∧ (z.2:R × P).2 = 0} := by
  rw [Set.image_comp,← Set.image_inter he]
  rw [central_open_cylinder_image hrad hcentral himage]

end NearbyLagrangian.Transport

namespace NearbyLagrangian.RadialExtension
open Set Filter Function TopologicalSpace Transport SmoothFlow
open scoped Manifold ContDiff Topology NNReal
variable {V A M R E : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace A] {I : ModelWithCorners ℝ V A}
  [TopologicalSpace M] [ChartedSpace A M]
  [NormedAddCommGroup R] [InnerProductSpace ℝ R] [CompleteSpace R]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem supported_motion_cylinder_image (U : Opens (R × R)) (W : Opens (E × E))
    (e : Diffeomorph (I.prod 𝓘(ℝ,R × R)) 𝓘(ℝ,E × E) (M × U) W ∞)
    (form : M → V → V → ℝ) (hω : ∀ x u, form x u 0 = 0)
    (he : IsSymplecticCylinderChart U W e form)
    {H : ℝ → M → ℝ} {ζ ξ : R → ℝ} {K : ℝ × (E × E) → ℝ}
    (F : SupportedHamiltonianEvolution W K)
    (hKH : ∀ t ∈ Icc (0:ℝ) 1, ∀ x : W,
      K (t,(x:E × E)) = (cutoffHamiltonian (H t) ζ ξ ∘ radialInclusion U) (e.symm x))
    (hH : ∀ t ∈ Icc (0:ℝ) 1, MDifferentiable I 𝓘(ℝ,ℝ) (H t))
    (hζd : Differentiable ℝ ζ) (hξd : Differentiable ℝ ξ)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hbound : ∀ t ∈ Icc (0:ℝ) 1, ∀ x, |H t x| ≤ B)
    (hζ : ∀ a, ‖gradient ζ a‖ ≤ C)
    (hξ : ∀ w, ξ w ∈ Icc (0:ℝ) 1)
    (hplateau : ∀ w, ‖w‖ ≤ B*C+1 → ξ w = 1)
    {central : Set R} (hcentral : ∀ a ∈ central, ζ =ᶠ[𝓝 a] fun _ => (1:ℝ))
    (ψ : ℝ → M → M) (hψ0 : ∀ q, ψ 0 q = q)
    (hψd : ∀ q, ∀ t ∈ Icc (0:ℝ) 1,
      MDifferentiableWithinAt 𝓘(ℝ,ℝ) I (fun u => ψ u q) (Icc (0:ℝ) 1) t)
    (hψH : ∀ q, ∀ t ∈ Icc (0:ℝ) 1, ∀ v,
      form (ψ t q) (mfderivWithin 𝓘(ℝ,ℝ) I (fun u => ψ u q) (Icc (0:ℝ) 1) t 1) v =
        -mfderiv I 𝓘(ℝ,ℝ) (H t) (ψ t q) v)
    {L N : Set M} (himage : ψ 1 '' L = N) :
    (fun z : M × U => evolution F.flow ((0,(e z:E × E)),1)) ''
        {z | z.1 ∈ L ∧ (z.2:R × R).2 = 0} ∩
      (fun z : M × U => (e z:E × E)) '' {z | (z.2:R × R).1 ∈ central} =
      (fun z : M × U => (e z:E × E)) ''
        {z | z.1 ∈ N ∧ (z.2:R × R).1 ∈ central ∧ (z.2:R × R).2 = 0} := by
  have h01 : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨zero_le_one,le_rfl⟩
  have hξ0 : ξ =ᶠ[𝓝 (0:R)] fun _ => (1:ℝ) := by
    have hpos : 0 < B*C+1 := by positivity
    filter_upwards [Metric.ball_mem_nhds (0:R) hpos] with w hw
    apply hplateau
    exact le_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using hw)
  have hrad (q : M) (_hq : q ∈ L) (u : U) (hu : (u:R × R).2 = 0) :
      ((F.motion e 0 1 (q,u)).2:R × R).1 = (u:R × R).1 := by
    have hu' : u = ⟨((u:R × R).1,0),by simpa only [← hu,Prod.mk.eta] using u.property⟩ := by
      apply Subtype.ext
      exact Prod.ext rfl hu
    rw [hu']
    exact (supported_motion_radial U W e form hω he F hKH hH hζd hξd hB hC
      hbound hζ hξ hplateau q _ 1 h01).2.2.2
  have hc (q : M) (_hq : q ∈ L) (u : U) (hu : (u:R × R).2 = 0)
      (ha : (u:R × R).1 ∈ central) : F.motion e 0 1 (q,u) = (ψ 1 q,u) := by
    have hu' : u = ⟨((u:R × R).1,0),by simpa only [← hu,Prod.mk.eta] using u.property⟩ := by
      apply Subtype.ext
      exact Prod.ext rfl hu
    have hh := supported_motion_central U W e form he F hKH
      (b:=fun t => ψ t q) (a:=(u:R × R).1)
      (by simpa only [← hu,Prod.mk.eta] using u.property)
      (hcentral _ ha) hξ0 (hψd q) (fun t ht => hH t ht _) (hψH q) 1 h01
    simpa only [hψ0,← hu'] using hh
  have hm := central_open_cylinder_image_chart (fun z : M × U => (e z:E × E))
    (fun _ _ h => e.injective (Subtype.val_injective h)) hrad hc himage
  have heq : (fun z : M × U => (e (F.motion e 0 1 z):E × E)) =
      (fun z : M × U => evolution F.flow ((0,(e z:E × E)),1)) :=
    funext fun z => F.motion_identity e 0 1 z
  change (fun z : M × U => (e (F.motion e 0 1 z):E × E)) '' _ ∩ _ = _ at hm
  rw [heq] at hm
  exact hm

end NearbyLagrangian.RadialExtension

end

end OAI
