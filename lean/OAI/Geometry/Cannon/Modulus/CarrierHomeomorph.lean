import Mathlib
import OAI.Geometry.Cannon.Modulus.Ambient
import OAI.Geometry.Cannon.Conformal.Round

namespace OAI

section
section
section
noncomputable section
namespace CannonRoundRadial
open Set Metric Topology

theorem carrier_homeomorph {X Y Z ι : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z]
    (A : ι → Set X) (K : ι → Set Y)
    (hc : ∀ S : Set Y,IsPreconnected S →
      IsPreconnected (⋃ (i : {i : ι // (S∩K i).Nonempty}),A i.val))
    (N : Y ≃ₜ Z) (S : Set Z) (hS : IsPreconnected S) :
    IsPreconnected (⋃ (i : {i : ι // (S∩N '' K i).Nonempty}),A i.val) := by
  have he (i : ι) : (S∩N '' K i).Nonempty ↔ (N ⁻¹' S∩K i).Nonempty := by
    constructor
    · rintro ⟨_,hs,⟨x,hx,rfl⟩⟩
      exact ⟨x,hs,hx⟩
    · rintro ⟨x,hx,hk⟩
      exact ⟨N x,hx,⟨x,hk,rfl⟩⟩
  have hpre : IsPreconnected (N ⁻¹' S) := by
    rw [←Homeomorph.image_symm]
    exact hS.image N.symm N.symm.continuous.continuousOn
  have hu : (⋃ (i : {i : ι // (S∩N '' K i).Nonempty}),A i.val)=
      (⋃ (i : {i : ι // (N ⁻¹' S∩K i).Nonempty}),A i.val) := by
    ext x
    simp only [mem_iUnion,Subtype.exists]
    constructor <;> rintro ⟨i,hi,hx⟩
    · exact ⟨i,(he i).mp hi,hx⟩
    · exact ⟨i,(he i).mpr hi,hx⟩
  rw [hu]
  exact hc _ hpre

theorem round_realization {X ι : Type*} [PseudoMetricSpace X]
    (A : ι → Set X) (K : ι → Set (OnePoint ℂ))
    (f : C(X,OnePoint ℂ)) (hfs : Function.Surjective f)
    (hpre : ∀ S : Set (OnePoint ℂ),f ⁻¹' S⊆
      ⋃ (i : {i : ι // (S∩K i).Nonempty}),A i.val)
    (hc : ∀ S : Set (OnePoint ℂ),IsPreconnected S →
      IsPreconnected (⋃ (i : {i : ι // (S∩K i).Nonempty}),A i.val))
    (eps : ℝ) (hfib : ∀ x y,f x=f y → dist x y≤eps)
    (N : OnePoint ℂ≃ₜOnePoint ℂ) :
    ∃ g : C(X,Round),Function.Surjective g ∧
      (∀ x,g x=CannonMobius.roundChart (N (f x))) ∧
      (∀ x y,g x=g y → dist x y≤eps) ∧
      (∀ S : Set Round,g ⁻¹' S⊆
        ⋃ (i : {i : ι // (S∩(N.trans CannonMobius.roundChart) '' K i).Nonempty}),A i.val) ∧
      (∀ p : Round,∀ t : ℝ,IsPreconnected
        (⋃ (i : {i : ι // (sphere p t∩(N.trans CannonMobius.roundChart) '' K i).Nonempty}),A i.val)) := by
  let E : OnePoint ℂ≃ₜRound:=N.trans CannonMobius.roundChart
  let g : C(X,Round):=⟨E ∘ f,E.continuous.comp f.continuous⟩
  refine ⟨g,E.surjective.comp hfs,fun x=>rfl,?_,?_,?_⟩
  · intro x y hxy
    exact hfib x y (E.injective hxy)
  · intro S x hx
    have hx' : f x∈E ⁻¹' S:=hx
    obtain ⟨i,hi⟩:=mem_iUnion.mp (hpre (E ⁻¹' S) (show x∈f ⁻¹' (E ⁻¹' S) from hx'))
    obtain ⟨q,hq,hqK⟩:=i.property
    exact mem_iUnion.mpr ⟨⟨i.val,⟨E q,hq,⟨q,hqK,rfl⟩⟩⟩,hi⟩
  · intro p t
    exact carrier_homeomorph A K hc E _ (metric_sphere_preconnected p t)
end CannonRoundRadial

end
end
section
noncomputable section
namespace CannonRelease
open Set Metric Topology unitInterval CannonGraph CannonCarrierCharging CannonUniformization
open scoped OnePoint

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_annular_metric_carriers (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ L c : ℝ,1≤L ∧ 0<c ∧ c≤1 ∧ ∀ {Y κ : Type*},∀ [PseudoMetricSpace Y],
      ∀ A : κ → Set (Boundary D),∀ K : κ → Set (Y),
      ∀ f : C(Boundary D,Y),
      (∀ S : Set (Y),f ⁻¹' S⊆
        ⋃(d : {d : κ // (S∩K d).Nonempty}),A d.val) →
      ∀ (o a₀ b₀ z₀ : Boundary D) (r R : ℝ),0<r → 0<R →
        dist o a₀≤r → R≤dist o b₀ → R≤dist o z₀ →
      ∀ (p : Y) (a b : ℝ),
        dist (f o) p≤a →
        b≤dist (f a₀) p →
        dist (f b₀) p≤a →
        b≤dist (f z₀) p →
      ∀ t∈Icc a b,
        ∃ x∈⋃(d : {d : κ // (sphere p t∩K d).Nonempty}),A d.val,
        ∃ y∈⋃(d : {d : κ // (sphere p t∩K d).Nonempty}),A d.val,
          ∀ γ : Path x y,range γ∈annulusFamily o (L*r) (c*R) := by
  let _ := visualMetricSpace D hδ
  dsimp only
  obtain ⟨L,hL,hinner⟩:=boundary_controlled_paths D hδ φ
  obtain ⟨c,hc,hc1,houter⟩:=boundary_outside_paths D hδ φ
  refine ⟨L,c,hL,hc,hc1,?_⟩
  intro Y κ _ A K f hpre o a₀ b₀ z₀ r R hr hR ha₀ hb₀ hz₀ p a b ho ha hb hz
  have hi:=hinner o o a₀ r hr (by change dist o o≤r; simpa using hr.le) ha₀
  have ho':=houter o b₀ z₀ R hR hb₀ hz₀
  let γ : Path o a₀:=hi.somePath
  let η : Path b₀ z₀:=ho'.somePath
  have hγ : IsPreconnected (range γ) := isPreconnected_range γ.continuous
  have hη : IsPreconnected (range η) := isPreconnected_range η.continuous
  have hhγ : range γ⊆closedBall o (L*r) := by
    rintro x ⟨t,rfl⟩
    have hh:=hi.somePath_mem t
    change dist o (γ t)<L*r at hh
    exact (dist_comm (γ t) o).le.trans hh.le
  have hhη : range η⊆(ball o (c*R))ᶜ := by
    rintro x ⟨t,rfl⟩ hx
    have hh:=ho'.somePath_mem t
    change c*R<dist o (η t) at hh
    have hx':=mem_ball.mp hx
    rw [dist_comm] at hx'
    exact (not_lt_of_ge hh.le) hx'
  exact radial_continua_carrier_crossing f A K hpre (range γ) (range η) hγ hη
    o (L*r) (c*R) hhγ hhη p a b
    ⟨o,⟨0,γ.source⟩,a₀,⟨1,γ.target⟩,ho,ha⟩
    ⟨b₀,⟨0,η.source⟩,z₀,⟨1,η.target⟩,hb,hz⟩
end CannonRelease

end
end
end
end

end OAI
