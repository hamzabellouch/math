import Mathlib
import OAI.Geometry.Cannon.Modulus.TracePreconnected
import OAI.Geometry.Cannon.Topology.ThreeSeparation

namespace OAI

section
noncomputable section
namespace CannonCarrierCharging
open Set Metric Topology CannonMobius CannonUniformization CannonRadialWitness
open scoped OnePoint

lemma preimage_carrier_postcompose {X Y Z κ : Type*}
    (A : κ → Set X) (K : κ → Set Y) (f : X → Y) (N : Y → Z)
    (hpre : ∀ S : Set Y,f ⁻¹' S ⊆ ⋃(d : {d : κ // (S∩K d).Nonempty}),A d.val) :
    ∀ S : Set Z,(N ∘ f) ⁻¹' S ⊆ ⋃(d : {d : κ // (S∩N '' K d).Nonempty}),A d.val := by
  intro S x hx
  obtain ⟨d,hd⟩:=mem_iUnion.mp (hpre (N ⁻¹' S) hx)
  obtain ⟨y,hy,hyk⟩:=d.property
  exact mem_iUnion.mpr ⟨⟨d.val,⟨N y,hy,⟨y,hyk,rfl⟩⟩⟩,hd⟩

theorem relative_radial_carrier_witness :
    ∃ C : ℝ,1 ≤ C ∧ ∀ {X κ : Type*},∀ [MetricSpace X],
    ∀ (L σ : ℝ),
      (∀ o u v : X,∀ s : ℝ,0<s → dist o u ≤ s → dist o v ≤ s →
        JoinedIn (closedBall o (L*s)) u v) →
      (∀ o u v : X,∀ s : ℝ,0<s → s ≤ dist o u → s ≤ dist o v →
        JoinedIn (ball o (σ*s))ᶜ u v) →
    ∀ (A : κ → Set X) (K : κ → Set Sphere) (f : C(X,Sphere)),
      (∀ S : Set Sphere,f ⁻¹' S ⊆ ⋃(d : {d : κ // (S∩K d).Nonempty}),A d.val) →
    ∀ (v : Fin 3 → X) (s : ℝ),0<s →
      (∀ i j,i≠j → s ≤ dist (v i) (v j)) → (∀ i,f (v i)=std i) →
    ∀ (o a₀ b₀ : X) (r R ε η : ℝ),0<r → 0<R → R  ≤  s/2 →
      dist o a₀ ≤ r → R ≤ dist o b₀ →
      0<dist (f o) (f b₀) → 0<ε → 0 ≤ η → η ≤ 1 → 102*η*C^2<ε^2 →
      ε*dist (f o) (f b₀)<dist (f o) (f a₀) →
    ∃ i : Fin 3,∃ p : ℂ,∃ a b : ℝ,0 ≤ a ∧ a ≤ b ∧
      b ≤ 3*(C*dist (f o) (f b₀)) ∧ b-a=η*(C*dist (f o) (f b₀)) ∧
      ∀ t∈Icc a b,
        ∃ x∈⋃(d : {d : κ // (((↑) '' sphere p t : Set Sphere)∩markedChart i '' K d).Nonempty}),A d.val,
        ∃ y∈⋃(d : {d : κ // (((↑) '' sphere p t : Set Sphere)∩markedChart i '' K d).Nonempty}),A d.val,
          ∀ γ : Path x y,range γ∈annulusFamily o (L*r) (σ*R) := by
  obtain ⟨C,hC,hsel⟩:=CannonFiniteNormalization.uniform_relative_chart_selection
  refine ⟨C,hC,?_⟩
  intro X κ _ L σ hinner houter A K f hpre v s hs hv hmark o a₀ b₀ r R ε η hr hR hRs ha₀ hb₀ hdb hε hη hη1 hηε hdiff
  obtain ⟨i,hi,u,hu,x,p,hx,hp,hxp⟩:=hsel f v s hs hv hmark o b₀ R hRs hb₀
  let g : C(X,Sphere):=⟨fun y=>markedChart i (f y),(markedChart i).continuous.comp f.continuous⟩
  have hgpole : g (v i)=∞:=by change markedChart i (f (v i))=∞; rw [hmark,markedChart_pole]
  have hiE:=hinner o o a₀ r hr (by simpa using hr.le) ha₀
  have hoF:=houter o u (v i) R hR hu hi
  let γ : Path o a₀:=hiE.somePath
  let ζ : Path u (v i):=hoF.somePath
  let E:=range γ
  let F:=range ζ
  have hE : IsPreconnected E:=isPreconnected_range γ.continuous
  have hF : IsPreconnected F:=isPreconnected_range ζ.continuous
  have hEa : a₀∈E:=⟨1,γ.target⟩
  have hEo : o∈E:=⟨0,γ.source⟩
  have hFu : u∈F:=⟨0,ζ.source⟩
  have hFv : v i∈F:=⟨1,ζ.target⟩
  have hEin : E ⊆ closedBall o (L*r):=by rintro y ⟨t,rfl⟩; exact hiE.somePath_mem t
  have hFout : F ⊆ (ball o (σ*R))ᶜ:=by rintro y ⟨t,rfl⟩; exact hoF.somePath_mem t
  have hgF : IsPreconnected (g '' F):=hF.image g g.continuous.continuousOn
  have hFp : (p:Sphere)∈g '' F:=⟨u,hFu,hp⟩
  have hFinf : ∞∈g '' F:=⟨v i,hFv,hgpole⟩
  let S:=C*dist (f o) (f b₀)
  have hS : 0<S:=mul_pos (by linarith) hdb
  obtain ⟨q,hq,hpq⟩:=continuum_point_at_radius hgF hFp hFinf hS.le
  have hxy : 102*η*S^2<dist (x:Sphere) (g a₀)^2 := by
    have he : dist (x:Sphere) (g a₀)=dist (f o) (f a₀) := by
      rw [←hx]
      exact (markedChart_isometry i).dist_eq _ _
    rw [he]
    have hh:=mul_lt_mul_of_pos_right hηε (sq_pos_of_pos hdb)
    have hh' : (ε*dist (f o) (f b₀))^2<dist (f o) (f a₀)^2:=
      pow_lt_pow_left₀ hdiff (by positivity) (by decide)
    dsimp [S]
    nlinarith [hh']
  obtain ⟨c,hc,a,b,ha,hab,hb,hw,uE,huE,vE,hvE,huE',hvE'⟩:=spherical_two_center_band
    (hE.image g g.continuous.continuousOn) (show (x:Sphere)∈g '' E from ⟨o,hEo,hx⟩)
    (mem_image_of_mem g hEa) hS hpq hxp hη hη1 hxy
  have hcF : (c:Sphere)∈g '' F:=by rcases hc with rfl|rfl; exact hFp; exact hq
  obtain ⟨uF,huF,hguF⟩:=hcF
  obtain ⟨uE,huE,rfl⟩:=huE
  obtain ⟨vE,hvE,rfl⟩:=hvE
  refine ⟨i,c,a,b,ha,hab,hb,hw,?_⟩
  apply spherical_continua_carrier_crossing g A (fun d=>markedChart i '' K d)
    (preimage_carrier_postcompose A K f (markedChart i) hpre) E F hE hF
    o (L*r) (σ*R) hEin hFout c a b
    ⟨uE,huE,vE,hvE,huE',hvE'⟩
  refine ⟨uF,huF,v i,hFv,?_,?_⟩
  · exact ⟨c,mem_closedBall_self ha,hguF.symm⟩
  · rw [hgpole]
    exact OnePoint.infty_notMem_image_coe
end CannonCarrierCharging

end
end

end OAI
