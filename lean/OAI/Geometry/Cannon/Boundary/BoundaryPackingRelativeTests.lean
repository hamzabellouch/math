import Mathlib
import OAI.Geometry.Cannon.Conformal.BoundaryFiniteSphereRealizations
import OAI.Geometry.Cannon.PlaneTopology.RealizationVertex
import OAI.Geometry.Cannon.PlaneTopology.SelectedFaceChargingCounts

namespace OAI

section
noncomputable section
namespace CannonRelease
open Set Metric Topology CannonGraph CannonVisual CannonMobius CannonCells CannonUniformization
open CannonEmbeddedArc CannonEmbeddedArc.Arc CannonFaceIncidence CannonFiniteNormalization
open CannonCarrierCharging
open scoped OnePoint

universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_packing_relative_tests (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ L LI σ s r₀ Z : ℝ,1 ≤ L ∧ 1 ≤ LI ∧ 0<σ ∧ σ ≤ 1 ∧ 0<s ∧ 0<r₀ ∧ 0 ≤ Z ∧
    ∃ V : ℝ → ℝ,(∀ ε,0<ε → 0<V ε) ∧
    ∀ mesh : ℝ,0 < mesh → mesh ≤ r₀ → ∀ T : Finset (Boundary D),
      (∀ x∈T,∀ y∈T,x≠y → mesh ≤ dist x y) →
      (∀ x : Boundary D,∃ y∈T,dist x y ≤ mesh) →
    ∃ g : C(Boundary D,Sphere),Function.Surjective g ∧
      (∀ x y,g x=g y → dist x y ≤ 2*(L*mesh)) ∧
      ∀ (o a b : Boundary D) (r R ε : ℝ),0<r → 0<R → R ≤ s →
        dist o a ≤ r → R ≤ dist o b → 0<dist (g o) (g b) → 0<ε →
        ε*dist (g o) (g b)<dist (g o) (g a) →
      V ε ≤ Z*modulus (fun i : T=>ball i.val (2*mesh)) (annulusFamily o (LI*r) (σ*R)) := by
  classical
  let _ := visualMetricSpace D hδ
  let _ : LocallyPathConnectedSpace SphereTwo:=CannonPaths.sphere_locallyPathConnected
  let _ : LocallyPathConnectedSpace (Boundary D):=φ.symm.isQuotientMap.locallyPathConnectedSpace
  dsimp only
  obtain ⟨M,L,r₀,hM,hL,hr₀,N,c,hc,hc1,kr,kc,hprod⟩:=boundary_finite_sphere_realizations D hδ φ
  obtain ⟨LI,hLI,hi⟩:=boundary_controlled_paths D hδ φ
  obtain ⟨σ,hσ,hσ1,ho⟩:=boundary_outside_paths D hδ φ
  have hinner : ∀ o u v : Boundary D,∀ r : ℝ,0<r → dist o u ≤ r → dist o v ≤ r →
      JoinedIn (closedBall o (LI*r)) u v := by
    intro o u v r hr hu hv
    exact (hi o u v r hr hu hv).mono (fun x hx=>by
      change dist o x<LI*r at hx
      rw [mem_closedBall,dist_comm]
      exact hx.le)
  have houter : ∀ o u v : Boundary D,∀ r : ℝ,0<r → r ≤ dist o u → r ≤ dist o v →
      JoinedIn (ball o (σ*r))ᶜ u v := by
    intro o u v r hr hu hv
    exact (ho o u v r hr hu hv).mono (fun x hx=>by
      change σ*r<dist o x at hx
      rw [mem_compl_iff,mem_ball,dist_comm]
      exact not_lt.mpr hx.le)
  obtain ⟨V,hV,hcost⟩:=packing_relative_modulus_cost LI σ hinner houter
  let marks : Fin 3 → Boundary D:=fun i=>φ.symm (roundChart (std i))
  have hmarks : Function.Injective marks:=φ.symm.injective.comp (roundChart.injective.comp std_injective)
  obtain ⟨sep,hsep,hsepmarks⟩:=three_separation marks hmarks
  have hMp : 0<1+M:=by linarith
  let small:=min r₀ (sep/(8*(1+M)))
  have hsmall : 0<small:=lt_min hr₀ (div_pos hsep (by positivity))
  let Z : ℝ:=324*(26*(N:ℝ)+1)*(kr:ℝ)*(N*kc:ℕ)
  refine ⟨L,LI,σ,sep/4,small,Z,hL,hLI,hσ,hσ1,by positivity,hsmall,by dsimp [Z]; positivity,V,hV,?_⟩
  intro mesh hm hms T hTsep hcover
  have hmesh₀ : mesh ≤ r₀:=hms.trans (min_le_left _ _)
  have hsmallmesh : (1+M)*mesh ≤ sep/8 := by
    have hh:=(le_div_iff₀ (show 0<8*(1+M) by positivity)).mp (hms.trans (min_le_right _ _))
    nlinarith
  let : Infinite (Boundary D):=Infinite.of_injective
    (fun z : ℂ=>φ.symm (roundChart (z:Sphere)))
    (φ.symm.injective.comp (roundChart.injective.comp OnePoint.coe_injective))
  obtain ⟨p,hp⟩:=T.exists_notMem
  obtain ⟨e,he,heR,ι,hι,hιd,hιn,H,hH,Q,hQ,hT,hK,hE,hD,hdiam,hN,hrow,hcol,hdeg,htri,hfaces,
    out,hout,B,z,hz,hlen,hdis,hring,hull,J,hJ,hJI,f,hfs,hfin,hfout,hfedge,hfiber,hconn,hpre,hnorm⟩:=
    hprod mesh hm hmesh₀ T hTsep hcover p hp
  let _ : Fintype ι:=hι
  let _ : DecidableEq ι:=hιd
  let _ : Nonempty ι:=hιn
  let _ : Fintype (Faces H):=hfaces
  obtain ⟨v,hv,hva,Norm,hNorm,g,hg,hgs,hmark,rest⟩:=packing_center_normalized_realization
    H e T mesh M sep marks hT hcover hE hsepmarks (by linarith) z B.radius
    (fun v _=>B.radius_pos v) hdis f hfs hfedge
  have hmarksep : ∀ i j,i≠j → sep/2 ≤ dist (e (v i).val) (e (v j).val) := by
    intro i j hij
    have hs:=hsepmarks i j hij
    have h1:=hva i
    have h2:=hva j
    have ht:=dist_triangle (marks i) (e (v i).val) (marks j)
    have ht':=dist_triangle (e (v i).val) (e (v j).val) (marks j)
    rw [dist_comm (e (v j).val) (marks j)] at ht'
    linarith
  have hNm (i : Fin 3) : Norm (z (v i).val)=std i := by
    rw [←realization_at_vertex H e z f hfedge (v i),←hg]
    exact hmark i
  have hpre' : ∀ S : Set Sphere,g ⁻¹' S ⊆
      ⋃(d : {d : Faces H // (S∩Norm '' sphereTile H z out d).Nonempty}),compactifiedFace H e d.val := by
    intro S x hx
    have hh:=preimage_carrier_postcompose (compactifiedFace H e) (sphereTile H z out) f Norm hpre S
    apply hh
    change Norm (f x)∈S
    rw [←hg]
    exact hx
  obtain ⟨hcycles,hinter,hfill⟩:=B.hull_geometry hH Q hQ hK htri z hz
  refine ⟨g,hgs,?_,?_⟩
  · intro x y hxy
    exact hfiber x y (Norm.injective (by simpa only [hg] using hxy))
  · intro o a b r R ε hr hR hRs ha hb hgb hε hdiff
    exact hcost H hH Q hQ hK N hdeg e he.continuous z B.radius B.radius_pos hlen hdis hcycles
      out hinter hfill Norm hNorm T mesh L hm hcover hdiam kr kc hrow hcol hconn g hpre'
      (fun i=>(v i).val) (sep/2) (by positivity) (fun i=>(v i).property) hmarksep hmark hNm
      o a b r R ε hr hR (by linarith) ha hb hgb hε hdiff
end CannonRelease

end
end

end OAI
