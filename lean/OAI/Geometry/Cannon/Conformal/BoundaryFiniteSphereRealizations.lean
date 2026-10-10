import Mathlib
import OAI.Geometry.Cannon.Boundary.BoundaryUniformCirclePacking
import OAI.Geometry.Cannon.PlaneTopology.BoundaryRadiusControl
import OAI.Geometry.Cannon.PlaneTopology.ClosedInsideSegment
import OAI.Geometry.Cannon.Conformal.SphereTile
import OAI.Geometry.Cannon.Modulus.UniformOriginalChargingCounts

namespace OAI

section
section
section
noncomputable section
namespace CannonRelease
open Set Metric Topology unitInterval CannonGraph CannonEmbeddedArc CannonEmbeddedArc.Arc CannonFaceIncidence
open scoped OnePoint

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
attribute [local instance] Classical.propDecidable
variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_finite_sphere_realizations (φ : Boundary D ≃ₜ SphereTwo) :
    let _ := visualMetricSpace D hδ
    ∃ M L r₀ : ℝ,1≤M ∧ 1≤L ∧ 0<r₀ ∧ ∃ N : ℕ, ∃ c : ℝ,0<c ∧ c≤1 ∧ ∃ kr kc : ℕ,
    ∀ r : ℝ,0<r → r≤r₀ → ∀ T : Finset (Boundary D),
      (∀ x∈T,∀ y∈T,x≠y → r≤dist x y) →
      (∀ x : Boundary D,∃ y∈T,dist x y≤r) →
      ∀ p : Boundary D,p∉T →
      ∃ e : ℂ → Boundary D,IsOpenEmbedding e ∧ range e={p}ᶜ ∧
      ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (_ : Nonempty κ) (H : κ → Arc ℂ),
        Pairwise (fun i j=>Compatible (H i) (H j)) ∧
        ∃ Q : Finset (ℂ × ℂ),(∀ i,range (H i)⊆⋃q∈Q,segment ℝ q.1 q.2) ∧
        (T:Set (Boundary D))⊆e '' (⋃ i,range (H i)) ∧
        (∀ q : ℂ,IsPreconnected ((⋃ i,range (H i))\{q})) ∧
        (∀ i,∀ t s : I,dist (e (H i t)) (e (H i s))≤M*r) ∧
        (∀ d,∀ z∈closure (face H d),∀ w∈closure (face H d),dist (e z) (e w)≤L*r) ∧
        (∀ d,∀ x∈compactifiedFace H e d,∀ y∈compactifiedFace H e d,dist x y≤L*r) ∧
        (∀ x : Boundary D,Nat.card {i : κ | ∃ t:I,dist (e (H i t)) x<2*M*r}≤N) ∧
        (∀ x : Boundary D,(T.filter (fun y=>dist x y<(L+3)*r)).card≤kr) ∧
        (∀ x : Boundary D,Nat.card {v : ℂ | Vertex H v ∧ dist (e v) x<(L+3)*r}≤kc) ∧
        (∀ v : ℂ,Nat.card {i : κ | v∈range (H i)}≤N) ∧
        (∀ d : Faces H,(faceVertices H d).card=3) ∧
        ∃ _ : Fintype (Faces H),∃ out : Faces H,
          (∀ d,d≠out → IsCompact (closure (face H d))) ∧
          ∃ B : DevelopedFaces H out, ∃ z : ℂ → ℂ,
            (∀ d,d≠out → ∀ q∈faceVertices H d,z q=B.chart d q) ∧
            (∀ i,dist (z (H i 0)) (z (H i 1))=B.radius (H i 0)+B.radius (H i 1)) ∧
            (∀ u,Vertex H u → ∀ v,Vertex H v → u≠v → B.radius u+B.radius v≤dist (z u) (z v)) ∧
            (∀ j,∀ u v,Spans (H j) u v → c*B.radius u≤B.radius v ∧ c*B.radius v≤B.radius u) ∧
            (∀ d,∀ v∈faceVertices H d,faceHull H z d⊆closedBall (z v) ((1+c⁻¹)*B.radius v)) ∧
            ∃ J : OnePoint ℂ≃ₜOnePoint ℂ,
              (∀ x∈frontier (faceHull H z out),J (x:OnePoint ℂ)=(x:OnePoint ℂ)) ∧
              J '' ((↑) '' faceHull H z out : Set (OnePoint ℂ))=
                (((↑) '' interior (faceHull H z out) : Set (OnePoint ℂ)))ᶜ ∧
              ∃ f : C(Boundary D,OnePoint ℂ),Function.Surjective f ∧
                (∀ d : Faces H,d≠out → MapsTo f (compactifiedFace H e d) ((↑) '' faceHull H z d)) ∧
                MapsTo f (compactifiedFace H e out)
                  (J '' ((↑) '' faceHull H z out : Set (OnePoint ℂ))) ∧
                (∀ i t,f (e (H i t))=((Path.segment (z (H i 0)) (z (H i 1)) t:ℂ):OnePoint ℂ)) ∧
                (∀ x y : Boundary D,f x=f y → dist x y≤2*(L*r)) ∧
                (∀ S : Set (OnePoint ℂ),IsPreconnected S →
                  IsPreconnected (⋃ (d : {d : Faces H // (S∩sphereTile H z out d).Nonempty}),
                    compactifiedFace H e d.val)) ∧
                (∀ S : Set (OnePoint ℂ),f ⁻¹' S⊆
                  ⋃ (d : {d : Faces H // (S∩sphereTile H z out d).Nonempty}),
                    compactifiedFace H e d.val) ∧
                (∀ a : Fin 3 → Boundary D,(∀ i j,i≠j → 2*(L*r)<dist (a i) (a j)) →
                  ∃ N : OnePoint ℂ≃ₜOnePoint ℂ,N∈CannonMobius.biholomorphic ∧
                    ∃ g : C(Boundary D,OnePoint ℂ),(∀ x,g x=N (f x)) ∧ Function.Surjective g ∧
                      (∀ i,g (a i)=CannonMobius.std i) ∧
                      (∀ x y,g x=g y → dist x y≤2*(L*r))) := by
  classical
  let _ := visualMetricSpace D hδ
  dsimp only
  obtain ⟨M,L,r₀,hM,hL,hr₀,N,hgraph⟩ := boundary_uniform_circle_packing D hδ φ
  obtain ⟨c,hc,hc1,hcgraph⟩ := exists_global_radius_constant N
  obtain ⟨Q₀,C,_hQ₀,hC,hpoly⟩:=relative_polynomial_packing D hδ
  have hpolypack : CannonPacking.PolynomialPacking (X:=Boundary D) Q₀ C:=hpoly
  obtain ⟨kr,kc,hcharge⟩:=CannonCarrierCharging.uniform_original_charging_counts Q₀ C L hpolypack hC.le hL N
  have hL4 : 0<L+4 := by linarith
  refine ⟨M,L,min r₀ ((L+4)⁻¹),hM,hL,lt_min hr₀ (inv_pos.mpr hL4),N,c,hc,hc1,kr,kc,?_⟩
  intro r hr hrs T hsep hcover p hp
  have hrs₀ : r≤r₀:=hrs.trans (min_le_left _ _)
  have hscale : (L+4)*r≤1 := by
    have hh:=mul_le_mul_of_nonneg_left (hrs.trans (min_le_right _ _)) hL4.le
    simpa only [mul_inv_cancel₀ hL4.ne'] using hh
  obtain ⟨e,he,heR,κ,hκ,hκd,hκn,H,hH,Q,hQ,hT,hK,hE,hD,hN,hdeg,htri,hfaces,hpack⟩ :=
    hgraph r hr hrs₀ T hsep hcover p hp
  let _ : Fintype κ := hκ
  let _ : DecidableEq κ := hκd
  let _ : Nonempty κ := hκn
  let _ : Fintype (Faces H) := hfaces
  obtain ⟨hrow,hcol⟩:=hcharge r M hr hM hscale T hsep hcover H e hN
  obtain ⟨out,hout⟩:=outer_face_compact_others H
  obtain ⟨B,-⟩:=hpack out
  obtain ⟨z,hz,hlen,hdis,J,hJ,hJI,f,hf,hfin,hfout,hfedge⟩:=B.spherical_realization hH Q hQ hK htri hout
  obtain ⟨O⟩:=facialCycle_exists H hH Q hQ hK out (htri out)
  have hring : ∀ j u v,Spans (H j) u v → c*B.radius u≤B.radius v ∧ c*B.radius v≤B.radius u := by
    intro j u v huv
    exact ⟨hcgraph H out B hH Q hQ hK z hz hlen hdis O u v j huv.vertex_left (hdeg u) huv,
      hcgraph H out B hH Q hQ hK z hz hlen hdis O v u j huv.vertex_right (hdeg v) huv.symm⟩
  let E : OnePoint ℂ≃ₜBoundary D:=OnePoint.equivOfIsEmbeddingOfRangeEq p e he.isEmbedding heR
  let g : C(Boundary D,OnePoint ℂ):=f.comp ⟨E.symm,E.symm.continuous⟩
  have hge (x : ℂ) : g (e x)=f (x:OnePoint ℂ) := by
    change f (E.symm (E (x:OnePoint ℂ)))=f (x:OnePoint ℂ)
    rw [E.symm_apply_apply]
  have hfin' (d : Faces H) (hd : d≠out) :
      MapsTo g (compactifiedFace H e d) ((↑) '' faceHull H z d) := by
    apply compactifiedFace_mapsTo H e g d _
    · exact ((((faceVertices H d).finite_toSet.image z).isCompact_convexHull ℝ).image
        OnePoint.continuous_coe).isClosed
    · intro x hx
      simpa only [Function.comp_apply,hge] using hfin d hd hx
  have hfout' : MapsTo g (compactifiedFace H e out)
      (J '' ((↑) '' faceHull H z out : Set (OnePoint ℂ))) := by
    apply compactifiedFace_mapsTo H e g out _
    · exact (((((faceVertices H out).finite_toSet.image z).isCompact_convexHull ℝ).image
        OnePoint.continuous_coe).image J.continuous).isClosed
    · intro x hx
      simpa only [Function.comp_apply,hge] using hfout hx
  have hmaps (d : Faces H) : MapsTo g (compactifiedFace H e d) (sphereTile H z out d) := by
    by_cases hd : d=out
    · subst d
      simpa [sphereTile,hJI] using hfout'
    · simpa only [sphereTile,ite_eq_right hd] using hfin' d hd
  have hdiam := fun d=>compactifiedFace_dist_bound H e d (L*r) (hD d)
  obtain ⟨hcycles,hinter,hfill⟩:=B.hull_geometry hH Q hQ hK htri z hz
  have hdense : DenseRange e := by
    have hd : DenseRange (E ∘ ((↑):ℂ → OnePoint ℂ)) :=
      E.surjective.denseRange.comp OnePoint.denseRange_coe E.continuous
    exact hd
  have hcorner (d : Faces H) : (faceVertices H d).Nonempty := by
    rw [←Finset.card_pos,htri d]
    norm_num
  have hsourcecover := (compactified_face_interiors_cover H hH Q hQ hcorner e he p heR hdense).1
  have hfiber := sphere_realization_fiber_bound e he.continuous g hsourcecover z B.radius B.radius_pos
      hlen hdis hcycles hinter hfill hmaps (L*r) hdiam
  refine ⟨e,he,heR,κ,hκ,hκd,hκn,H,hH,Q,hQ,hT,hK,hE,hD,hdiam,hN,hrow,hcol,hdeg,htri,hfaces,out,hout,
    B,z,hz,hlen,hdis,hring,?_,J,hJ,hJI,g,hf.comp E.symm.surjective,hfin',hfout',?_,hfiber,?_,?_,?_⟩
  · intro d v hv
    obtain ⟨C⟩:=facialCycle_exists H hH Q hQ hK d (htri d)
    exact C.hull_radius_bound z B.radius B.radius_pos c hc hlen hring hv
  · intro i t
    rw [hge,hfedge]
  · intro S hS
    exact sphere_carrier_preconnected e he.continuous z B.radius B.radius_pos hlen hdis
      hcycles hinter hfill S hS
  · exact CannonFiniteCarrier.preimage_subset_carrier _ _ g hsourcecover hmaps
  · intro a ha
    exact CannonMobius.normalize_finite_realization g (hf.comp E.symm.surjective) (2*(L*r)) hfiber a ha
end CannonRelease

end
end
end
end

end OAI
