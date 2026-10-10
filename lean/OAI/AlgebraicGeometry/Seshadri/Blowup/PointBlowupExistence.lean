import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.SmoothSurfaceDimension
import OAI.AlgebraicGeometry.Seshadri.Blowup.FiniteCenters
import OAI.AlgebraicGeometry.Seshadri.Blowup.BlowupProper
import OAI.AlgebraicGeometry.Seshadri.Blowup.BlowupIntegral
import OAI.AlgebraicGeometry.Seshadri.Geometry.RelativeProjectivity

namespace OAI


                                              
section

namespace MaximalSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.Projective MaximalSeshadri.SectionOpens

lemma Surface.centre_support_ne_top (S : Surface) (r : ℕ) (p : Configuration S r) :
    (centreIdeal S r p).support ≠ ⊤ := by
  classical
  intro h
  let q : Fin r → (Spec (.of ℂ) ⟶ S.scheme) := fun i => (p.val i).left
  let f : Fin r → Set S.scheme := fun i => ((q i).ker.support : Set S.scheme)
  have hc : ∀ i, IsClosed (f i) := fun i => ((q i).ker.support).isClosed
  have hu : Set.univ ⊆ ⋃₀ (↑(Finset.univ.image f) : Set (Set S.scheme)) := by
    intro x _
    have hx : x ∈ (centreIdeal S r p).support := by rw [h]; trivial
    obtain ⟨i,hi⟩ := (FinitePointBlowup.mem_centre_support q x).mp hx
    exact Set.mem_sUnion.mpr ⟨f i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,hi⟩
  obtain ⟨z,hz,huz⟩ := isIrreducible_iff_sUnion_isClosed.mp
    (IrreducibleSpace.isIrreducible_univ S.scheme : IsIrreducible (Set.univ : Set S.scheme))
    (Finset.univ.image f) (by
      intro z hz
      obtain ⟨i,-,rfl⟩ := Finset.mem_image.mp hz
      exact hc i) hu
  obtain ⟨i,-,rfl⟩ := Finset.mem_image.mp hz
  have hs := FinitePointBlowup.point_support q
    S.structureMap (fun i => (p.val i).w) i
  let : Subsingleton S.scheme := ⟨fun x y => by
    have hx := huz (show x ∈ Set.univ from trivial)
    have hy := huz (show y ∈ Set.univ from trivial)
    change x ∈ ((q i).ker.support : Set S.scheme) at hx
    change y ∈ ((q i).ker.support : Set S.scheme) at hy
    rw [hs] at hx hy
    exact hx.trans hy.symm⟩
  have hd := topologicalKrullDim_zero_of_discreteTopology S.scheme
  have h2 := S.two_le_dimension
  exact (by norm_num : ¬ (2 : WithBot ℕ∞) ≤ 0) (h2.trans hd)

theorem LineBundle.projective_embedding {X : Scheme.{0}} [IsIntegral X] [CompactSpace X]
    (p : X ⟶ Spec (.of ℂ)) [IsProper p] (L : LineBundle X) (hL : L.IsAmple) :
    ∃ N : ℕ, ∃ e : X ⟶ complexProjectiveSpace N,
      IsClosedImmersion e ∧ e ≫ projectiveSpaceToSpec N = p := by
  classical
  obtain ⟨n,hn,σ,hσ,s,hs,hc⟩ := L.ample_projective_sections p hL
  have hne : Nonempty σ := by
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have hx : x ∈ ⨆ i, isoOpen (s i) := by rw [hs]; trivial
    obtain ⟨i,-⟩ := Opens.mem_iSup.mp hx
    exact ⟨i⟩
  have hpos := Fintype.card_pos_iff.mpr hne
  obtain ⟨N,hN⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hpos)
  let e : Fin (N+1) ≃ σ := ((Fintype.equivFin σ).trans (finCongr hN)).symm
  have ht : (⨆ i,isoOpen (s (e i))) = ⊤ := (e.iSup_comp (g := fun j => isoOpen (s j))).trans hs
  let k := p.appTop.hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom
  refine ⟨N,sectionsMorphism k (s ∘ e) ht,sectionsMorphism_reindex_closed _ s hs e ht,?_⟩
  change sectionsMorphism k (s ∘ e) ht ≫ projectiveBase = p
  exact (sectionsMorphism_over k (s ∘ e) ht).trans (SpecMaps.factor p)

theorem Surface.pointBlowup_exists (S : Surface) (L : LineBundle S.scheme)
    (hL : L.IsAmple) (r : ℕ) (p : Configuration S r) :
    Nonempty (PointBlowup S r p) := by
  classical
  let I := centreIdeal S r p
  let B := BlowupGluing.scheme I
  let π : B ⟶ S.scheme := BlowupGluing.projection I
  have hπ : IsBlowup I π := BlowupGluing.isBlowup I
  let : IsIntegral B := BlowupGluing.scheme_isIntegral I (S.centre_support_ne_top r p)
  let : IsProper π := BlowupGluing.projection_proper I
  let : IsProper (π ≫ S.structureMap) := inferInstance
  let : CompactSpace B := QuasiCompact.compactSpace_of_compactSpace π
  let q : Fin r → (Spec (.of ℂ) ⟶ S.scheme) := fun i => (p.val i).left
  have hq : ∀ i, q i ≫ S.structureMap = 𝟙 _ := fun i => (p.val i).w
  have hd : Function.Injective (fun i => q i (⟨⊥,Ideal.isPrime_bot⟩ : Spec (.of ℂ))) :=
    p.property
  let : SmoothOfRelativeDimension 2 (π ≫ S.structureMap) :=
    FinitePointBlowup.smooth_finite_point_blowup q S.structureMap hq hd π hπ
  obtain ⟨J,ι,hJ⟩ := hπ.1
  obtain ⟨a,n,ha,hn,hA⟩ := hπ.ample_exceptional_twist L hL J ι hJ
  obtain ⟨N,e,he,hep⟩ := ((((L.pow a).pullback π).pow n).tensor J).projective_embedding
    (π ≫ S.structureMap) hA
  let T : Surface := ⟨B,π ≫ S.structureMap,inferInstance,inferInstance,N,e,he,hep⟩
  have hE i : InvertiblePullbackIdeal (q i).ker π :=
    FinitePointBlowup.exceptional_invertible q S.structureMap hq hd π hπ i
  choose E j hj using hE
  exact ⟨⟨T,π,rfl,hπ,E,j,hj⟩⟩

end
end MaximalSeshadri.Geometry

end

end OAI
