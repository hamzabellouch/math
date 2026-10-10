import Mathlib
import OAI.CategoryTheory.Thomason.SimplexBoxes

namespace OAI

/-! Fiber Recognition. -/

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

theorem weak_box_injective (I : Type u) [Fintype I] [LinearOrder I]
    (n : ℕ) (e : I ≃ Fin (n+1)) {K L : SSet.{u}} [SSet.KanComplex K]
    (r : K ⟶ L) (hr : simplicialWeakEquivalences r) (x : K _⦋0⦌)
    (a b : nerve (Finset I) ⟶ K)
    (ha : (boxBoundary I).ι ≫ a = SSet.const x)
    (hb : (boxBoundary I).ι ≫ b = SSet.const x)
    (H : BasedHomotopy (boxBoundary I).ι (SSet.const (r.app _ x)) (a ≫ r) (b ≫ r)) :
    BasedHomotopy (boxBoundary I).ι (SSet.const x) a b := by
  let f := boxPairProjection I
  let g := boxBoundaryProjection I
  let j := nerveMap (inclusion (Cubical.boundaryFaces I)).toFunctor
  have ha' : j ≫ f ≫ a = SSet.const x := by
    rw [← Category.assoc,box_pair_square,Category.assoc,ha,SSet.comp_const]
  have hb' : j ≫ f ≫ b = SSet.const x := by
    rw [← Category.assoc,box_pair_square,Category.assoc,hb,SSet.comp_const]
  have H' : BasedHomotopy j (SSet.const (r.app _ x)) ((f ≫ a) ≫ r) ((f ≫ b) ≫ r) := by
    simpa only [SSet.comp_const,Category.assoc] using based_homotopy_pre
      _ j f g (box_pair_square _) _ H
  obtain ⟨G,hG⟩ := weak_cubical_injective (PartOrd.of (NonemptyFiniteChains (Finset I)))
    (PartOrd.of (Cubical.boundaryFaces I)) (inclusion (Cubical.boundaryFaces I))
    Subtype.val_injective n (finiteBoxPair I n e) r hr x (f ≫ a) (f ≫ b) ha' hb' H'
  exact pair_local_injective_plain _ j f g (box_pair_square _)
    (boxPairProjection_local _) (boxBoundaryProjection_local _) _ a b ha hb G
    (by simpa only [SSet.comp_const] using hG)

theorem weak_box_surjective (I : Type u) [Fintype I] [LinearOrder I]
    (n : ℕ) (e : I ≃ Fin (n+1)) {K L : SSet.{u}} [SSet.KanComplex K] [SSet.KanComplex L]
    (r : K ⟶ L) (hr : simplicialWeakEquivalences r) (x : K _⦋0⦌)
    (a : nerve (Finset I) ⟶ L)
    (ha : (boxBoundary I).ι ≫ a = SSet.const (r.app _ x)) :
    ∃ b : nerve (Finset I) ⟶ K, (boxBoundary I).ι ≫ b = SSet.const x ∧
      BasedHomotopy (boxBoundary I).ι (SSet.const (r.app _ x)) (b ≫ r) a := by
  let f := boxPairProjection I
  let g := boxBoundaryProjection I
  let j := nerveMap (inclusion (Cubical.boundaryFaces I)).toFunctor
  have ha' : j ≫ f ≫ a = SSet.const (r.app _ x) := by
    rw [← Category.assoc,box_pair_square,Category.assoc,ha,SSet.comp_const]
  obtain ⟨b',hb',H'⟩ := weak_cubical_surjective (PartOrd.of (NonemptyFiniteChains (Finset I)))
    (Cubical.boundaryFaces I) n (finiteBoxPair I n e) r hr x (f ≫ a) ha'
  obtain ⟨b,G,hb,hG⟩ := pair_local_surjective_plain (boxBoundary I).ι j f g
    (box_pair_square _) (boxPairProjection_local _) (boxBoundaryProjection_local _)
    (SSet.const x) b' (by simpa only [SSet.comp_const] using hb')
  have HG : BasedHomotopy j (SSet.const (r.app _ x)) ((f ≫ b) ≫ r) (b' ≫ r) := by
    simpa only [SSet.comp_const,SSet.const_comp] using
      based_homotopy_post j (SSet.const x) ⟨G,by simpa only [SSet.comp_const] using hG⟩ r
  obtain ⟨F,hF⟩ := based_homotopy_trans j (SSet.const (r.app _ x)) HG H'
  let F' : SSet.Homotopy (f ≫ (b ≫ r)) (f ≫ a) := CoherentGluing.toHomotopy F.h
    (by simpa only [Category.assoc] using F.h₀) F.h₁
  refine ⟨b,hb,pair_local_injective_plain _ j f g (box_pair_square _)
    (boxPairProjection_local _) (boxBoundaryProjection_local _)
    (SSet.const (r.app _ x)) (b ≫ r) a ?_ ha F' ?_⟩
  · rw [← Category.assoc,hb,SSet.const_comp]
  · simpa only [F', CoherentGluing.toHomotopy, SSet.comp_const] using hF
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition

lemma zero_face_horn_iff (n d : ℕ) (a : (Δ[n] : SSet.{u}) _⦋d⦌) :
    (SSet.stdSimplex.δ (0 : Fin (n+2))).app _ a ∈ (SSet.horn (n+1) 0).obj _ ↔
      a ∈ (SSet.boundary n).obj _ := by
  rw [SSet.mem_horn_iff_notMem_range, SSet.mem_boundary_iff_notMem_range]
  constructor
  · rintro ⟨j,hj,h⟩
    obtain ⟨k,rfl⟩ := Fin.exists_succ_eq.mpr hj
    refine ⟨k,?_⟩
    rintro ⟨l,hl⟩
    apply h
    refine ⟨l,?_⟩
    change (0 : Fin (n+2)).succAbove (a l) = k.succ
    simpa using congrArg Fin.succ hl
  · rintro ⟨k,hk⟩
    refine ⟨k.succ,Fin.succ_ne_zero _,?_⟩
    rintro ⟨l,hl⟩
    apply hk
    refine ⟨l,?_⟩
    change (0 : Fin (n+2)).succAbove (a l) = k.succ at hl
    simpa using hl

def boundaryInHorn (n : ℕ) : (∂Δ[n] : SSet.{u}) ⟶ Λ[n+1,0] :=
  SSet.Subcomplex.lift ((SSet.boundary n).ι ≫ SSet.stdSimplex.δ 0) (by
    intro d a ha
    obtain ⟨x,rfl⟩ := ha
    exact (zero_face_horn_iff n d.unop.len x.1).2 x.2)

def hornInBoundary (n : ℕ) : (Λ[n+1,0] : SSet.{u}) ⟶ ∂Δ[n+1] :=
  SSet.Subcomplex.homOfLE (by
    intro d a ha
    obtain ⟨j,_,hj⟩ := (SSet.mem_horn_iff_notMem_range a 0).1 ha
    exact (SSet.mem_boundary_iff_notMem_range a).2 ⟨j,hj⟩)

@[reassoc] lemma boundaryInHorn_ι (n : ℕ) :
    boundaryInHorn.{u} n ≫ (SSet.horn (n+1) 0).ι =
      (SSet.boundary n).ι ≫ SSet.stdSimplex.δ 0 := rfl
@[reassoc] lemma hornInBoundary_ι (n : ℕ) :
    hornInBoundary.{u} n ≫ (SSet.boundary (n+1)).ι = (SSet.horn (n+1) 0).ι := rfl
@[reassoc] lemma boundaryInHorn_square (n : ℕ) :
    (SSet.boundary n).ι ≫ SSet.boundary.ι (0 : Fin (n+2)) =
      boundaryInHorn.{u} n ≫ hornInBoundary n := rfl

instance (n : ℕ) : Mono (hornInBoundary.{u} n) := by
  exact mono_of_mono_fac (hornInBoundary_ι.{u} n)

lemma boundary_horn_isPushout (n : ℕ) :
    IsPushout (SSet.boundary n).ι (boundaryInHorn.{u} n)
      (SSet.boundary.ι (0 : Fin (n+2))) (hornInBoundary n) where
  w := boundaryInHorn_square n
  isColimit' := ⟨evaluationJointlyReflectsColimits _ (fun d =>
    (PushoutCocone.isColimitMapCoconeEquiv _ _).2 (by
      have hs : IsPushout ((SSet.boundary.{u} n).ι.app d) ((boundaryInHorn.{u} n).app d)
          ((SSet.boundary.ι.{u} (0 : Fin (n+2))).app d) ((hornInBoundary.{u} n).app d) := by
        apply Types.isPushout_of_isPullback_of_mono'
        · rw [Types.isPullback_iff]
          refine ⟨rfl,?_,?_⟩
          · intro x y h
            exact Subtype.ext h.1
          · intro x y h
            have h' : (SSet.stdSimplex.δ (0 : Fin (n+2))).app d x = y.1 :=
              congrArg Subtype.val h
            have hx : x ∈ (SSet.boundary n).obj d :=
              (zero_face_horn_iff n d.unop.len x).1 (h' ▸ y.2)
            exact ⟨⟨x,hx⟩,rfl,Subtype.ext h'⟩
        · apply Set.eq_univ_of_forall
          intro z
          by_cases hz : z.1 ∈ (SSet.horn (n+1) 0).obj d
          · exact Or.inr ⟨⟨z.1,hz⟩,Subtype.ext rfl⟩
          · obtain ⟨j,hj⟩ := (SSet.mem_boundary_iff_notMem_range z.1).1 z.2
            have hj0 : j = 0 := by
              by_contra h
              exact hz ((SSet.mem_horn_iff_notMem_range _ _).2 ⟨j,h,hj⟩)
            subst j
            let x := SSet.stdSimplex.objEquiv.symm
              (SimplexCategory.factor_δ (SSet.stdSimplex.objEquiv z.1) 0)
            refine Or.inl ⟨x,Subtype.ext ?_⟩
            apply SSet.stdSimplex.objEquiv.injective
            exact SimplexCategory.factor_δ_spec _ _ (fun k h => hj ⟨k,h⟩)
        · intro x y _ _ h
          exact (CategoryTheory.mono_iff_injective ((hornInBoundary.{u} n).app d)).1
            inferInstance h
      exact hs.isColimit))⟩
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal HornSubdivision KanPath Contiguity

lemma simplex_homotopic_const {K : SSet.{u}} (n : ℕ) (a : Δ[n] ⟶ K) :
    ∃ x : K _⦋0⦌, Homotopic a (SSet.const x) := by
  let P := ULift.{u} (Fin (n+1))
  let q : P := ⟨0⟩
  let v : (nerve P) _⦋0⦌ := (Functor.const (Fin 1)).obj q
  let e := SSet.stdSimplex.isoNerve.{u} n
  have H : Homotopic (nerveMap (constantOrder P q).toFunctor) (𝟙 (nerve P)) :=
    homotopic_of_homotopy (orderHomotopy (constantOrder P q) OrderHom.id (fun x => Fin.zero_le x.down))
  have hc : nerveMap (constantOrder P q).toFunctor = SSet.const v := nerve_constant_vertex v
  rw [hc] at H
  have H' := homotopic_pre e.hom (homotopic_post H (e.inv ≫ a))
  refine ⟨(e.inv ≫ a).app _ v, homotopic_symm ?_⟩
  simpa only [SSet.const_comp,SSet.comp_const,Category.id_comp,← Category.assoc,
    Iso.hom_inv_id,Category.id_comp, NatTrans.comp_app, types_comp_apply] using H'

lemma straighten_boundary {K : SSet.{u}} [SSet.KanComplex K]
    (n : ℕ) (a : (∂Δ[n+1] : SSet.{u}) ⟶ K) :
    ∃ x : K _⦋0⦌, ∃ b : (∂Δ[n+1] : SSet.{u}) ⟶ K,
      Homotopic a b ∧ hornInBoundary n ≫ b = SSet.const x := by
  obtain ⟨g,hg⟩ := SSet.KanComplex.hornFilling (hornInBoundary n ≫ a)
  obtain ⟨x,H⟩ := simplex_homotopic_const (n+1) g
  have H' := homotopic_pre (SSet.horn (n+1) 0).ι H
  rw [← hg,SSet.comp_const] at H'
  obtain ⟨G⟩ := homotopy_of_homotopic H'
  obtain ⟨b,Gb,hb,_⟩ := homotopy_extension (hornInBoundary n) a G
  exact ⟨x,b,homotopic_of_homotopy Gb,hb⟩

lemma nullhomotopy_boundary_of_face {K : SSet.{u}}
    (n : ℕ) (x : K _⦋0⦌) (b : (∂Δ[n+1] : SSet.{u}) ⟶ K)
    (hb : hornInBoundary n ≫ b = SSet.const x)
    (H : BasedHomotopy (SSet.boundary n).ι (SSet.const x)
      (SSet.boundary.ι (0 : Fin (n+2)) ≫ b) (SSet.const x)) :
    Nonempty (SSet.Homotopy b (SSet.const x)) := by
  obtain ⟨H,hH⟩ := H
  let sq := boundary_horn_isPushout.{u} n
  have w : (SSet.boundary n).ι ≫ curryR H.h =
      boundaryInHorn n ≫ curryR (SSet.const x) := by
    apply uncurryR_injective
    simp only [uncurryR_pre,uncurryR_curryR,hH,SSet.comp_const]
  let g := sq.desc (curryR H.h) (curryR (SSet.const x)) w
  have h₀ : g ≫ eval₀ K = b := by
    apply sq.hom_ext
    · rw [← Category.assoc,sq.inl_desc,comp_eval₀,uncurryR_curryR,H.h₀]
    · rw [← Category.assoc,sq.inr_desc,comp_eval₀,uncurryR_curryR,SSet.comp_const,hb]
  have h₁ : g ≫ eval₁ K = SSet.const x := by
    apply sq.hom_ext
    · rw [← Category.assoc,sq.inl_desc,comp_eval₁,uncurryR_curryR,H.h₁,SSet.comp_const]
    · rw [← Category.assoc,sq.inr_desc,comp_eval₁,uncurryR_curryR,SSet.comp_const,SSet.comp_const]
  exact ⟨CoherentGluing.toHomotopy (uncurryR g)
    (by rw [← comp_eval₀,h₀]) (by rw [← comp_eval₁,h₁])⟩
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal HornSubdivision KanPath Contiguity

theorem terminal_rlp_of_nullsimplices {K : SSet.{u}} [SSet.KanComplex K]
    (x₀ : K _⦋0⦌)
    (h : ∀ (n : ℕ) (x : K _⦋0⦌) (a : Δ[n] ⟶ K),
      (SSet.boundary n).ι ≫ a = SSet.const x →
      BasedHomotopy (SSet.boundary n).ι (SSet.const x) a (SSet.const x)) :
    SSet.modelCategoryQuillen.I.rlp (terminal.from K) := by
  rintro _ _ _ ⟨n⟩
  constructor
  intro a b sq
  cases n with
  | zero =>
    exact ⟨⟨{ l := SSet.const x₀, fac_left := SSet.boundary.hom_ext₀, fac_right := Subsingleton.elim _ _ }⟩⟩
  | succ n =>
    obtain ⟨x,c,Hac,hc⟩ := straighten_boundary n a
    have he : (SSet.boundary n).ι ≫ (SSet.boundary.ι (0 : Fin (n+2)) ≫ c) =
        SSet.const x := by
      rw [← Category.assoc,boundaryInHorn_square,Category.assoc,hc,SSet.comp_const]
    obtain ⟨H⟩ := nullhomotopy_boundary_of_face n x c hc (h n x _ he)
    have H' := homotopic_symm (homotopic_trans Hac (homotopic_of_homotopy H))
    obtain ⟨G⟩ := homotopy_of_homotopic H'
    have G' : SSet.Homotopy ((SSet.boundary (n+1)).ι ≫ SSet.const x) a := by
      simpa only [SSet.comp_const] using G
    obtain ⟨l,_,hl,_⟩ := homotopy_extension (SSet.boundary (n+1)).ι (SSet.const x) G'
    exact ⟨⟨{ l := l, fac_left := hl, fac_right := Subsingleton.elim _ _ }⟩⟩

lemma based_homotopy_zero {K : SSet.{u}} {a b : Δ[0] ⟶ K}
    (x : K _⦋0⦌) (H : SSet.Homotopy a b) :
    BasedHomotopy (SSet.boundary 0).ι (SSet.const x) a b := by
  refine ⟨H,?_⟩
  ext n ⟨⟨t,ht⟩,s⟩
  simp at ht

theorem weak_terminal_rlp {K : SSet.{u}} [SSet.KanComplex K]
    (hw : simplicialWeakEquivalences (terminal.from K)) :
    SSet.modelCategoryQuillen.I.rlp (terminal.from K) := by
  let p := terminal.from K
  let v : (⊤_ SSet.{u}) _⦋0⦌ := SSet.yonedaEquiv (terminal.from (Δ[0] : SSet.{u}))
  obtain ⟨z,hz⟩ := (KanQuillen.map_components_bijective_of_weak p hw).2 (SSet.π₀.mk v)
  obtain ⟨z,rfl⟩ := SSet.π₀.mk_surjective z
  apply terminal_rlp_of_nullsimplices z
  intro n x a ha
  cases n with
  | zero =>
    have hv : SSet.π₀.mk (SSet.yonedaEquiv a) = SSet.π₀.mk x := by
      apply (KanQuillen.map_components_bijective_of_weak p hw).1
      apply congrArg SSet.π₀.mk
      apply SSet.yonedaEquiv.symm.injective
      subsingleton
    obtain ⟨H⟩ := homotopy_of_homotopic (component_homotopic_const hv)
    have H' : SSet.Homotopy a (SSet.const x) := by
      simpa only [← SSet.yonedaEquiv_symm_zero,Equiv.symm_apply_apply] using H
    exact based_homotopy_zero x H'
  | succ n =>
    apply weak_simplex_injective n p hw x a (SSet.const x) ha (SSet.comp_const _ _)
    have he : a ≫ p = SSet.const x ≫ p := Subsingleton.elim _ _
    rw [he]
    exact based_homotopy_refl _ _ _ (by rw [← Category.assoc,SSet.comp_const,SSet.const_comp])
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal KanPath HornSubdivision Contiguity

lemma correct_nullhomotopy_to_fiber {A B K L : SSet.{u}}
    (i : B ⟶ A) [Mono i] (p : K ⟶ L) (hp : simplicialFibrations p)
    (x : K _⦋0⦌) {a : A ⟶ K}
    (H : SSet.Homotopy a (SSet.const x))
    (J : SSet.Homotopy (SSet.const (X := A) x) (SSet.const x))
    (hH : i ▷ Δ[1] ≫ H.h = SSet.const x)
    (hJ : i ▷ Δ[1] ≫ J.h = SSet.const x)
    (G : SSet.Homotopy (H.h ≫ p) (J.h ≫ p))
    (gi : i ▷ Δ[1] ▷ Δ[1] ≫ G.h = SSet.const (p.app _ x))
    (g₀ : (SSet.ι₀ : A ⟶ A ⊗ Δ[1]) ▷ Δ[1] ≫ G.h = SSet.const (p.app _ x))
    (g₁ : (SSet.ι₁ : A ⟶ A ⊗ Δ[1]) ▷ Δ[1] ≫ G.h = SSet.const (p.app _ x)) :
    ∃ F : SSet.Homotopy a (SSet.const x),
      i ▷ Δ[1] ≫ F.h = SSet.const x ∧ F.h ≫ p = SSet.const (p.app _ x) := by
  let s := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet) i
    (SSet.stdSimplex.δ (n := 0) (0 : Fin 2))
  have hs : SSet.anodyneExtensions s.ι :=
    SSet.anodyneExtensions_pushoutObjObjι s (SimplicialCylinder.delta_one_anodyne 0)
  have htop {b : A ⟶ K} (T : SSet.Homotopy b (SSet.const x))
      (hT : i ▷ Δ[1] ≫ T.h = SSet.const x) : s.ι ≫ T.h = SSet.const x := by
    apply s.isPushout.hom_ext
    · rw [← Category.assoc,s.inl_ι,SSet.comp_const]
      apply (cancel_epi (SimplicialCylinder.zeroFactorIso A).hom).mp
      change endpoint A 0 ≫ T.h = _
      rw [endpoint_one,T.h₁,SSet.comp_const]
    · rw [← Category.assoc,s.inr_ι]
      change i ▷ Δ[1] ≫ T.h = _
      rw [hT,SSet.comp_const]
  have hside : s.ι ▷ Δ[1] ≫ G.h = SSet.const (p.app _ x) := by
    apply (s.isPushout.map (tensorRight (Δ[1] : SSet.{u}))).hom_ext
    · change s.inl ▷ Δ[1] ≫ s.ι ▷ Δ[1] ≫ G.h = _
      rw [← comp_whiskerRight_assoc,s.inl_ι]
      apply (cancel_epi ((SimplicialCylinder.zeroFactorIso A).hom ▷ Δ[1])).mp
      rw [← comp_whiskerRight_assoc]
      change (endpoint A 0) ▷ Δ[1] ≫ G.h = _
      rw [endpoint_one,g₁,SSet.comp_const,SSet.comp_const]
    · change s.inr ▷ Δ[1] ≫ s.ι ▷ Δ[1] ≫ G.h = _
      rw [← comp_whiskerRight_assoc,s.inr_ι]
      change i ▷ Δ[1] ▷ Δ[1] ≫ G.h = _
      rw [gi,SSet.comp_const]
  obtain ⟨Q,hQ,hQ₀,hQ₁,hQp⟩ := cylinder_lift_ends s.ι hs p hp H.h J.h (SSet.const x) G.h
    (by rw [htop H hH,SSet.comp_const])
    (by rw [htop J hJ,SSet.comp_const]) G.h₀.symm G.h₁.symm
    (by rw [SSet.const_comp,hside])
  let F : SSet.Homotopy a (SSet.const x) := CoherentGluing.toHomotopy
    ((SSet.ι₀ : A ⟶ A ⊗ Δ[1]) ▷ Δ[1] ≫ Q)
    (by rw [SSet.ι₀_comp_assoc,hQ₀,H.h₀])
    (by rw [SSet.ι₁_comp_assoc,hQ₁,J.h₀])
  have hQi : i ▷ Δ[1] ▷ Δ[1] ≫ Q = SSet.const x := by
    have hi : s.inr ≫ s.ι = i ▷ Δ[1] := s.inr_ι
    rw [← hi,comp_whiskerRight_assoc,hQ,SSet.comp_const]
  refine ⟨F,?_,?_⟩
  · change i ▷ Δ[1] ≫ (SSet.ι₀ : A ⟶ A ⊗ Δ[1]) ▷ Δ[1] ≫ Q = _
    rw [← comp_whiskerRight_assoc,← SSet.ι₀_comp,comp_whiskerRight_assoc,hQi,SSet.comp_const]
  · change ((SSet.ι₀ : A ⟶ A ⊗ Δ[1]) ▷ Δ[1] ≫ Q) ≫ p = _
    rw [Category.assoc,hQp,g₀]
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal KanPath HornSubdivision Contiguity

lemma correct_box_nullhomotopy (I : Type u) [Fintype I] [LinearOrder I]
    {K L : SSet.{u}} [SSet.KanComplex K] [SSet.KanComplex L]
    (p : K ⟶ L) (hp : simplicialFibrations p) (hw : simplicialWeakEquivalences p)
    (x : K _⦋0⦌) {a : nerve (Finset I) ⟶ K}
    (ha : a ≫ p = SSet.const (p.app _ x))
    (H : SSet.Homotopy a (SSet.const x))
    (hH : (boxBoundary I).ι ▷ Δ[1] ≫ H.h = SSet.const x) :
    ∃ F : SSet.Homotopy a (SSet.const x),
      (boxBoundary I).ι ▷ Δ[1] ≫ F.h = SSet.const x ∧
      F.h ≫ p = SSet.const (p.app _ x) := by
  let : LinearOrder (Option I) := LinearOrder.lift' (Fintype.equivFin (Option I))
    (Fintype.equivFin (Option I)).injective
  have hb : (boxBoundary (Option I)).ι ≫ boxToPrism I ≫ H.h ≫ p = SSet.const (p.app _ x) :=
    boxPrism_boundary_const I (p.app _ x) (H.h ≫ p)
      (by rw [← Category.assoc,hH,SSet.const_comp])
      (by rw [← Category.assoc,H.h₀,ha])
      (by rw [← Category.assoc,H.h₁,SSet.const_comp])
  obtain ⟨b,hb,Gb⟩ := weak_box_surjective (Option I) (Fintype.card I)
    (Fintype.equivFinOfCardEq (by simp)) p hw x (boxToPrism I ≫ H.h ≫ p) hb
  have hm : (prismToBox I ≫ b) ≫ p = prismToBox I ≫ (b ≫ p) := Category.assoc _ _ _
  have hj₀ : SSet.ι₀ ≫ prismToBox I ≫ b = SSet.const x := by
    rw [← Category.assoc,← prismBoxEnd_zero_comp,Category.assoc,hb,SSet.comp_const]
  have hj₁ : SSet.ι₁ ≫ prismToBox I ≫ b = SSet.const x := by
    rw [← Category.assoc,← prismBoxEnd_one_comp,Category.assoc,hb,SSet.comp_const]
  let J : SSet.Homotopy (SSet.const (X := nerve (Finset I)) x) (SSet.const x) :=
    CoherentGluing.toHomotopy (prismToBox I ≫ b) hj₀ hj₁
  have hj : (boxBoundary I).ι ▷ Δ[1] ≫ J.h = SSet.const x := by
    change (boxBoundary I).ι ▷ Δ[1] ≫ prismToBox I ≫ b = _
    rw [← Category.assoc,← prismBoxSide_comp,Category.assoc,hb,SSet.comp_const]
  obtain ⟨G,hG⟩ := based_homotopy_symm (boxBoundary (Option I)).ι (SSet.const (p.app _ x)) Gb
  let G' : SSet.Homotopy (H.h ≫ p) (J.h ≫ p) := CoherentGluing.toHomotopy
    (prismToBox I ▷ Δ[1] ≫ G.h)
    (by rw [SSet.ι₀_comp_assoc,G.h₀,← Category.assoc];
        change ((boxPrismIso I).inv ≫ (boxPrismIso I).hom) ≫ _ = _;
        rw [Iso.inv_hom_id,Category.id_comp])
    (by rw [SSet.ι₁_comp_assoc,G.h₁]; rfl)
  have hg : (boxBoundary (Option I)).ι ▷ Δ[1] ≫ G.h = SSet.const (p.app _ x) := by
    simpa only [SSet.comp_const] using hG
  apply correct_nullhomotopy_to_fiber (boxBoundary I).ι p hp x H J hH hj G'
  · change (boxBoundary I).ι ▷ Δ[1] ▷ Δ[1] ≫ prismToBox I ▷ Δ[1] ≫ G.h = _
    rw [← comp_whiskerRight_assoc,← prismBoxSide_comp,comp_whiskerRight_assoc,hg,SSet.comp_const]
  · change SSet.ι₀ ▷ Δ[1] ≫ prismToBox I ▷ Δ[1] ≫ G.h = _
    rw [← comp_whiskerRight_assoc,← prismBoxEnd_zero_comp,comp_whiskerRight_assoc,hg,SSet.comp_const]
  · change SSet.ι₁ ▷ Δ[1] ≫ prismToBox I ▷ Δ[1] ≫ G.h = _
    rw [← comp_whiskerRight_assoc,← prismBoxEnd_one_comp,comp_whiskerRight_assoc,hg,SSet.comp_const]

lemma weak_fibration_box_nullhomotopy (I : Type u) [Fintype I] [LinearOrder I]
    (n : ℕ) (e : I ≃ Fin (n+1)) {K L : SSet.{u}} [SSet.KanComplex K] [SSet.KanComplex L]
    (p : K ⟶ L) (hp : simplicialFibrations p) (hw : simplicialWeakEquivalences p)
    (x : K _⦋0⦌) (a : nerve (Finset I) ⟶ K)
    (hab : (boxBoundary I).ι ≫ a = SSet.const x)
    (ha : a ≫ p = SSet.const (p.app _ x)) :
    ∃ F : SSet.Homotopy a (SSet.const x),
      (boxBoundary I).ι ▷ Δ[1] ≫ F.h = SSet.const x ∧
      F.h ≫ p = SSet.const (p.app _ x) := by
  have H : BasedHomotopy (boxBoundary I).ι (SSet.const (p.app _ x))
      (a ≫ p) (SSet.const x ≫ p) := by
    rw [ha,SSet.const_comp]
    exact based_homotopy_refl _ _ _ (SSet.comp_const _ _)
  obtain ⟨H,hH⟩ := weak_box_injective I n e p hw x a (SSet.const x) hab (SSet.comp_const _ _) H
  exact correct_box_nullhomotopy I p hp hw x ha H (by simpa only [SSet.comp_const] using hH)
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open SSet.modelCategoryQuillen
open LastVertexProof KanHomotopy KanLocal KanPath HornSubdivision Contiguity

def strictFiber {K L : SSet.{u}} (p : K ⟶ L) (y : L _⦋0⦌) : K.Subcomplex where
  obj n := {s | p.app n s = L.map (n.unop.const _ 0).op y}
  map {n m} θ s hs := by
    change p.app m (K.map θ s) = _
    rw [← CategoryTheory.comp_apply,p.naturality,CategoryTheory.comp_apply,hs,
      ← CategoryTheory.comp_apply,← L.map_comp]
    rfl

lemma strictFiber_ι_comp {K L : SSet.{u}} (p : K ⟶ L) (y : L _⦋0⦌) :
    (strictFiber p y).ι ≫ p = SSet.const y := by
  ext n s
  exact s.property

def strictFiberLift {A K L : SSet.{u}} (p : K ⟶ L) (y : L _⦋0⦌)
    (a : A ⟶ K) (ha : a ≫ p = SSet.const y) : A ⟶ (strictFiber p y : SSet) where
  app n := TypeCat.ofHom fun s => ⟨a.app n s,by
    change p.app n (a.app n s) = _
    exact congrArg (fun f : A ⟶ L => f.app n s) ha⟩
  naturality n m θ := by
    ext s
    apply Subtype.ext
    exact congrArg (fun f => f s) (a.naturality θ)

lemma strictFiberLift_ι {A K L : SSet.{u}} (p : K ⟶ L) (y : L _⦋0⦌)
    (a : A ⟶ K) (ha : a ≫ p = SSet.const y) :
    strictFiberLift p y a ha ≫ (strictFiber p y).ι = a := rfl

lemma strictFiber_kan {K L : SSet.{u}} (p : K ⟶ L) (hp : simplicialFibrations p)
    (y : L _⦋0⦌) : SSet.KanComplex (strictFiber p y : SSet) := by
  apply (HomotopicalAlgebra.isFibrant_iff _).mpr
  apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
  intro A B i hi
  constructor
  intro a b sq
  have := hp i hi
  let q : CommSq (a ≫ (strictFiber p y).ι) i p (SSet.const y) :=
    ⟨by rw [Category.assoc,strictFiber_ι_comp,SSet.comp_const,SSet.comp_const]⟩
  refine ⟨⟨{
    l := strictFiberLift p y q.lift q.fac_right
    fac_left := ?_
    fac_right := Subsingleton.elim _ _ }⟩⟩
  apply (cancel_mono (strictFiber p y).ι).mp
  rw [Category.assoc,strictFiberLift_ι,q.fac_left]

lemma strictFiber_homotopy {A K L : SSet.{u}} (p : K ⟶ L) (y : L _⦋0⦌)
    {a b : A ⟶ (strictFiber p y : SSet)}
    (H : SSet.Homotopy (a ≫ (strictFiber p y).ι) (b ≫ (strictFiber p y).ι))
    (hH : H.h ≫ p = SSet.const y) : Nonempty (SSet.Homotopy a b) := by
  refine ⟨CoherentGluing.toHomotopy (strictFiberLift p y H.h hH) ?_ ?_⟩
  · apply (cancel_mono (strictFiber p y).ι).mp
    rw [Category.assoc,strictFiberLift_ι,H.h₀]
  · apply (cancel_mono (strictFiber p y).ι).mp
    rw [Category.assoc,strictFiberLift_ι,H.h₁]
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal KanPath HornSubdivision Contiguity PolyPoint

lemma weak_fibration_vertex_homotopy {K L : SSet.{u}}
    [SSet.KanComplex K] [SSet.KanComplex L]
    (p : K ⟶ L) (hp : simplicialFibrations p) (hw : simplicialWeakEquivalences p)
    (x z : K _⦋0⦌) (hz : p.app _ z = p.app _ x) :
    ∃ F : SSet.Homotopy (SSet.const (X := Δ[0]) z) (SSet.const x),
      F.h ≫ p = SSet.const (p.app _ x) := by
  have hc : SSet.π₀.mk z = SSet.π₀.mk x := by
    apply (KanQuillen.map_components_bijective_of_weak p hw).1
    exact congrArg SSet.π₀.mk hz
  obtain ⟨H⟩ := homotopy_of_homotopic (component_homotopic_const hc)
  let I := ULift.{u} (Fin 0)
  let A := nerve (Finset I)
  let q : A ⟶ (Δ[0] : SSet.{u}) := SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0)
  let H' : SSet.Homotopy (SSet.const (X := A) z) (SSet.const x) :=
    homotopy_pre q H
  have hH : (boxBoundary I).ι ▷ Δ[1] ≫ H'.h = SSet.const x := by
    ext n st
    obtain ⟨i,hi⟩ := st.1.property
    exact Fin.elim0 i.down
  obtain ⟨F,hF,hFp⟩ := correct_box_nullhomotopy I p hp hw x
    (by rw [SSet.const_comp,hz]) H' hH
  let v : A _⦋0⦌ := (⟨fun _ : Fin 1 => (∅ : Finset I), fun _ _ _ => le_rfl⟩ : Fin 1 →o Finset I).toFunctor
  let j : (Δ[0] : SSet.{u}) ⟶ A := SSet.const v
  refine ⟨homotopy_pre j F,?_⟩
  change (j ▷ Δ[1] ≫ F.h) ≫ p = _
  rw [Category.assoc,hFp,SSet.comp_const]

lemma strictFiber_vertex_iff {K L : SSet.{u}} (p : K ⟶ L) (y : L _⦋0⦌)
    (x : K _⦋0⦌) : x ∈ (strictFiber p y).obj (op ⦋0⦌) ↔ p.app _ x = y := by
  have e : (⦋0⦌.const ⦋0⦌ 0) = 𝟙 _ := by
    ext i
    simp
  change (p.app _ x = L.map _ y) ↔ _
  rw [e]
  change (p.app _ x = L.map (𝟙 _) y) ↔ _
  rw [L.map_id]
  rfl

lemma strictFiber_vertex_homotopy {K L : SSet.{u}}
    [SSet.KanComplex K] [SSet.KanComplex L]
    (p : K ⟶ L) (hp : simplicialFibrations p) (hw : simplicialWeakEquivalences p)
    (y : L _⦋0⦌) (x z : (strictFiber p y : SSet) _⦋0⦌) :
    Nonempty (SSet.Homotopy (SSet.const (X := Δ[0]) z) (SSet.const x)) := by
  have hx : p.app _ x.val = y := (strictFiber_vertex_iff p y x.val).mp x.property
  have hz : p.app _ z.val = y := (strictFiber_vertex_iff p y z.val).mp z.property
  obtain ⟨H,hH⟩ := weak_fibration_vertex_homotopy p hp hw x.val z.val (hz.trans hx.symm)
  let H' : SSet.Homotopy (SSet.const (X := Δ[0]) z ≫ (strictFiber p y).ι)
      (SSet.const x ≫ (strictFiber p y).ι) :=
    CoherentGluing.toHomotopy H.h (by rw [SSet.const_comp]; exact H.h₀)
      (by rw [SSet.const_comp]; exact H.h₁)
  exact strictFiber_homotopy p y H' (by simpa only [H',CoherentGluing.toHomotopy,hx] using hH)
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory
open scoped Topology Topology.Homotopy

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal Subdivision Contiguity PolyPoint Mesh Approximation

lemma cubical_null_of_group_subsingleton (P B : PartOrd.{u}) [Finite P] [Finite B]
    (i : B →o P) (hi : Function.Injective i) (n : ℕ) (c : CubicalPair P B i n)
    {K : SSet.{u}} [SSet.KanComplex K] (x : K _⦋0⦌)
    [Subsingleton (HomotopyGroup (Fin (n+1)) (SSet.toTop.obj K) (KanQuillen.realVertex x))]
    (a : nerve P ⟶ K) (ha : nerveMap i.toFunctor ≫ a = SSet.const x) :
    BasedHomotopy (nerveMap i.toFunctor) (SSet.const x) a (SSet.const x) := by
  let loop (a : nerve P ⟶ K) (ha : nerveMap i.toFunctor ≫ a = SSet.const x) :
      GenLoop (Fin (n+1)) (SSet.toTop.obj K) (KanQuillen.realVertex x) :=
    ⟨(polyRealize a).comp ⟨c.home.symm,c.home.symm.continuous⟩,by
      intro y hy
      exact poly_realize_boundary i x a ha _ ((c.boundary _).mpr (by simpa using hy))⟩
  have he : (⟦loop a ha⟧ : HomotopyGroup (Fin (n+1)) (SSet.toTop.obj K) (KanQuillen.realVertex x)) =
      ⟦loop (SSet.const x) (SSet.comp_const _ _)⟧ :=
    @Subsingleton.elim (HomotopyGroup (Fin (n+1)) (SSet.toTop.obj K) (KanQuillen.realVertex x))
      inferInstance _ _
  obtain ⟨G⟩ : GenLoop.Homotopic (loop a ha) (loop (SSet.const x) (SSet.comp_const _ _)) :=
    Quotient.exact he
  have H := top_homotopy_rel_pre G ⟨c.home,c.home.continuous⟩ _
    (fun y hy => (c.boundary y).mp hy)
  have H' : (polyRealize a).HomotopyRel (polyRealize (SSet.const x))
      (Set.range (map i (preservesChains_monotone i))) :=
    H.cast (by ext y; simp [loop]) (by ext y; simp [loop])
  exact finite_cubical_realization_faithful P B i hi n c x a (SSet.const x)
    ha (SSet.comp_const _ _) H'

lemma cube_classes_subsingleton_of_boxes {K : SSet.{u}} [SSet.KanComplex K]
    (n : ℕ) (x : K _⦋0⦌)
    (h : ∀ a : nerve (Finset (ULift.{u} (Fin (n+1)))) ⟶ K,
      (boxBoundary (ULift.{u} (Fin (n+1)))).ι ≫ a = SSet.const x →
      BasedHomotopy (boxBoundary (ULift.{u} (Fin (n+1)))).ι (SSet.const x) a (SSet.const x)) :
    Subsingleton (CubeClasses n x) := by
  let I := ULift.{u} (Fin (n+1))
  let f := boxPairProjection I
  let g := boxBoundaryProjection I
  let j := nerveMap (cubeBoundaryInclusion.{u} n).toFunctor
  have hc (a : CubeMap n x) : BasedHomotopy j (SSet.const x) a.val (SSet.const x) := by
    obtain ⟨b,G,hb,hG⟩ := pair_local_surjective_plain (boxBoundary I).ι j f g
      (box_pair_square I) (boxPairProjection_local I) (boxBoundaryProjection_local I)
      (SSet.const x) a.val (by simpa only [SSet.comp_const] using a.property)
    have H := based_homotopy_pre (boxBoundary I).ι j f g (box_pair_square I) (SSet.const x) (h b hb)
    have H' : BasedHomotopy j (SSet.const x) (f ≫ b) (SSet.const x) := by
      simpa only [SSet.comp_const] using H
    exact based_homotopy_trans j (SSet.const x)
      (based_homotopy_symm j (SSet.const x) ⟨G,by simpa only [SSet.comp_const] using hG⟩) H'
  constructor
  intro a b
  obtain ⟨a,rfl⟩ := Quotient.mk_surjective a
  obtain ⟨b,rfl⟩ := Quotient.mk_surjective b
  exact Quotient.sound (based_homotopy_trans j (SSet.const x) (hc a)
    (based_homotopy_symm j (SSet.const x) (hc b)))

theorem terminal_rlp_of_nullboxes {K : SSet.{u}} [SSet.KanComplex K]
    (x₀ : K _⦋0⦌)
    (h₀ : ∀ x y : K _⦋0⦌, Nonempty (SSet.Homotopy (SSet.const (X := Δ[0]) x) (SSet.const y)))
    (h : ∀ (n : ℕ) (x : K _⦋0⦌) (a : nerve (Finset (ULift.{u} (Fin (n+1)))) ⟶ K),
      (boxBoundary (ULift.{u} (Fin (n+1)))).ι ≫ a = SSet.const x →
      BasedHomotopy (boxBoundary (ULift.{u} (Fin (n+1)))).ι (SSet.const x) a (SSet.const x)) :
    SSet.modelCategoryQuillen.I.rlp (terminal.from K) := by
  apply terminal_rlp_of_nullsimplices x₀
  intro n x a ha
  cases n with
  | zero =>
    obtain ⟨H⟩ := h₀ (SSet.yonedaEquiv a) x
    have H' : SSet.Homotopy a (SSet.const x) := by
      simpa only [← SSet.yonedaEquiv_symm_zero,Equiv.symm_apply_apply] using H
    exact based_homotopy_zero x H'
  | succ n =>
    let := cube_classes_subsingleton_of_boxes n x (h n x)
    let : Subsingleton (HomotopyGroup (Fin (n+1)) (SSet.toTop.obj K) (KanQuillen.realVertex x)) :=
      Function.Surjective.subsingleton (positive_realization_comparison n x).2
    let f := simplexPairProjection.{u} (n+1)
    let g := simplexBoundaryProjection.{u} (n+1)
    let j := nerveMap (inclusion (simplexBoundary.{u} (n+1))).toFunctor
    have ha' : j ≫ f ≫ a = SSet.const x := by
      rw [← Category.assoc,simplex_pair_square,Category.assoc,ha,SSet.comp_const]
    obtain ⟨G,hG⟩ := cubical_null_of_group_subsingleton (simplexPoset (n+1))
      (PartOrd.of (simplexBoundary (n+1))) (inclusion (simplexBoundary (n+1)))
      Subtype.val_injective n (simplexCubicalPair n) x (f ≫ a) ha'
    let G' : SSet.Homotopy (f ≫ a) (f ≫ SSet.const x) :=
      CoherentGluing.toHomotopy G.h G.h₀ (by simpa only [SSet.comp_const] using G.h₁)
    exact pair_local_injective_plain _ j f g (simplex_pair_square _)
      (simplexPairProjection_local _) (simplexBoundaryProjection_local _) _ a (SSet.const x)
      ha (SSet.comp_const _ _) G' (by simpa only [G',CoherentGluing.toHomotopy,SSet.comp_const] using hG)
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal KanPath HornSubdivision Contiguity

lemma strictFiber_based_box_null {K L : SSet.{u}}
    [SSet.KanComplex K] [SSet.KanComplex L]
    (p : K ⟶ L) (hp : simplicialFibrations p) (hw : simplicialWeakEquivalences p)
    (y : L _⦋0⦌) (n : ℕ) (x : (strictFiber p y : SSet) _⦋0⦌)
    (a : nerve (Finset (ULift.{u} (Fin (n+1)))) ⟶ (strictFiber p y : SSet))
    (ha : (boxBoundary (ULift.{u} (Fin (n+1)))).ι ≫ a = SSet.const x) :
    BasedHomotopy (boxBoundary (ULift.{u} (Fin (n+1)))).ι (SSet.const x) a (SSet.const x) := by
  have hx : p.app _ x.val = y := (strictFiber_vertex_iff p y x.val).mp x.property
  obtain ⟨H,hH,hHp⟩ := weak_fibration_box_nullhomotopy (ULift.{u} (Fin (n+1)))
    n Equiv.ulift p hp hw x.val (a ≫ (strictFiber p y).ι)
    (by rw [← Category.assoc,ha,SSet.const_comp]; rfl)
    (by rw [Category.assoc,strictFiber_ι_comp,SSet.comp_const,hx])
  let H' : SSet.Homotopy a (SSet.const x) := CoherentGluing.toHomotopy
    (strictFiberLift p y H.h (by simpa only [hx] using hHp))
    (by apply (cancel_mono (strictFiber p y).ι).mp
        rw [Category.assoc,strictFiberLift_ι,H.h₀])
    (by apply (cancel_mono (strictFiber p y).ι).mp
        rw [Category.assoc,strictFiberLift_ι,H.h₁,SSet.const_comp]; rfl)
  refine ⟨H',?_⟩
  apply (cancel_mono (strictFiber p y).ι).mp
  change (_ ≫ strictFiberLift p y H.h (by simpa only [hx] using hHp)) ≫ (strictFiber p y).ι = _
  rw [Category.assoc,strictFiberLift_ι,hH,SSet.comp_const,SSet.const_comp]
  rfl

theorem weak_kan_fibration_fiber_rlp {K L : SSet.{u}}
    [SSet.KanComplex K] [SSet.KanComplex L]
    (p : K ⟶ L) (hp : simplicialFibrations p) (hw : simplicialWeakEquivalences p)
    (y : L _⦋0⦌) : SSet.modelCategoryQuillen.I.rlp (terminal.from (strictFiber p y : SSet)) := by
  let := strictFiber_kan p hp y
  obtain ⟨x,hx⟩ := KanQuillen.weak_fibration_surjective_vertices p hp hw y
  have hx' : x ∈ (strictFiber p y).obj (op ⦋0⦌) := (strictFiber_vertex_iff p y x).mpr hx
  apply terminal_rlp_of_nullboxes (K := (strictFiber p y : SSet)) ⟨x,hx'⟩
  · intro a b
    exact strictFiber_vertex_homotopy p hp hw y b a
  · intro n a b hb
    exact strictFiber_based_box_null p hp hw y n a b hb
end Thomason.GeometricRecognition

end

noncomputable section
universe u v w z
open CategoryTheory Limits Simplicial Opposite PartialOrder MonoidalCategory CartesianMonoidalCategory

namespace Thomason.GeometricRecognition
open LastVertexProof KanHomotopy KanLocal KanPath HornSubdivision Contiguity

private def simplexConeOrder {n m : ℕ} (s : Fin (m+1) →o Fin (n+1))
    (t : Fin (m+1) →o Fin 2) : Fin (m+1) →o Fin (n+1) where
  toFun j := if t j = 0 then 0 else s j
  monotone' := by
    intro i j h
    have ht := t.monotone h
    dsimp only
    split_ifs with hi hj hj
    · exact le_rfl
    · exact Fin.zero_le _
    · exact False.elim (hi (le_antisymm (hj ▸ ht) (Fin.zero_le _)))
    · exact s.monotone h

def simplexCone (n : ℕ) : (Δ[n] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[n] where
  app m := TypeCat.ofHom fun s => SSet.stdSimplex.objMk
    (simplexConeOrder (SSet.stdSimplex.asOrderHom s.1) (SSet.stdSimplex.asOrderHom s.2))
  naturality m k θ := by
    ext s
    rfl

lemma simplexCone_zero (n : ℕ) :
    SSet.ι₀ ≫ simplexCone.{u} n = SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0) := by
  ext m s
  apply SSet.stdSimplex.ext
  intro j
  rfl
lemma simplexCone_one (n : ℕ) : SSet.ι₁ ≫ simplexCone.{u} n = 𝟙 _ := by
  ext m s
  apply SSet.stdSimplex.ext
  intro j
  rfl

theorem fibration_rlp_of_fibers {K L : SSet.{u}} (p : K ⟶ L)
    (hp : simplicialFibrations p)
    (hf : ∀ y : L _⦋0⦌, SSet.modelCategoryQuillen.I.rlp
      (terminal.from (strictFiber p y : SSet))) : SSet.modelCategoryQuillen.I.rlp p := by
  rintro _ _ _ ⟨n⟩
  constructor
  intro a b sq
  let i := (SSet.boundary n).ι
  let C := simplexCone.{u} n ≫ b
  let y := b.app _ (SSet.stdSimplex.obj₀Equiv.symm 0)
  have hc₀ : SSet.ι₀ ≫ C = SSet.const y := by
    rw [← Category.assoc,simplexCone_zero,SSet.const_comp]
  have hc₁ : SSet.ι₁ ≫ C = b := by rw [← Category.assoc,simplexCone_one,Category.id_comp]
  have : HasLiftingProperty (SSet.ι₁ (X := (SSet.boundary n : SSet))) p :=
    (SimplicialCylinder.endpoint_anodyne (SSet.boundary n : SSet)).2 p hp
  let q : CommSq a SSet.ι₁ p (i ▷ Δ[1] ≫ C) :=
    ⟨by rw [SSet.ι₁_comp_assoc,hc₁]; exact sq.w⟩
  let a₀ := SSet.ι₀ ≫ q.lift
  have ha₀ : a₀ ≫ p = SSet.const y := by
    dsimp only [a₀]
    rw [Category.assoc,q.fac_right,SSet.ι₀_comp_assoc,hc₀,SSet.comp_const]
  let af := strictFiberLift p y a₀ ha₀
  have := hf y _ ⟨n⟩
  let r : CommSq af i (terminal.from (strictFiber p y : SSet)) (terminal.from _) :=
    ⟨Subsingleton.elim _ _⟩
  let l := r.lift ≫ (strictFiber p y).ι
  have hl : i ≫ l = a₀ := by rw [← Category.assoc,r.fac_left,strictFiberLift_ι]
  have hlp : l ≫ p = SSet.const y := by rw [Category.assoc,strictFiber_ι_comp,SSet.comp_const]
  obtain ⟨Q,hQ,hQ₀,hQp⟩ := cylinder_lift i p hp 1 l q.lift C
    (by rw [endpoint_zero,hl])
    (by rw [endpoint_zero,hc₀,hlp]) q.fac_right
  refine ⟨⟨{l := SSet.ι₁ ≫ Q, fac_left := ?_,fac_right := ?_}⟩⟩
  · rw [← SSet.ι₁_comp_assoc,hQ,q.fac_left]
  · rw [Category.assoc,hQp,hc₁]
end Thomason.GeometricRecognition

end

end OAI
