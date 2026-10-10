import OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCech
import OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyPencil

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry.BaseSections

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial
variable {K : Type} [Field K] {U V W : Scheme.{0}} [IsAffine U] [IsAffine V]

theorem two_chart_intersection_finite
    (kU : K →+* Γ(U,⊤)) (kV : K →+* Γ(V,⊤)) (kW : K →+* Γ(W,⊤))
    (a : W ⟶ U) (b : W ⟶ V) [IsOpenImmersion a] [IsOpenImmersion b]
    (hka : a.appTop.hom.comp kU = kW) (hkb : b.appTop.hom.comp kV = kW)
    (u : Γ(U,⊤)) (v : Γ(V,⊤))
    (ha : a.opensRange = U.basicOpen u) (_hb : b.opensRange = V.basicOpen v)
    (huv : a.appTop u * b.appTop v = 1)
    (hu : (Polynomial.eval₂RingHom kU u).Finite)
    (hv : (Polynomial.eval₂RingHom kV v).Finite)
    (L : LineBundle U) (P : LineBundle V) (N : W.Modules)
    (e : L.sheaf.restrict a ≅ N) (d : P.sheaf.restrict b ≅ N) :
    Module.Finite K ↥((chartMap kU kW a hka L.sheaf e).range ⊓
        (chartMap kV kW b hkb P.sheaf d).range) := by
  let := polynomialModule kU u L.sheaf ⊤
  let := polynomialModule kV v P.sheaf ⊤
  let := polynomialModule kW (a.appTop u) N ⊤
  let := polynomialTower kU u L.sheaf ⊤
  let := polynomialTower kV v P.sheaf ⊤
  let := polynomialTower kW (a.appTop u) N ⊤
  let : Module.Finite K[X] (Sections kU L.sheaf ⊤) := polynomial_finite kU u L hu
  let : Module.Finite K[X] (Sections kV P.sheaf ⊤) := polynomial_finite kV v P hv
  let F := chartPolynomialMap kU kW a hka L.sheaf e u
  let G := chartMap kV kW b hkb P.sheaf d
  let : IsLocalizedModule.Away (Polynomial.X : K[X]) F :=
    chartPolynomialMap_localize kU kW a hka L.sheaf e u ha
  have hInv (y : Sections kV P.sheaf ⊤) :
      (Polynomial.X : K[X]) • G ((Polynomial.X : K[X]) • y) = G y := by
    change (Polynomial.eval₂RingHom kW (a.appTop u)) Polynomial.X •
      G ((Polynomial.eval₂RingHom kV v) Polynomial.X • y) = G y
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    rw [chartMap_smul, ← mul_smul, huv, one_smul]
  exact LaurentCech.intersection_finite F G hInv
end

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Projective PiExponentSeshadri.Frames
variable {K : Type} [Field K] {X : Scheme.{0}}

def twoBaseIntersection (k : K →+* Γ(X,⊤)) (M : X.Modules) (U V : X.Opens) :
    Submodule K (Sections k M (U ⊓ V)) :=
  (res k M (show U ⊓ V ≤ U from inf_le_left)).range ⊓
    (res k M (show U ⊓ V ≤ V from inf_le_right)).range

theorem finite_pencil_intersection (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Bool → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (L : LineBundle X) :
    let U := SectionOpens.isoOpen (s false)
    let V := SectionOpens.isoOpen (s true)
    Module.Finite K ↥(twoBaseIntersection k L.sheaf U V) := by
  intro U V
  let W := U ⊓ V
  let a := X.homOfLE (show W ≤ U from inf_le_left)
  let b := X.homOfLE (show W ≤ V from inf_le_right)
  let kU := U.ι.appTop.hom.comp k
  let kV := V.ι.appTop.hom.comp k
  let kW := W.ι.appTop.hom.comp k
  let u := coefficient (sectionFrame (s false)) (restrictSection U.ι (s true))
  let v := coefficient (sectionFrame (s true)) (restrictSection V.ι (s false))
  obtain ⟨hU,hu⟩ := finite_pencil_chart k s hs false
  obtain ⟨hV,hv⟩ := finite_pencil_chart k s hs true
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  have ha : a.opensRange = U.toScheme.basicOpen u := by
    rw [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf]
    simp only [Scheme.Opens.ι_preimage_self, top_inf_eq]
    exact pencil_overlap_basic s false
  have hb : b.opensRange = V.toScheme.basicOpen v := by
    rw [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf]
    simp only [Scheme.Opens.ι_preimage_self, inf_top_eq]
    exact pencil_overlap_basic s true
  let e := nestedRestriction L.sheaf (show W ≤ U from inf_le_left)
  let d := nestedRestriction L.sheaf (show W ≤ V from inf_le_right)
  let F := chartMap kU kW a (nestedBase k inf_le_left) (L.restrict U.ι).sheaf e
  let G := chartMap kV kW b (nestedBase k inf_le_right) (L.restrict V.ι).sheaf d
  let : Module.Finite K ↥(F.range ⊓ G.range) :=
    two_chart_intersection_finite kU kV kW a b (nestedBase k inf_le_left)
      (nestedBase k inf_le_right) u v ha hb (pencil_overlap_reciprocal s) hu hv
      (L.restrict U.ι) (L.restrict V.ι) (L.sheaf.restrict W.ι) e d
  let E := chartTop k L.sheaf W
  have he : (F.range ⊓ G.range).map E.toLinearMap = twoBaseIntersection k L.sheaf U V := by
    rw [Submodule.map_inf E.toLinearMap E.injective]
    exact congrArg₂ (· ⊓ ·) (chartMap_range_coherent k L.sheaf inf_le_left)
      (chartMap_range_coherent k L.sheaf inf_le_right)
  let : Module.Finite K ↥((F.range ⊓ G.range).map E.toLinearMap) :=
    Module.Finite.equiv (E.submoduleMap (F.range ⊓ G.range))
  rw [← he]
  infer_instance
end PiExponentSeshadri.Geometry.BaseSections

namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Abelian
open PiExponentSeshadri.Projective PiExponentSeshadri.Frames BaseSections
variable {K : Type} [Field K] {X : Scheme.{0}}

lemma BaseSections.res_comp (k : K →+* Γ(X,⊤)) (M : X.Modules)
    {U V W : X.Opens} (h : U ≤ V) (g : V ≤ W) (m : Sections k M W) :
    res k M h (res k M g m) = res k M (h.trans g) m := by
  change M.presheaf.map (homOfLE h).op (M.presheaf.map (homOfLE g).op m) = _
  exact (congrArg (fun f : M.presheaf.obj (op W) ⟶ M.presheaf.obj (op U) => f m)
    (M.presheaf.map_comp (homOfLE g).op (homOfLE h).op)).symm

def BaseSections.globalIntersection [IsIntegral X] (k : K →+* Γ(X,⊤))
    (L : LineBundle X) (U V : X.Opens) :
    Sections k L.sheaf ⊤ →ₗ[K] ↥(twoBaseIntersection k L.sheaf U V) :=
  (res k L.sheaf (show U ⊓ V ≤ ⊤ from le_top)).codRestrict _ (by
    intro m
    exact ⟨⟨res k L.sheaf (show U ≤ ⊤ from le_top) m,
      res_comp k L.sheaf inf_le_left le_top m⟩,
      ⟨res k L.sheaf (show V ≤ ⊤ from le_top) m,
      res_comp k L.sheaf inf_le_right le_top m⟩⟩)

lemma BaseSections.globalIntersection_injective [IsIntegral X] (k : K →+* Γ(X,⊤))
    (L : LineBundle X) (U V : X.Opens) [Nonempty (U ⊓ V : X.Opens)] :
    Function.Injective (globalIntersection k L U V) := by
  intro a b h
  exact L.restriction_injective (homOfLE (show U ⊓ V ≤ ⊤ from le_top))
    (congrArg Subtype.val h)

def BaseSections.globalSectionsLinear (M : X.Modules) :
    GlobalSections X M ≃ₗ[Γ(X,⊤)] Γ(M,⊤) where
  toEquiv := FlasqueCohomology.globalHomEquiv X.ringCatSheaf M
  map_add' := by intro f g; rfl
  map_smul' := by
    intro r f
    change restrictScalar X ⊤ r • f.app ⊤ (1 : Γ(X,⊤)) = r • f.app ⊤ (1 : Γ(X,⊤))
    congr 1
    change (X.presheaf.map (𝟙 (op ⊤))) r = r
    rw [X.presheaf.map_id]
    rfl

def BaseSections.cohomologyZero (k : K →+* Γ(X,⊤)) (M : X.Modules) :
    letI := Module.compHom (cohomology M 0) k
    cohomology M 0 ≃ₗ[K] Sections k M ⊤ := by
  letI := Module.compHom (cohomology M 0) k
  let e := (Ext.linearEquiv₀ (R := Γ(X,⊤)) (X := structureSheaf X) (Y := M)).trans
    (globalSectionsLinear M)
  refine { toFun := e
           invFun := e.symm
           left_inv := e.left_inv
           right_inv := e.right_inv
           map_add' := e.map_add
           map_smul' := ?_ }
  intro r m
  change e (k r • m) = restrictScalar X ⊤ (k r) • e m
  rw [e.map_smul]
  congr 1
  change k r = X.presheaf.map (𝟙 (op ⊤)) (k r)
  rw [X.presheaf.map_id]
  rfl

theorem finite_pencil_H0_finite [IsIntegral X]
    (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Bool → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (hn : ¬ IsAffine X) (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 0) k
    Module.Finite K (cohomology L.sheaf 0) := by
  let U := SectionOpens.isoOpen (s false)
  let V := SectionOpens.isoOpen (s true)
  obtain ⟨hU,_⟩ := finite_pencil_chart k s hs false
  obtain ⟨hV,_⟩ := finite_pencil_chart k s hs true
  have hc : U ⊔ V = ⊤ := by
    apply top_unique
    intro x hx
    have : x ∈ ⨆ i, SectionOpens.isoOpen (s i) := hs ▸ hx
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp this
    cases i with
    | false => exact Or.inl hi
    | true => exact Or.inr hi
  have hneU : (U : Set X).Nonempty := by
    by_contra h
    have he : U = ⊥ := by ext x; simp [Set.not_nonempty_iff_eq_empty.mp h]
    rw [he, bot_sup_eq] at hc
    have : IsAffine (⊤ : X.Opens).toScheme := hc ▸ hV
    exact hn (.of_isIso X.topIso.inv)
  have hneV : (V : Set X).Nonempty := by
    by_contra h
    have he : V = ⊥ := by ext x; simp [Set.not_nonempty_iff_eq_empty.mp h]
    rw [he, sup_bot_eq] at hc
    have : IsAffine (⊤ : X.Opens).toScheme := hc ▸ hU
    exact hn (.of_isIso X.topIso.inv)
  obtain ⟨x,hxU,hxV⟩ := nonempty_preirreducible_inter U.isOpen V.isOpen hneU hneV
  let : Nonempty (U ⊓ V : X.Opens) := ⟨⟨x,hxU,hxV⟩⟩
  let := finite_pencil_intersection k s hs L
  let : Module.Finite K (Sections k L.sheaf ⊤) := Module.Finite.of_injective
    (globalIntersection k L U V) (globalIntersection_injective k L U V)
  let := Module.compHom (cohomology L.sheaf 0) k
  exact Module.Finite.equiv (cohomologyZero k L.sheaf).symm

end PiExponentSeshadri.Geometry

namespace PiExponentSeshadri.Geometry.BaseSections
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Projective PiExponentSeshadri.Frames
variable {K : Type} [Field K] {X : Scheme.{0}}

theorem finite_pencil_cokernel (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Bool → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (L : LineBundle X) :
    let U := SectionOpens.isoOpen (s false)
    let V := SectionOpens.isoOpen (s true)
    Module.Finite K (Sections k L.sheaf (U ⊓ V) ⧸ twoBaseImage k L.sheaf U V) := by
  intro U V
  let W := U ⊓ V
  let a := X.homOfLE (show W ≤ U from inf_le_left)
  let b := X.homOfLE (show W ≤ V from inf_le_right)
  let kU := U.ι.appTop.hom.comp k
  let kV := V.ι.appTop.hom.comp k
  let kW := W.ι.appTop.hom.comp k
  let u := coefficient (sectionFrame (s false)) (restrictSection U.ι (s true))
  let v := coefficient (sectionFrame (s true)) (restrictSection V.ι (s false))
  obtain ⟨hU,hu⟩ := finite_pencil_chart k s hs false
  obtain ⟨hV,hv⟩ := finite_pencil_chart k s hs true
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  have ha : a.opensRange = U.toScheme.basicOpen u := by
    rw [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf]
    simp only [Scheme.Opens.ι_preimage_self, top_inf_eq]
    exact pencil_overlap_basic s false
  have hb : b.opensRange = V.toScheme.basicOpen v := by
    rw [Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf]
    simp only [Scheme.Opens.ι_preimage_self, inf_top_eq]
    exact pencil_overlap_basic s true
  let e := nestedRestriction L.sheaf (show W ≤ U from inf_le_left)
  let d := nestedRestriction L.sheaf (show W ≤ V from inf_le_right)
  let F := chartMap kU kW a (nestedBase k inf_le_left) (L.restrict U.ι).sheaf e
  let G := chartMap kV kW b (nestedBase k inf_le_right) (L.restrict V.ι).sheaf d
  let : Module.Finite K (Sections kW (L.sheaf.restrict W.ι) ⊤ ⧸ (F.range ⊔ G.range)) :=
    two_chart_cokernel_finite kU kV kW a b (nestedBase k inf_le_left)
      (nestedBase k inf_le_right) u v ha hb (pencil_overlap_reciprocal s) hu
      (L.restrict U.ι) (L.restrict V.ι) (L.sheaf.restrict W.ι) e d
  let E := chartTop k L.sheaf W
  have he : (F.range ⊔ G.range).map E.toLinearMap = twoBaseImage k L.sheaf U V := by
    rw [Submodule.map_sup]
    exact congrArg₂ (· ⊔ ·) (chartMap_range_coherent k L.sheaf inf_le_left)
      (chartMap_range_coherent k L.sheaf inf_le_right)
  let q := Submodule.Quotient.equiv (F.range ⊔ G.range)
    (twoBaseImage k L.sheaf U V) E he
  exact Module.Finite.of_surjective q.toLinearMap q.surjective
end PiExponentSeshadri.Geometry.BaseSections

namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Projective PiExponentSeshadri.Frames BaseSections
variable {K : Type} [Field K] {X : Scheme.{0}} [IsNoetherian X]

theorem finite_pencil_H1_finite (k : K →+* Γ(X,⊤)) {M : X.Modules}
    (s : Bool → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsFinite (sectionsMorphism k s hs)] (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 1) k
    Module.Finite K (cohomology L.sheaf 1) := by
  let U := SectionOpens.isoOpen (s false)
  let V := SectionOpens.isoOpen (s true)
  obtain ⟨hU,_⟩ := finite_pencil_chart k s hs false
  obtain ⟨hV,_⟩ := finite_pencil_chart k s hs true
  have hc : U ⊔ V = ⊤ := by
    apply top_unique
    intro x hx
    have : x ∈ ⨆ i, SectionOpens.isoOpen (s i) := hs ▸ hx
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp this
    cases i with
    | false => exact Or.inl hi
    | true => exact Or.inr hi
  let := Module.compHom (cohomology L.sheaf 1) k
  let := finite_pencil_cokernel k s hs L
  let e := twoBaseCohomologyOne k L.sheaf U V hU hV hc
  exact Module.Finite.of_surjective e.toLinearMap e.surjective

end PiExponentSeshadri.Geometry

end

end OAI
