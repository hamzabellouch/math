import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.CurveProjection
import OAI.AlgebraicGeometry.Seshadri.Cohomology.AffineVanishing
import OAI.AlgebraicGeometry.Seshadri.Intersection.PencilIntersection

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite Abelian
open MaximalSeshadri.Projective MaximalSeshadri.Frames BaseSections

variable {K : Type} [Field K] {X : Scheme.{0}}

lemma BaseSections.res_comp (k : K →+* Γ(X,⊤)) (M : X.Modules)
    {U V W : X.Opens} (h : U ≤ V) (g : V ≤ W) (m : Sections k M W) :
    res k M h (res k M g m) = res k M (h.trans g) m := by
  exact congrArg (fun morphism : M.presheaf.obj (op W) ⟶ M.presheaf.obj (op U) =>
    morphism m) (M.presheaf.map_comp (homOfLE g).op (homOfLE h).op).symm

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

theorem projective_curve_H0_finite {σ : Type} [Fintype σ] [Infinite K]
    [IsIntegral X] [IsNoetherian X] (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p]
    (hd : topologicalKrullDim X = 1) {M : X.Modules}
    (s : σ → (O X ⟶ M)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) s hs)]
    (L : LineBundle X) :
    letI := Module.compHom (cohomology L.sheaf 0)
      (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
    Module.Finite K (cohomology L.sheaf 0) := by
  obtain ⟨t,ht,hf⟩ := projective_curve_finite_pencil p hd s hs
  let := hf
  apply finite_pencil_H0_finite _ t ht ?_ L
  intro h
  let : IsAffine X := h
  have hh := proper_affine_dimension_zero p
  rw [hd] at hh
  norm_num at hh
end
end MaximalSeshadri.Geometry
end


end
end

end OAI
