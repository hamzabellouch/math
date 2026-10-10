import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Divisors.PrincipalSectionIdeal
import OAI.AlgebraicGeometry.Seshadri.Geometry.GeometricDivision
import OAI.AlgebraicGeometry.Seshadri.Sheaves.CartierTensor

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace MonoidalCategory
open MaximalSeshadri.Frames MaximalSeshadri.Projective

variable {X : Scheme.{0}}

def frameOnSmaller {M : X.Modules} {U : X.Opens} (e : M.restrict U.ι ≅ O U.toScheme)
    (V : X.Opens) (h : V ≤ U) : M.restrict V.ι ≅ O V.toScheme :=
  (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h).symm).app M ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M ≪≫
      restrictFrame (X.homOfLE h) e

lemma common_affine_frames (L M : LineBundle X) (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧
      Nonempty (L.sheaf.restrict U.1.ι ≅ O U.1.toScheme) ∧
      Nonempty (M.sheaf.restrict U.1.ι ≅ O U.1.toScheme) := by
  obtain ⟨A,hA,⟨e⟩⟩ := L.locallyRankOne x
  obtain ⟨B,hB,⟨f⟩⟩ := M.locallyRankOne x
  obtain ⟨_,⟨U,hUa,rfl⟩,hx,hU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ A ⊓ B from ⟨hA,hB⟩)
      (A ⊓ B).isOpen
  exact ⟨⟨U,hUa⟩,hx,⟨frameOnSmaller e U (fun _ hy => (hU hy).1)⟩,
    ⟨frameOnSmaller f U (fun _ hy => (hU hy).2)⟩⟩

def LineBundle.tensor (L M : LineBundle X) : LineBundle X where
  sheaf := moduleTensor X L.sheaf M.sheaf
  locallyRankOne x := by
    obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames L M x
    exact ⟨U.1,hx,⟨moduleTensorRestrict U.1 L.sheaf M.sheaf ≪≫
      moduleTensorIso e f ≪≫ moduleTensorUnit (O U.1.toScheme)⟩⟩

lemma sectionMultiply_eq (L M : LineBundle X) (s : O X ⟶ L.sheaf) :
    sectionMultiply L M s = (moduleTensorUnit M.sheaf).inv ≫
      moduleTensorMap s (𝟙 M.sheaf) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  let sheafification : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let counit : sheafification.obj M.sheaf.val ≅ M.sheaf :=
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit).app M.sheaf
  change counit.inv ≫ sheafification.map
      ((λ_ M.sheaf.val).inv ≫ (s.val ⊗ₘ 𝟙 M.sheaf.val)) =
    (counit.inv ≫ sheafification.map (λ_ M.sheaf.val).inv) ≫
      sheafification.map (s.val ⊗ₘ 𝟙 M.sheaf.val)
  rw [sheafification.map_comp, Category.assoc]

def tensorFrame (L M : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme)
    (f : M.sheaf.restrict U.ι ≅ O U.toScheme) :
    (L.tensor M).sheaf.restrict U.ι ≅ O U.toScheme :=
  moduleTensorRestrict U L.sheaf M.sheaf ≪≫ moduleTensorIso e f ≪≫
    moduleTensorUnit (O U.toScheme)

def tensorUnitTwist (M : LineBundle X) (U : X.Opens)
    (f : M.sheaf.restrict U.ι ≅ O U.toScheme) : O U.toScheme ≅ O U.toScheme :=
  f.symm ≪≫ (Scheme.Modules.restrictFunctor U.ι).mapIso (moduleTensorUnit M.sheaf).symm ≪≫
    moduleTensorRestrict U (O X) M.sheaf ≪≫
      moduleTensorIso (Scheme.Modules.restrictUnitIso U.ι) f ≪≫ moduleTensorUnit (O U.toScheme)

lemma tensor_multiply_framed (L M : LineBundle X) (s : O X ⟶ L.sheaf) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme)
    (f : M.sheaf.restrict U.ι ≅ O U.toScheme) :
    f.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map (sectionMultiply L M s) ≫
      (tensorFrame L M U e f).hom = (tensorUnitTwist M U f).hom ≫
        (restrictSection U.ι s ≫ e.hom) := by
  let F : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
  let c : O U.toScheme ⟶ O U.toScheme := restrictSection U.ι s ≫ e.hom
  let unitRestriction : F.obj (O X) ≅ O U.toScheme :=
    Scheme.Modules.restrictUnitIso U.ι
  let sourceUnit : moduleTensor X (O X) M.sheaf ≅ M.sheaf :=
    moduleTensorUnit M.sheaf
  let targetUnit : moduleTensor U.toScheme (O U.toScheme) (O U.toScheme) ≅
      O U.toScheme := moduleTensorUnit (O U.toScheme)
  let sourceRestriction : F.obj (moduleTensor X (O X) M.sheaf) ≅
      moduleTensor U.toScheme (F.obj (O X)) (F.obj M.sheaf) :=
    moduleTensorRestrict U (O X) M.sheaf
  let targetRestriction : F.obj (moduleTensor X L.sheaf M.sheaf) ≅
      moduleTensor U.toScheme (F.obj L.sheaf) (F.obj M.sheaf) :=
    moduleTensorRestrict U L.sheaf M.sheaf
  let tensorMap : moduleTensor X (O X) M.sheaf ⟶ moduleTensor X L.sheaf M.sheaf :=
    moduleTensorMap s (𝟙 M.sheaf)
  let multiplication : M.sheaf ⟶ moduleTensor X L.sheaf M.sheaf :=
    sectionMultiply L M s
  have multiplication_eq : multiplication = sourceUnit.inv ≫ tensorMap :=
    sectionMultiply_eq L M s
  have he : F.map s ≫ e.hom = unitRestriction.hom ≫ c := by
    change F.map s ≫ e.hom = unitRestriction.hom ≫
      (unitRestriction.inv ≫ F.map s) ≫ e.hom
    exact ((Category.assoc _ _ _).trans
      (unitRestriction.hom_inv_id_assoc (F.map s ≫ e.hom))).symm
  have ht : moduleTensorMap (F.map s ≫ e.hom) f.hom =
      moduleTensorMap unitRestriction.hom f.hom ≫
        moduleTensorMap c (𝟙 (O U.toScheme)) := by
    rw [← moduleTensorMap_comp (X := U.toScheme),Category.comp_id,← he]
  have naturality : F.map tensorMap ≫ targetRestriction.hom =
      sourceRestriction.hom ≫ moduleTensorMap (F.map s) (𝟙 (F.obj M.sheaf)) := by
    have naturality' : F.map tensorMap ≫ targetRestriction.hom =
        sourceRestriction.hom ≫ moduleTensorMap (F.map s) (F.map (𝟙 M.sheaf)) :=
      moduleTensorRestrict_natural U s (𝟙 M.sheaf)
    simpa only [F.map_id] using naturality'
  change f.inv ≫ F.map multiplication ≫ targetRestriction.hom ≫
      moduleTensorMap (X := U.toScheme) e.hom f.hom ≫ targetUnit.hom =
    (f.inv ≫ F.map sourceUnit.inv ≫ sourceRestriction.hom ≫
      moduleTensorMap unitRestriction.hom f.hom ≫ targetUnit.hom) ≫ c
  rw [multiplication_eq, F.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (F.map tensorMap), naturality]
  simp only [Category.assoc]
  rw [← Category.assoc (moduleTensorMap (X := U.toScheme) (F.map s) (𝟙 _)),
    ← moduleTensorMap_comp (X := U.toScheme),
    Category.id_comp]
  rw [ht,Category.assoc]
  have hscalar : moduleTensorMap c (𝟙 (O U.toScheme)) ≫ targetUnit.hom =
      targetUnit.hom ≫ c := by
    exact (moduleTensorUnit_scalar (X := U.toScheme) c (𝟙 (O U.toScheme))).trans
      (congrArg (fun morphism : O U.toScheme ⟶ O U.toScheme =>
        targetUnit.hom ≫ morphism) (Category.comp_id c))
  rw [hscalar]

lemma tensor_multiply_ideal (L M : LineBundle X) (s : O X ⟶ L.sheaf)
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (f : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    Ideal.span {U.1.topIso.hom (endValue (f.inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map (sectionMultiply L M s) ≫
        (tensorFrame L M U.1 e f).hom))} =
    Ideal.span {U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))} := by
  rw [tensor_multiply_framed,endValue_comp,map_mul,← Ideal.span_singleton_mul_span_singleton]
  have hu : IsUnit (endValue (tensorUnitTwist M U.1 f).hom) :=
    (end_isIso_iff _).mp inferInstance
  rw [Ideal.span_singleton_eq_top.mpr (hu.map U.1.topIso.hom.hom),Ideal.top_mul]
  rfl

theorem divide_by_generated_section [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L M : LineBundle X)
    {σ : Type} [Fintype σ] (k : ℂ →+* Γ(X,⊤))
    (s : σ → (O X ⟶ L.sheaf)) (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    (v : σ → ℂ) (hne : sectionCombination k s v ≠ 0)
    (t : O X ⟶ (L.tensor M).sheaf)
    (ht : pullbackSection (sectionIdeal k s hs v).subschemeι t = 0) :
    ∃! q : O X ⟶ M.sheaf, q ≫ sectionMultiply L M (sectionCombination k s v) = t := by
  apply @geometric_global_division X p M (L.tensor M)
    (sectionMultiply L M (sectionCombination k s v))
    (sectionMultiply_mono L M _ hne) (sectionIdeal k s hs v) ?_ t ht
  intro x
  obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames L M x
  refine ⟨U,hx,f,tensorFrame L M U.1 e f,?_⟩
  exact (sectionIdeal_on_any_frame k s hs v U e).trans
    (tensor_multiply_ideal L M (sectionCombination k s v) U e f).symm

theorem divide_by_power_section [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X) (d n : ℕ)
    {σ : Type} [Fintype σ] (k : ℂ →+* Γ(X,⊤))
    (a : σ → (O X ⟶ (L.pow d).sheaf))
    (ha : (⨆ i, SectionOpens.isoOpen (a i)) = ⊤)
    (v : σ → ℂ) (hne : sectionCombination k a v ≠ 0)
    (t : O X ⟶ (L.pow (d+n)).sheaf)
    (ht : pullbackSection (sectionIdeal k a ha v).subschemeι t = 0) :
    ∃! q : O X ⟶ (L.pow n).sheaf,
      q ≫ sectionMultiply (L.pow d) (L.pow n) (sectionCombination k a v) ≫
        (linePowerAdd L d n).inv = t := by
  let e : (L.pow (d+n)).sheaf ≅ ((L.pow d).tensor (L.pow n)).sheaf :=
    linePowerAdd L d n
  have hv : pullbackSection (sectionIdeal k a ha v).subschemeι (t ≫ e.hom) = 0 := by
    unfold pullbackSection at ht ⊢
    rw [Functor.map_comp,← Category.assoc,ht,zero_comp]
  obtain ⟨q,hq,huniq⟩ := divide_by_generated_section (X := X) p (L.pow d) (L.pow n)
    k a ha v hne (t ≫ e.hom) hv
  let multiplication : (L.pow n).sheaf ⟶ ((L.pow d).tensor (L.pow n)).sheaf :=
    sectionMultiply (L.pow d) (L.pow n) (sectionCombination k a v)
  change q ≫ multiplication = t ≫ e.hom at hq
  refine ⟨q,?_,?_⟩
  · change q ≫ multiplication ≫ e.inv = t
    rw [← Category.assoc,hq,Category.assoc,e.hom_inv_id,Category.comp_id]
  · intro r hr
    apply huniq
    apply (cancel_mono e.inv).mp
    change r ≫ multiplication ≫ e.inv = t at hr
    change (r ≫ multiplication) ≫ e.inv = (t ≫ e.hom) ≫ e.inv
    simpa only [Category.assoc,e.hom_inv_id,Category.comp_id] using hr

lemma global_quotient_ne_zero {M N : X.Modules} (f : M ⟶ N)
    (s : O X ⟶ N) (hs : s ≠ 0) (t : O X ⟶ M) (ht : t ≫ f = s) : t ≠ 0 := by
  intro h
  rw [h,zero_comp] at ht
  exact hs ht.symm

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
