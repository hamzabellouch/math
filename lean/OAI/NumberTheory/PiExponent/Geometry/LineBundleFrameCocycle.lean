import OAI.NumberTheory.PiExponent.Approximation.FrameSubopensCoherence
import OAI.NumberTheory.PiExponent.Approximation.SectionOpens
import OAI.NumberTheory.PiExponent.Geometry.LineBundleGluing
import OAI.NumberTheory.PiExponent.Polynomials.FrameCoefficientLaws

namespace OAI

namespace PiExponentSeshadri.LineBundleFrameCocycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentSeshadri.ProjectiveChartSections

variable {X : Scheme} {ι : Type} (M : X.Modules) (U : ι → X.Opens)
  (e : ∀ i, M.restrict (U i).ι ≅ structureSheaf (U i).toScheme)

abbrev frame (i : ι) (W : X.Opens) (hi : W ≤ U i) := restrictOpenFrame hi (e i)

abbrev coeff (i : ι) (W : X.Opens) (hi : W ≤ U i) :=
  framedCoefficientsEquiv W M (frame M U e i W hi)

lemma coeff_restrict {V W : X.Opens} (h : V ≤ W) (i : ι) (hi : W ≤ U i)
    (s : Γ(M,W)) :
    coeff M U e i V (h.trans hi) (M.presheaf.map (homOfLE h).op s) =
      X.presheaf.map (homOfLE h).op (coeff M U e i W hi s) := by
  change framedCoefficientsEquiv V M (restrictOpenFrame (h.trans hi) (e i)) _ = _
  rw [← restrictOpenFrame_trans h hi (e i)]
  exact framedCoefficientsEquiv_restrict M h _ s

def transition (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j) : Γ(X,W)ˣ :=
  Units.map W.topIso.hom.hom.toMonoidHom
    (frameChange (frame M U e j W hj) (frame M U e i W hi))

lemma coeff_change (i j : ι) (W : X.Opens) (hi : W ≤ U i) (hj : W ≤ U j)
    (s : Γ(M,W)) :
    coeff M U e i W hi s = (transition M U e i j W hi hj : Γ(X,W)) *
      coeff M U e j W hj s := by
  exact framedCoefficientsEquiv_change W M (frame M U e j W hj) (frame M U e i W hi) s

def ofFrames : LineBundleGluing.Cocycle U where
  transition := transition M U e
  restriction i j {V W} h hi hj := by
    let s := (coeff M U e j W hj).symm 1
    have hj1 : coeff M U e j W hj s = (1 : Γ(X,W)) :=
      (coeff M U e j W hj).apply_symm_apply 1
    have hi1 : coeff M U e i W hi s = (transition M U e i j W hi hj : Γ(X,W)) := by
      rw [coeff_change M U e i j W hi hj, hj1, mul_one]
    have hjV : coeff M U e j V (h.trans hj) (M.presheaf.map (homOfLE h).op s) = 1 := by
      rw [coeff_restrict M U e h j hj, hj1]
      exact map_one (X.presheaf.map (homOfLE h).op).hom
    calc
      _ = X.presheaf.map (homOfLE h).op (coeff M U e i W hi s) := congrArg _ hi1.symm
      _ = coeff M U e i V (h.trans hi) (M.presheaf.map (homOfLE h).op s) :=
        (coeff_restrict M U e h i hi s).symm
      _ = _ := by rw [coeff_change M U e i j V (h.trans hi) (h.trans hj), hjV, mul_one]
  identity i W hi := by
    apply Units.ext
    change W.topIso.hom (endValue ((frame M U e i W hi).inv ≫
      (frame M U e i W hi).hom)) = 1
    simp
  cocycle i j k W hi hj hk := by
    apply Units.ext
    change W.topIso.hom (endValue ((frame M U e j W hj).inv ≫
      (frame M U e i W hi).hom)) *
      W.topIso.hom (endValue ((frame M U e k W hk).inv ≫
        (frame M U e j W hj).hom)) =
      W.topIso.hom (endValue ((frame M U e k W hk).inv ≫
        (frame M U e i W hi).hom))
    rw [← map_mul, mul_comm, ← endValue_comp]
    simp

def toSections (V : X.Opens) (s : Γ(M,V)) : LineBundleGluing.sections (ofFrames M U e) V :=
  ⟨fun p => coeff M U e p.1 p.2.val p.2.property.2
    (M.presheaf.map (homOfLE p.2.property.1).op s), by
    constructor
    · intro i W W' hW hi h
      change X.presheaf.map (homOfLE h).op
        (coeff M U e i W hi (M.presheaf.map (homOfLE hW).op s)) = _
      rw [← coeff_restrict]
      congr 1
      change (M.presheaf.map _ ≫ M.presheaf.map _) s = _
      rw [← Functor.map_comp]
      rfl
    · intro i j W hW hi hj
      exact coeff_change M U e i j W hi hj _⟩

lemma chartEquiv_toSections (i : ι) (V : X.Opens) (hi : V ≤ U i) (s : Γ(M,V)) :
    LineBundleGluing.chartEquiv (ofFrames M U e) i hi (toSections M U e V s) =
      coeff M U e i V hi s := by
  change coeff M U e i V hi (M.presheaf.map (homOfLE (le_refl V)).op s) = _
  simp

lemma toSections_bijective (i : ι) (V : X.Opens) (hi : V ≤ U i) :
    Function.Bijective (toSections M U e V) := by
  constructor
  · intro s t h
    apply (coeff M U e i V hi).injective
    simpa only [chartEquiv_toSections] using
      congrArg (LineBundleGluing.chartEquiv (ofFrames M U e) i hi) h
  · intro t
    refine ⟨(coeff M U e i V hi).symm
      (LineBundleGluing.chartEquiv (ofFrames M U e) i hi t), ?_⟩
    apply (LineBundleGluing.chartEquiv (ofFrames M U e) i hi).injective
    rw [chartEquiv_toSections, AddEquiv.apply_symm_apply]

def presheafHom : M.val ⟶ LineBundleGluing.presheaf (ofFrames M U e) where
  app V := ModuleCat.ofHom
    (X := M.val.obj V)
    (Y := (LineBundleGluing.presheaf (ofFrames M U e)).obj V)
    { toFun := toSections M U e V.unop
      map_add' := by
        intro s t
        apply Subtype.ext
        funext p
        change coeff M U e p.1 p.2.val p.2.property.2
          (M.presheaf.map (homOfLE p.2.property.1).op (s + t)) = _
        erw [map_add]
        exact map_add _ _ _
      map_smul' := by
        intro a s
        apply Subtype.ext
        funext p
        change coeff M U e p.1 p.2.val p.2.property.2
          (M.presheaf.map (homOfLE p.2.property.1).op (a • s)) =
          X.presheaf.map (homOfLE p.2.property.1).op a *
            coeff M U e p.1 p.2.val p.2.property.2
              (M.presheaf.map (homOfLE p.2.property.1).op s)
        erw [M.map_smul]
        exact framedCoefficientsEquiv_smul _ _ _ _ _ }
  naturality {V W} f := by
    ext s
    apply Subtype.ext
    funext p
    change coeff M U e p.1 p.2.val p.2.property.2
      (M.presheaf.map (homOfLE p.2.property.1).op (M.presheaf.map f s)) =
      coeff M U e p.1 p.2.val p.2.property.2 (M.presheaf.map _ s)
    congr 1
    change (M.presheaf.map _ ≫ M.presheaf.map _) s = _
    rw [← Functor.map_comp]
    rfl

lemma restrict_presheafHom_isIso (i : ι) :
    IsIso ((modulePresheafRestrict (U i).ι).map (presheafHom M U e)) := by
  let f := (modulePresheafRestrict (U i).ι).map (presheafHom M U e)
  have (V : (U i).toScheme.Opensᵒᵖ) : IsIso (f.app V) := by
    apply (ConcreteCategory.isIso_iff_bijective (f.app V)).mpr
    exact toSections_bijective M U e i ((U i).ι ''ᵁ V.unop) ((U i).ι_image_le V.unop)
  let a := PresheafOfModules.isoMk (fun V => asIso (f.app V))
    (fun {_ _} k => f.naturality k)
  change IsIso a.hom
  infer_instance

lemma sheafification_presheafHom_isIso (hcover : ⊤ ≤ ⨆ i, U i) :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (presheafHom M U e)) := by
  apply SectionOpens.isIso_of_locally_isIso
  intro x
  have hx : x ∈ ⨆ i, U i := hcover (show x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  refine ⟨U i, hi, ?_⟩
  let := restrict_presheafHom_isIso M U e i
  apply (NatIso.isIso_map_iff (moduleSheafificationRestrict (U i).ι)
    (presheafHom M U e)).mpr
  change IsIso ((PresheafOfModules.sheafification (𝟙 (U i).toScheme.ringCatSheaf.obj)).map
    ((modulePresheafRestrict (U i).ι).map (presheafHom M U e)))
  infer_instance

def isoSheaf (hcover : ⊤ ≤ ⨆ i, U i) :
    M ≅ LineBundleGluing.sheaf (ofFrames M U e) := by
  letI := sheafification_presheafHom_isIso M U e hcover
  exact ((asIso (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
    (𝟙 X.ringCatSheaf.obj)).counit).app M).symm ≪≫
    @asIso _ _ _ _
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (presheafHom M U e))
      (sheafification_presheafHom_isIso M U e hcover)

end
end PiExponentSeshadri.LineBundleFrameCocycle

end OAI
