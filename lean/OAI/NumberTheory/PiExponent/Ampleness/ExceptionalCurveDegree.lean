import OAI.NumberTheory.PiExponent.Ampleness.AdmissibleBlowupGeometry
import OAI.NumberTheory.PiExponent.Ampleness.BlowupCurveMargin
import OAI.NumberTheory.PiExponent.Geometry.CurveContactFamily
import OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionDivisor
import OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionOrder
import OAI.NumberTheory.PiExponent.Geometry.PlaceCenteredBranch
import OAI.NumberTheory.PiExponent.Geometry.ProjectivePullbackFrames
import OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal
import OAI.NumberTheory.PiExponent.Jets.JetCenterIdentification
import OAI.NumberTheory.PiExponent.Jets.JetProductLocalization
import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealTensorPowers
import OAI.NumberTheory.PiExponent.LocalAlgebra.PresentedIdealIso
import OAI.NumberTheory.PiExponent.LocalAlgebra.SectionZeroIdeal

namespace OAI

namespace PiExponent.ExceptionalCurveDegree
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal PiExponent.SectionImageIdeal
variable {X Y : Scheme.{0}}

def inverseSection (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) :
    GlobalSections Y J.inverse.sheaf :=
  (lineTensorInverseIso J).inv ≫ tensorInclusion J J.inverse ι

theorem inverseSection_zeroIdeal (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
    [J.sheaf.IsQuasicoherent] :
    zeroIdeal J.inverse (inverseSection J ι) = imageIdealSheaf ι := by
  classical
  have hc (y : Y) := common_affine_frames J J.inverse y
  choose U hy e f using hc
  let e' y := (e y).some
  let f' y := (f y).some
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U
  · apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hy y⟩
  · intro y
    let V := U y
    let a := Scheme.Modules.restrictUnitIso V.1.ι
    let b := tensorFrame J J.inverse V.1 (e' y) (f' y)
    rw [zeroIdeal_on_frame J.inverse (inverseSection J ι) V (f' y),
      imageIdealSheaf_on_frame ι V (e' y)]
    change Ideal.span {affineMapCoefficient V a (f' y)
      ((lineTensorInverseIso J).inv ≫ tensorInclusion J J.inverse ι)} = _
    erw [affineMapCoefficient_comp V a b (f' y),
      ← Ideal.span_singleton_mul_span_singleton]
    have hu : IsUnit (affineMapCoefficient V a b (lineTensorInverseIso J).inv) := by
      apply IsUnit.map V.1.topIso.hom.hom
      exact (end_isIso_iff _).mp
        (a.symm ≪≫ ((Scheme.Modules.restrictFunctor V.1.ι).mapIso
          (lineTensorInverseIso J)).symm ≪≫ b).isIso_hom
    rw [Ideal.span_singleton_eq_top.mpr hu, Ideal.top_mul]
    exact tensor_inclusion_ideal J J.inverse ι V (e' y) (f' y)

theorem inverseSection_zeroIdeal_eq_comap
    (I : X.IdealSheafData) (π : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
    (hJ : PresentsPullbackIdeal I π J ι) :
    zeroIdeal J.inverse (inverseSection J ι) = I.comap π := by
  let := GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation J
  rw [inverseSection_zeroIdeal, PresentedIdealIso.imageIdealSheaf_eq_comap I π J ι hJ]

theorem zeroIdeal_pullback (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (f : Y ⟶ X) :
    zeroIdeal (L.pullback f) (pullbackSection f s) = (zeroIdeal L s).comap f := by
  classical
  have hlocal (y : Y) : ∃ V : Y.affineOpens, y ∈ V.1 ∧
      (zeroIdeal (L.pullback f) (pullbackSection f s)).ideal V =
        ((zeroIdeal L s).comap f).ideal V := by
    obtain ⟨U, hU, ⟨e⟩⟩ := PiExponentSeshadri.InvertibleLocal.affine_frame L (f y)
    obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset
      (show y ∈ f ⁻¹ᵁ U.1 from hU)
    let g := f.resLE U.1 V hVU
    obtain ⟨eF, he⟩ := exists_restricted_pullback_frame_all_of_factor f U.1 V g
      (Scheme.Hom.resLE_comp_ι f hVU).symm e
    refine ⟨⟨V, hV⟩, hyV, ?_⟩
    rw [zeroIdeal_on_frame (L.pullback f) (pullbackSection f s) ⟨V, hV⟩ eF,
      PiExponentSeshadri.IdealPullback.comap_ideal (zeroIdeal L s) f ⟨V, hV⟩ U hVU,
      zeroIdeal_on_frame L s U e, Ideal.map_span, Set.image_singleton]
    erw [he s]
    congr 2
    change V.topIso.hom ((f.resLE U.1 V hVU).appTop _) = _
    have ht : (f.resLE U.1 V hVU).appTop = U.1.topIso.hom ≫
        f.appLE U.1 V hVU ≫ V.topIso.inv := by
      simpa only [Scheme.Hom.appTop, Scheme.Hom.appLE_eq_app] using!
        (Scheme.Hom.resLE_app_top f hVU)
    rw [ht]
    simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  choose V hy hV using hlocal
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top V
  · apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hy y⟩
  · exact hV

theorem zeroIdeal_zero (L : LineBundle X) : zeroIdeal L 0 = ⊥ := by
  classical
  choose U hx e using fun x : X => PiExponentSeshadri.InvertibleLocal.affine_frame L x
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U
  · apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  · intro x
    rw [zeroIdeal_on_frame L 0 (U x) (e x).some]
    erw [restrictSection_zero, coefficient_zero, map_zero, Ideal.span_singleton_zero]
    rfl

theorem pullback_inverseSection_zeroIdeal
    (I : X.IdealSheafData) (π : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
    (hJ : PresentsPullbackIdeal I π J ι)
    {Z : Scheme.{0}} (g : Z ⟶ Y) :
    zeroIdeal (J.inverse.pullback g) (pullbackSection g (inverseSection J ι)) =
      I.comap (g ≫ π) := by
  rw [zeroIdeal_pullback, inverseSection_zeroIdeal_eq_comap I π J ι hJ,
    Scheme.IdealSheafData.comap_comp]

theorem pullback_inverseSection_ne_zero
    (I : X.IdealSheafData) (π : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
    (hJ : PresentsPullbackIdeal I π J ι)
    {Z : Scheme.{0}} (g : Z ⟶ Y) (hg : I.comap (g ≫ π) ≠ ⊥) :
    pullbackSection g (inverseSection J ι) ≠ 0 := by
  intro hs
  have h := pullback_inverseSection_zeroIdeal I π J ι hJ g
  rw [hs] at h
  exact hg (h.symm.trans (zeroIdeal_zero _))

theorem zeroIdeal_spec_top {A : Type} [CommRing A]
    (L : LineBundle (Spec (CommRingCat.of A)))
    (s : GlobalSections _ L.sheaf) (e : L.sheaf ≅ O (Spec (CommRingCat.of A))) :
    ((zeroIdeal L s).ideal ⟨⊤, isAffineOpen_top _⟩).map
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom =
        Ideal.span {LocalSectionOrder.localCoefficient e s} := by
  change (imageIdeal (L.dualSection s) ⊤).map _ = _
  rw [imageIdeal_top_of_frame (L.dualSection s)
    (InverseFrames.pairingFrame (lineTensorInverseIso L) e)]
  change (Ideal.span {endValue ((InverseFrames.pairingFrame (lineTensorInverseIso L) e).inv ≫
    InverseFrames.dualMap (lineTensorInverseIso L) s)}).map _ = _
  erw [InverseFrames.dualMap_coefficient]
  rw [Ideal.map_span, Set.image_singleton]
  rfl

def localIdeal {A : Type} [CommRing A] (I : X.IdealSheafData)
    (q : Spec (CommRingCat.of A) ⟶ X) : Ideal A :=
  ((I.comap q).ideal ⟨⊤, isAffineOpen_top _⟩).map
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom

theorem localIdeal_specIdeal {A B : Type} [CommRing A] [CommRing B]
    (I : Ideal B) (φ : B →+* A) :
    localIdeal (PiExponentSeshadri.IdealPullback.specIdeal I)
      (Spec.map (CommRingCat.ofHom φ)) = I.map φ := by
  unfold localIdeal
  rw [PiExponentSeshadri.IdealPullback.specIdeal_comap,
    PiExponentSeshadri.IdealPullback.specIdeal_top, Ideal.map_map]
  have he : (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom = RingHom.id A := by
    ext a
    exact (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id_apply a
  rw [he, Ideal.map_id]

theorem localIdeal_compactIdeal {A : Type} [CommRing A]
    {m : ℕ} {K : Type} [Fintype K] (c : K → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (j : CompactLogJetIdeal.affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (φ : CompactLogJetIdeal.coordinateRing m →+* A) :
    localIdeal (CompactLogJetIdeal.compactIdeal c T e j)
      (Spec.map (CommRingCat.ofHom φ) ≫ j) =
        (CompactLogJetIdeal.polynomialIdeal c T e).map φ := by
  unfold localIdeal
  rw [Scheme.IdealSheafData.comap_comp, CompactLogJetIdeal.restrict_compactIdeal]
  exact localIdeal_specIdeal _ φ

theorem localIdeal_eq_top_of_not_mem {A : Type} [CommRing A] [IsLocalRing A]
    (I : X.IdealSheafData) (q : Spec (CommRingCat.of A) ⟶ X)
    (hq : q (IsLocalRing.closedPoint A) ∉ I.support) : localIdeal I q = ⊤ := by
  have havoid (a : Spec (CommRingCat.of A)) : q a ∉ I.support :=
    ((IsLocalRing.specializes_closedPoint a).map q.continuous).mem_open
      I.support.isClosed.isOpen_compl hq
  have ht := CompactJetIdeal.restrict_eq_top_of_disjoint I q havoid
  unfold localIdeal
  rw [ht]
  exact Ideal.map_top _

section Curve
open CurveNormalizationModel CurveValuationCenter CurvePlaceCenter
open LocalSectionOrder
variable {E : Type} [Field E] [Algebra ℂ E]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

theorem map_powerIdeal_eq_top_of_transcendental {m : ℕ}
    (z : Fin (m+1) → E) (hz : ∃ i, Transcendental ℂ (z i))
    (c : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) :
    (CompactJetPolynomial.powerIdeal c (CompactJetPolynomial.logPolynomials T) e).map
      (MvPolynomial.aeval z).toRingHom = ⊤ := by
  classical
  have hn : ∃ i, MvPolynomial.aeval z
      (CompactJetPolynomial.coordinates c (CompactJetPolynomial.logPolynomials T) i) ≠ 0 := by
    by_contra h
    push Not at h
    have hle : Ideal.span (Set.range
        (CompactJetPolynomial.coordinates c (CompactJetPolynomial.logPolynomials T))) ≤
        RingHom.ker (MvPolynomial.aeval z).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact h i
    rw [CompactJetPolynomial.span_coordinates c _
      (CompactJetPolynomial.logPolynomials_eval_zero T)] at hle
    obtain ⟨i, hi⟩ := hz
    have hc : MvPolynomial.X i - MvPolynomial.C (CompactJetPolynomial.center c i) ∈
        WeightedBezout.pointIdeal (CompactJetPolynomial.center c) := by
      change MvPolynomial.aeval (CompactJetPolynomial.center c) _ = 0
      simp
    have he := hle hc
    change MvPolynomial.aeval z _ = 0 at he
    simp only [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C, sub_eq_zero] at he
    exact hi (he ▸ isAlgebraic_algebraMap (CompactJetPolynomial.center c i))
  obtain ⟨i, hi⟩ := hn
  apply Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem _ (show
      CompactJetPolynomial.coordinates c (CompactJetPolynomial.logPolynomials T) i ^ e i ∈
        CompactJetPolynomial.powerIdeal c (CompactJetPolynomial.logPolynomials T) e from
          Ideal.subset_span (Set.mem_range_self i)))
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow]
  exact (isUnit_iff_ne_zero.mpr hi).pow (e i)

theorem compactIdeal_comap_ne_bot_of_generic {m : ℕ} {K : Type} [Fintype K]
    (c : K → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (j : CompactLogJetIdeal.affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (g : parameterCurve f hf ⟶ X) (z : Fin (m+1) → E)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hgeneric : parameterCurveGenericPoint f hf ≫ g =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j) :
    (CompactLogJetIdeal.compactIdeal c T e j).comap g ≠ ⊥ := by
  have htop : localIdeal (CompactLogJetIdeal.compactIdeal c T e j)
      (parameterCurveGenericPoint f hf ≫ g) = ⊤ := by
    rw [hgeneric, localIdeal_compactIdeal]
    unfold CompactLogJetIdeal.polynomialIdeal
    change Ideal.mapHom (MvPolynomial.aeval z).toRingHom _ = _
    rw [map_prod]
    have ht : ∀ k : K, (CompactJetPolynomial.powerIdeal (c k)
        (CompactJetPolynomial.logPolynomials T) e).map (MvPolynomial.aeval z).toRingHom = ⊤ :=
      fun k => map_powerIdeal_eq_top_of_transcendental z hz (c k) T e
    simp only [Ideal.mapHom_apply, ht]
    rw [← Ideal.one_eq_top]
    exact Finset.prod_const_one
  intro hzero
  have hb : localIdeal (CompactLogJetIdeal.compactIdeal c T e j)
      (parameterCurveGenericPoint f hf ≫ g) = ⊥ := by
    simp only [localIdeal, Scheme.IdealSheafData.comap_comp, hzero,
      Scheme.IdealSheafData.comap_bot]
    exact Ideal.map_bot
  exact bot_ne_top (hb.symm.trans htop)

theorem centerMorphism_eq_centeredLift [X.IsSeparated]
    {m : ℕ} (j : CompactLogJetIdeal.affineSpace m ⟶ X)
    (g : parameterCurve f hf ⟶ X) (z : Fin (m+1) → E)
    (hgeneric : parameterCurveGenericPoint f hf ≫ g =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (p : NormalizedPlace ℂ E) (c : Fin m → ℂ)
    (hc : CurveCenters.Centered z (Fin.cases 1 c) p) :
    centerMorphism f hf p ≫ g =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.aeval (PlaceCenteredBranch.lift p z (Fin.cases 1 c) hc)).toRingHom) ≫ j := by
  apply centerMorphism_comp_eq_of_generic f hf p g
  rw [hgeneric, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro P
  exact PlaceCenteredBranch.lift_aeval p z (Fin.cases 1 c) hc P

theorem localIdeal_length_eq_logContact [X.IsSeparated]
    {m K : ℕ} (c : Fin K → Fin m → ℂ) (hc : Function.Injective c)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (R : ℚ) (he : ∀ i, v i * (e i : ℚ) = R)
    (hT : ∀ i, v i.succ < (T i : ℚ) * v 0)
    (j : CompactLogJetIdeal.affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (g : parameterCurve f hf ⟶ X) (z : Fin (m+1) → E)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hgeneric : parameterCurveGenericPoint f hf ≫ g =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (PlaceValuationRing.ring p))]
    (k : Fin K) (hcenter : CurveCenters.Centered z (Fin.cases 1 (c k)) p) :
    ((Module.length (PlaceValuationRing.ring p)
      ((PlaceValuationRing.ring p) ⧸
        localIdeal (CompactLogJetIdeal.compactIdeal c T e j)
          (centerMorphism f hf p ≫ g))).toNat : ℚ) =
      R * PlaceCenteredBranch.logContact p z (c k) hcenter
        (CurveContactFamily.nonconstant z (c k) hz) v := by
  let a := PlaceCenteredBranch.lift p z (Fin.cases 1 (c k)) hcenter
  have ha : (Fin.cases (a 0) (fun i => a i.succ) : Fin (m+1) → PlaceValuationRing.ring p) = a := by
    funext i
    cases i using Fin.cases <;> rfl
  have hy := PlaceCenteredBranch.lift_residue p z (Fin.cases 1 (c k)) hcenter 0
  have hx := fun i : Fin m =>
    PlaceCenteredBranch.lift_residue p z (Fin.cases 1 (c k)) hcenter i.succ
  rw [centerMorphism_eq_centeredLift f hf j g z hgeneric p (c k) hcenter,
    localIdeal_compactIdeal]
  have hm := JetProductLocalization.map_polynomialIdeal_eq_selected
    c hc T e (a 0) (fun i => a i.succ) k hy hx
  rw [ha] at hm
  rw [hm]
  exact LogarithmicContactIdeal.logarithmicIdeal_colength_eq_contact v hv (c k)
    (a 0) (fun i => a i.succ) hy hx
    (PlaceCenteredBranch.logLift_nonconstant p z (c k) hcenter
      (CurveContactFamily.nonconstant z (c k) hz)) T hT R e he

theorem divisor_eq_localIdeal_length
    (L : LineBundle (parameterCurve f hf))
    (s : GlobalSections _ L.sheaf) (hs : s ≠ 0) (p : NormalizedPlace ℂ E) :
    CurvePlaceSectionDivisor.divisor f hf L s hs p =
      (Module.length (PlaceValuationRing.ring p)
        ((PlaceValuationRing.ring p) ⧸ localIdeal (zeroIdeal L s) (centerMorphism f hf p))).toNat := by
  let q := centerMorphism f hf p
  obtain ⟨e, he⟩ := LocalPullbackSectionOrder.exists_frame_coefficient_germ q L
  have hn : localCoefficient e (pullbackSection q s) ≠ 0 := by
    rw [he s]
    apply (map_ne_zero_iff _
      (ConcreteCategory.bijective_of_isIso (Scheme.stalkClosedPointTo q)).injective).mpr
    exact SectionZeroStalk.sectionGerm_ne_zero L s hs
      (CurveSectionDegree.affineFrameAt L (q (IsLocalRing.closedPoint _))).openSet
      (CurveSectionDegree.affineFrameAt L (q (IsLocalRing.closedPoint _))).frame _
      (CurveSectionDegree.affineFrameAt L (q (IsLocalRing.closedPoint _))).mem
  have hi : localIdeal (zeroIdeal L s) q =
      Ideal.span {localCoefficient e (pullbackSection q s)} := by
    unfold localIdeal
    rw [← zeroIdeal_pullback L s q]
    exact zeroIdeal_spec_top (L.pullback q) (pullbackSection q s) e
  rw [CurvePlaceSectionOrder.divisor_eq_local_order f hf L s hs p e, hi,
    CurveLocalOrder.length_quotient_span_eq_addVal hn]
  rfl

variable (I : X.IdealSheafData) (π : Y ⟶ X)
variable (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
variable (hJ : PresentsPullbackIdeal I π J ι)
variable (g : parameterCurve f hf ⟶ Y) (hg : I.comap (g ≫ π) ≠ ⊥)

def idealDivisor : NormalizedPlace ℂ E →₀ ℕ :=
  CurvePlaceSectionDivisor.divisor f hf (J.inverse.pullback g)
    (pullbackSection g (inverseSection J ι))
    (pullback_inverseSection_ne_zero I π J ι hJ g hg)

theorem idealDivisor_apply (p : NormalizedPlace ℂ E) :
    idealDivisor f hf I π J ι hJ g hg p =
      (Module.length (PlaceValuationRing.ring p)
        ((PlaceValuationRing.ring p) ⧸
          localIdeal I (centerMorphism f hf p ≫ g ≫ π))).toNat := by
  erw [idealDivisor, divisor_eq_localIdeal_length]
  have hi : localIdeal
      (zeroIdeal (J.inverse.pullback g) (pullbackSection g (inverseSection J ι)))
        (centerMorphism f hf p) = localIdeal I (centerMorphism f hf p ≫ g ≫ π) := by
    simp only [localIdeal, pullback_inverseSection_zeroIdeal I π J ι hJ g,
      Scheme.IdealSheafData.comap_comp]
  rw [hi]

theorem degree_eq_neg_idealDivisor_sum :
    eulerCharacteristic (parameterCurveStructureMap f hf) 1 (J.pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) =
      -(idealDivisor f hf I π J ι hJ g hg).sum (fun _ n => (n : ℤ)) := by
  have hd := CurvePlaceSectionDivisor.degree_eq_euler_difference_full f hf
    (J.inverse.pullback g) (pullbackSection g (inverseSection J ι))
    (pullback_inverseSection_ne_zero I π J ι hJ g hg)
  have ht := parameterCurve_tensor_euler_add f hf (J.pullback g) (J.inverse.pullback g)
  let e : ((J.pullback g).tensor (J.inverse.pullback g)).sheaf ≅
      structureSheaf (parameterCurve f hf) :=
    (PiExponentSeshadri.PullbackTensor.iso g J J.inverse).symm ≪≫
      (Scheme.Modules.pullback g).mapIso (lineTensorInverseIso J) ≪≫ pullbackUnitIso g
  have he := eulerCharacteristic_iso (parameterCurveStructureMap f hf) e 1
  change _ = -(CurvePlaceSectionDivisor.divisor f hf (J.inverse.pullback g)
    (pullbackSection g (inverseSection J ι)) _).sum (fun _ n => (n : ℤ))
  omega

theorem compactIdeal_degree_eq_neg_contact_sum [X.IsSeparated]
    {m K : ℕ} (c : Fin K → Fin m → ℂ) (hc : Function.Injective c)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (R : ℚ) (he : ∀ i, v i * (e i : ℚ) = R)
    (hT : ∀ i, v i.succ < (T i : ℚ) * v 0)
    (j : CompactLogJetIdeal.affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (pX : X ⟶ Spec (CommRingCat.of ℂ)) [IsSeparated pX]
    (hj : j ≫ pX = CompactLogJetIdeal.structureMap m)
    (π : Y ⟶ X) (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
    (hJ : PresentsPullbackIdeal (CompactLogJetIdeal.compactIdeal c T e j) π J ι)
    (g : parameterCurve f hf ⟶ Y) (z : Fin (m+1) → E)
    (hz : ∃ i, Transcendental ℂ (z i))
    (hgeneric : parameterCurveGenericPoint f hf ≫ g ≫ π =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j)
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (PlaceValuationRing.ring p)))
    (hfinite : ∀ t : E, Transcendental ℂ t →
      FiniteDimensional (IntermediateField.adjoin ℂ {t}) E) :
    ((eulerCharacteristic (parameterCurveStructureMap f hf) 1 (J.pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℚ) =
      -R * ∑ p ∈ CurveContactFamily.places hfinite z c hz,
        CurveContactFamily.contact hres hfinite z c hz v p := by
  classical
  let I := CompactLogJetIdeal.compactIdeal c T e j
  have hg : I.comap (g ≫ π) ≠ ⊥ :=
    compactIdeal_comap_ne_bot_of_generic f hf c T e j (g ≫ π) z hz hgeneric
  let D := idealDivisor f hf I π J ι hJ g hg
  let P := CurveContactFamily.places hfinite z c hz
  have hzero (p : NormalizedPlace ℂ E) (hp : p ∉ P) : D p = 0 := by
    have havoid : (centerMorphism f hf p ≫ g ≫ π)
        (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) ∉ I.support := by
      intro hmem
      change _ ∈ ((CompactLogJetIdeal.compactIdeal c T e j).support : Set X) at hmem
      rw [CompactLogJetIdeal.support_compactIdeal c T e hepos j pX hj] at hmem
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hmem
      obtain ⟨a, ha⟩ := hk
      have hap : CompactLogJetIdeal.point (c k) a = CompactJetPolynomial.centerPoint (c k) := by
        have h := Set.mem_range_self (f := CompactLogJetIdeal.point (c k)) a
        rw [CompactLogJetIdeal.range_point] at h
        exact h
      have hclosed : (centerMorphism f hf p ≫ g ≫ π)
          (IsLocalRing.closedPoint (PlaceValuationRing.ring p)) =
          j (CompactJetPolynomial.centerPoint (c k)) := by
        exact ha.symm.trans (congrArg j hap)
      have hfield : Spec.map (CommRingCat.ofHom
          (algebraMap (PlaceValuationRing.ring p) E)) ≫
          (centerMorphism f hf p ≫ g ≫ π) =
          Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ j := by
        rw [← Category.assoc, centerMorphism_generic]
        exact hgeneric
      apply hp
      exact (CurveContactFamily.mem_places hfinite z c hz p).mpr
        ⟨k, JetCenterIdentification.centered_of_closedPoint_eq p z (c k) j _ hfield hclosed⟩
    change idealDivisor f hf I π J ι hJ g hg p = 0
    rw [idealDivisor_apply, localIdeal_eq_top_of_not_mem I _ havoid]
    simp
  have hsupport : D.support ⊆ P := by
    intro p hp
    by_contra h
    exact (Finsupp.mem_support_iff.mp hp) (hzero p h)
  have hvalue (p : NormalizedPlace ℂ E) (hp : p ∈ P) :
      (D p : ℚ) = R * CurveContactFamily.contact hres hfinite z c hz v p := by
    let := hres p
    have hp' : p ∈ CurveContactFamily.places hfinite z c hz := hp
    let k := CurveContactFamily.center hfinite z c hz p hp
    have hcenter := CurveContactFamily.centered hfinite z c hz p hp
    have h := localIdeal_length_eq_logContact f hf c hc T e v hv R he hT j (g ≫ π)
      z hz hgeneric p k hcenter
    change (idealDivisor f hf I π J ι hJ g hg p : ℚ) = _
    rw [idealDivisor_apply]
    simpa only [CurveContactFamily.contact, dite_eq_left hp', I, k] using h
  have hsum : D.sum (fun _ n => (n : ℚ)) =
      R * ∑ p ∈ P, CurveContactFamily.contact hres hfinite z c hz v p := by
    rw [D.sum_of_support_subset hsupport (fun _ n => (n : ℚ)) (by simp)]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p hp => hvalue p hp)
  have hd := degree_eq_neg_idealDivisor_sum f hf I π J ι hJ g hg
  have hdq : ((eulerCharacteristic (parameterCurveStructureMap f hf) 1 (J.pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) : ℤ) : ℚ) =
      -D.sum (fun _ n => (n : ℚ)) := by
    simpa only [Int.cast_neg, Finsupp.sum, Int.cast_sum, Int.cast_natCast] using
      congrArg (fun a : ℤ => (a : ℚ)) hd
  rw [hsum] at hdq
  simpa only [neg_mul, P] using hdq

end Curve

theorem admissible_degree_eq_neg_contactSum
    {ν Λ D : ℝ} (d : AdmissibleParameters ν Λ D)
    {E : Type} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]
    (y : E) (x : Fin d.m → E)
    (hgen : IntermediateField.adjoin ℂ
      (Set.range (Fin.cases y x : Fin (d.m+1) → E)) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1)
    (f : E) (hf : Transcendental ℂ f) :
    letI := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg f hf
    ∀ (g : CurveNormalizationModel.parameterCurve f hf ⟶ AdmissibleBlowupGeometry.blowup d),
    CurveNormalizationModel.parameterCurveGenericPoint f hf ≫ g ≫
      AdmissibleBlowupGeometry.projection d =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (Fin.cases y x)).toRingHom) ≫
        AdmissibleBlowupGeometry.affineChart d →
    ((eulerCharacteristic (CurveNormalizationModel.parameterCurveStructureMap f hf) 1
        ((AdmissibleBlowupGeometry.J d).pullback g).sheaf -
      eulerCharacteristic (CurveNormalizationModel.parameterCurveStructureMap f hf) 1
        (structureSheaf (CurveNormalizationModel.parameterCurve f hf)) : ℤ) : ℝ) =
      -((AdmissibleBlowupGeometry.scale d).radius : ℝ) *
        BlowupCurveMargin.contactSum d y x hgen htrdeg := by
  let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
  let := hfinite f hf
  intro g hgeneric
  let hres := PlaceLocalRing.residue_integral htrdeg.le
  let z : Fin (d.m+1) → E := Fin.cases y x
  let hz := CurveInequality.nonconstant_coordinates z hgen htrdeg
  have hc : Function.Injective d.curveCenters := by
    let i : Fin d.m := ⟨0, by have := d.m_pos; omega⟩
    intro j k h
    exact d.curveCenters_injective i (congrFun h i)
  have h := compactIdeal_degree_eq_neg_contact_sum f hf d.curveCenters hc
    (AdmissibleBlowupGeometry.logCutoff d) (AdmissibleBlowupGeometry.scale d).jetPowers
    (AdmissibleBlowupGeometry.scale d).jetPowers_pos d.curveJetWeights d.curveJetWeights_pos
    (AdmissibleBlowupGeometry.scale d).radius (AdmissibleBlowupGeometry.scale d).jetPowers_eq
    (AdmissibleBlowupGeometry.logCutoff_strict d) (AdmissibleBlowupGeometry.affineChart d)
    (AdmissibleBlowupGeometry.compactificationStructureMap d)
    (AdmissibleBlowupGeometry.affineChart_over d)
    (AdmissibleBlowupGeometry.projection d) (AdmissibleBlowupGeometry.J d)
    (AdmissibleBlowupGeometry.exceptionalInclusion d)
    (AdmissibleBlowupGeometry.exceptional_presents d) g z hz hgeneric hres hfinite
  change _ = -((AdmissibleBlowupGeometry.scale d).radius : ℝ) *
    ∑ p ∈ CurveContactFamily.places hfinite z d.curveCenters hz,
      (CurveContactFamily.contact hres hfinite z d.curveCenters hz d.curveJetWeights p : ℝ)
  exact_mod_cast h

end
end PiExponent.ExceptionalCurveDegree

end OAI
