import Mathlib
import OAI.AlgebraicGeometry.NumericalDimension.IncidenceSmoothness

namespace OAI

/-! Generic Members. -/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct

namespace NumericalDimensionOne
noncomputable section
universe u
lemma smooth_at_generic_fiber
    {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}} [IsIntegral Y]
    (f : X ⟶ Y) (sY : Y ⟶ Spec (.of k))
    [LocallyOfFinitePresentation f] [LocallyOfFiniteType sY] [Smooth (f ≫ sY)]
    (x : X) (hx : f x = genericPoint Y) : x ∈ f.smoothLocus := by
  let A := X.presheaf.stalk x
  let K := Y.presheaf.stalk (f x)
  let point : PrimeSpectrum k := sY (f x)
  let R := (Spec.structureSheaf k).presheaf.stalk point
  let e : k ≃ₐ[k] R := IsLocalization.atUnits _ point.asIdeal.primeCompl
      (fun z hz ↦ by aesop (add simp IsUnit.mem_submonoid_iff))
  let : Field R := (e.toRingEquiv.symm.isField (Field.toIsField k)).toField
  let : CharZero R := charZero_of_injective_ringHom e.injective
  have hK : IsField K := by
    have hh : ∀ y : Y, y = genericPoint Y → IsField (Y.presheaf.stalk y) := by
      intro y hy
      subst y
      exact Field.toIsField Y.functionField
    exact hh (f x) hx
  let : Field K := hK.toField
  let : Algebra R K := (sY.stalkMap (f x)).hom.toAlgebra
  let : Algebra K A := (f.stalkMap x).hom.toAlgebra
  let : Algebra R A := ((f ≫ sY).stalkMap x).hom.toAlgebra
  have : IsScalarTower R K A := IsScalarTower.of_algebraMap_eq' (by
    change ((f ≫ sY).stalkMap x).hom = (f.stalkMap x).hom.comp (sY.stalkMap (f x)).hom
    rw [Scheme.Hom.stalkMap_comp]
    rfl)
  have : Algebra.EssFiniteType R K := LocallyOfFiniteType.stalkMap sY (f x)
  have : Algebra.EssFiniteType K A := LocallyOfFiniteType.stalkMap f x
  have : CharZero K := charZero_of_injective_ringHom (algebraMap R K).injective
  have hsm : ((f ≫ sY).stalkMap x).hom.FormallySmooth := by
    exact (Scheme.Hom.mem_smoothLocus).mp (by rw [(f ≫ sY).smoothLocus_eq_top]; trivial)
  have : Algebra.FormallySmooth R A := hsm
  exact formallySmooth_over_perfect_subfield R K A

theorem proper_generic_smooth_open
    {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}} [IsIntegral Y]
    (f : X ⟶ Y) (sY : Y ⟶ Spec (.of k))
    [IsProper f] [LocallyOfFinitePresentation f] [LocallyOfFiniteType sY]
    [Smooth (f ≫ sY)] :
    ∃ U : Y.Opens, genericPoint Y ∈ U ∧ f ⁻¹ᵁ U ≤ f.smoothLocus := by
  let B : Set X := (f.smoothLocus : Set X)ᶜ
  have hB : IsClosed B := f.smoothLocus.isOpen.isClosed_compl
  let U : Y.Opens := ⟨(f '' B)ᶜ,(f.isClosedMap B hB).isOpen_compl⟩
  refine ⟨U,?_,?_⟩
  · rintro ⟨x,hx,hfx⟩
    exact hx (smooth_at_generic_fiber f sY x hfx)
  · intro x hx
    by_contra h
    exact hx ⟨x,h,rfl⟩
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct

namespace NumericalDimensionOne
noncomputable section
universe u
lemma smooth_morphismRestrict_of_preimage_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (U : Y.Opens) (hU : f ⁻¹ᵁ U ≤ f.smoothLocus) : Smooth (f ∣_ U) := by
  have hs : Smooth ((f ⁻¹ᵁ U).ι ≫ f) := by
    apply Scheme.Hom.smoothLocus_eq_top_iff.mp
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    apply top_unique
    intro x _
    exact hU x.2
  have : MorphismProperty.IsStableUnderBaseChange @Smooth.{u} :=
    smooth_isStableUnderBaseChange
  have : MorphismProperty.HasOfPostcompProperty @Smooth.{u}
      (MorphismProperty.monomorphisms Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.hasOfPostcompProperty_monomorphisms
  apply MorphismProperty.of_postcomp @AlgebraicGeometry.Smooth.{u}
    (W' := MorphismProperty.monomorphisms Scheme.{u}) (f ∣_ U) U.ι
    (inferInstanceAs (Mono U.ι))
  rwa [morphismRestrict_ι]

theorem exists_smooth_closed_fiber
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {X Y : Scheme.{u}} [IsIntegral Y]
    (f : X ⟶ Y) (sY : Y ⟶ Spec (.of k))
    [IsProper f] [LocallyOfFinitePresentation f] [LocallyOfFiniteType sY]
    [Smooth (f ≫ sY)] :
    ∃ p : Spec (.of k) ⟶ Y, p ≫ sY = 𝟙 _ ∧
      Smooth (Limits.pullback.snd f p) := by
  obtain ⟨U,hU,hpre⟩ := proper_generic_smooth_open f sY
  have : Smooth (f ∣_ U) := smooth_morphismRestrict_of_preimage_le f U hpre
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  obtain ⟨y,hyU,hy⟩ := nonempty_inter_closedPoints
    (show (U : Set Y).Nonempty from ⟨genericPoint Y,hU⟩) U.isOpen.isLocallyClosed
  let a := pointOfClosedPoint sY y hy
  have ha : Set.range a ⊆ Set.range U.ι := by
    rintro _ ⟨z,rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (pointOfClosedPoint_apply sY y hy z).symm ▸ hyU
  let b := IsOpenImmersion.lift U.ι a ha
  have hb : b ≫ U.ι = a := IsOpenImmersion.lift_fac U.ι a ha
  refine ⟨a,pointOfClosedPoint_comp sY y hy,?_⟩
  have hp := (IsPullback.of_hasPullback (f ∣_ U) b).paste_horiz
    (isPullback_morphismRestrict f U).flip
  rw [hb] at hp
  let e := hp.isoIsPullback _ _ (IsPullback.of_hasPullback f a)
  have he : e.hom ≫ pullback.snd f a = pullback.snd (f ∣_ U) b :=
    hp.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback f a)
  have : Smooth (e.hom ≫ pullback.snd f a) := by
    rw [he]
    infer_instance
  have : Smooth (e.inv ≫ e.hom ≫ pullback.snd f a) := inferInstance
  simpa using this
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct

namespace NumericalDimensionOne
noncomputable section
universe u

theorem exists_smooth_closed_fiber_in_open
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {X Y : Scheme.{u}} [IsIntegral Y]
    (f : X ⟶ Y) (sY : Y ⟶ Spec (.of k))
    [IsProper f] [LocallyOfFinitePresentation f] [LocallyOfFiniteType sY]
    [Smooth (f ≫ sY)] (V : Y.Opens) (hV : genericPoint Y ∈ V) :
    ∃ p : Spec (.of k) ⟶ Y, p ≫ sY = 𝟙 _ ∧
      Set.range p ⊆ V ∧ Smooth (Limits.pullback.snd f p) := by
  obtain ⟨U,hU,hpre⟩ := proper_generic_smooth_open f sY
  let W := U ⊓ V
  have : Smooth (f ∣_ W) := smooth_morphismRestrict_of_preimage_le f W
    (fun _ hx => hpre hx.1)
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace sY
  obtain ⟨y,hyW,hy⟩ := nonempty_inter_closedPoints
    (show (W : Set Y).Nonempty from ⟨genericPoint Y, hU, hV⟩) W.isOpen.isLocallyClosed
  let a := pointOfClosedPoint sY y hy
  have ha : Set.range a ⊆ Set.range W.ι := by
    rintro _ ⟨z,rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (pointOfClosedPoint_apply sY y hy z).symm ▸ hyW
  let b := IsOpenImmersion.lift W.ι a ha
  have hb : b ≫ W.ι = a := IsOpenImmersion.lift_fac W.ι a ha
  refine ⟨a,pointOfClosedPoint_comp sY y hy,?_,?_⟩
  · rintro _ ⟨z,rfl⟩
    exact (pointOfClosedPoint_apply sY y hy z).symm ▸ hyW.2
  have hp := (IsPullback.of_hasPullback (f ∣_ W) b).paste_horiz
    (isPullback_morphismRestrict f W).flip
  rw [hb] at hp
  let e := hp.isoIsPullback _ _ (IsPullback.of_hasPullback f a)
  have he : e.hom ≫ pullback.snd f a = pullback.snd (f ∣_ W) b :=
    hp.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback f a)
  have : Smooth (e.hom ≫ pullback.snd f a) := by
    rw [he]
    infer_instance
  have : Smooth (e.inv ≫ e.hom ≫ pullback.snd f a) := inferInstance
  simpa using this
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct

namespace NumericalDimensionOne
noncomputable section
universe u

theorem exists_smooth_incidence_member
    {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {n : Type u} [Fintype n] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsProper sX] [Smooth sX]
    (V : X.OpenCover) [∀ i, IsAffine (V.X i)]
    (r : ∀ i, n → Γ(V.X i,⊤)) (hn : ∀ i, ∃ j, r i j = 1)
    (J : 𝔸(n;X).IdealSheafData)
    (hJ : ∀ i, J.comap (AffineSpace.map n (V.f i)) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span {universalLinearSection (r i)}))
    (T : 𝔸(n;Spec (.of k)).Opens) (hT : genericPoint _ ∈ T) :
    ∃ p : Spec (.of k) ⟶ 𝔸(n;Spec (.of k)),
      p ≫ 𝔸(n;Spec (.of k)) ↘ Spec (.of k) = 𝟙 _ ∧ Set.range p ⊆ T ∧
        Smooth (pullback.snd (J.subschemeι ≫ AffineSpace.map n sX) p) := by
  have hs := universal_incidence_smooth_over V r hn J hJ
  let f := J.subschemeι ≫ AffineSpace.map n sX
  let sA := 𝔸(n;Spec (.of k)) ↘ Spec (.of k)
  have hm : IsProper (AffineSpace.map n sX) :=
    MorphismProperty.of_isPullback (AffineSpace.isPullback_map (n := n) sX).flip inferInstance
  have hfs : f ≫ sA = (J.subschemeι ≫ 𝔸(n;X) ↘ X) ≫ sX := by
    simp only [f,sA,Category.assoc,AffineSpace.map_over]
  have : Smooth (f ≫ sA) := by rw [hfs]; infer_instance
  have : IsLocallyNoetherian (𝔸(n;Spec (.of k))) :=
    LocallyOfFiniteType.isLocallyNoetherian sA
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f sA
  have : LocallyOfFinitePresentation f := inferInstance
  exact exists_smooth_closed_fiber_in_open f sA T hT
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct

namespace NumericalDimensionOne
noncomputable section
universe u
lemma idealSheaf_comap_ofIdealTop_affine {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (I : Ideal Γ(Y,⊤)) :
    (Scheme.IdealSheafData.ofIdealTop I).comap f =
      Scheme.IdealSheafData.ofIdealTop (I.map f.appTop.hom) := by
  have ofIdealTop_top {Z : Scheme.{u}} [IsAffine Z] (J : Ideal Γ(Z, ⊤)) :
      (Scheme.IdealSheafData.ofIdealTop J).ideal ⟨⊤, isAffineOpen_top Z⟩ = J :=
    Scheme.IdealSheafData.equivOfIsAffine.apply_symm_apply J
  apply le_antisymm
  · rw [← Scheme.IdealSheafData.le_map_iff_comap_le]
    apply Scheme.IdealSheafData.le_of_isAffine
    rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom]
    change (Scheme.IdealSheafData.ofIdealTop I).ideal ⟨⊤, isAffineOpen_top Y⟩ ≤
      Ideal.comap f.appTop.hom
        ((Scheme.IdealSheafData.ofIdealTop (I.map f.appTop.hom)).ideal
          ⟨⊤, isAffineOpen_top X⟩)
    exact (ofIdealTop_top I).le.trans
      (Ideal.le_comap_map.trans (Ideal.comap_mono (ofIdealTop_top _).ge))
  · apply Scheme.IdealSheafData.le_of_isAffine
    have h := Scheme.IdealSheafData.le_map_comap
      (Scheme.IdealSheafData.ofIdealTop I) f
    have h' := h ⟨⊤, isAffineOpen_top Y⟩
    rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom] at h'
    change (Scheme.IdealSheafData.ofIdealTop I).ideal ⟨⊤, isAffineOpen_top Y⟩ ≤
      Ideal.comap f.appTop.hom
        (((Scheme.IdealSheafData.ofIdealTop I).comap f).ideal ⟨⊤, isAffineOpen_top X⟩) at h'
    exact (ofIdealTop_top _).le.trans
      (Ideal.map_le_iff_le_comap.mpr ((ofIdealTop_top I).ge.trans h'))
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct

namespace NumericalDimensionOne
noncomputable section
universe u

def parameterSection {n : Type u} {X S : Scheme.{u}} (f : X ⟶ S)
    (p : S ⟶ 𝔸(n;S)) : X ⟶ 𝔸(n;X) :=
  AffineSpace.homOfVector (𝟙 X) (fun j => f.appTop (p.appTop (AffineSpace.coord S j)))
@[reassoc (attr := simp)]
lemma parameterSection_over {n : Type u} {X S : Scheme.{u}} (f : X ⟶ S)
    (p : S ⟶ 𝔸(n;S)) : parameterSection f p ≫ 𝔸(n;X) ↘ X = 𝟙 X := by
  simp [parameterSection]
@[reassoc]
lemma parameterSection_map {n : Type u} {X S : Scheme.{u}} (f : X ⟶ S)
    (p : S ⟶ 𝔸(n;S)) (hp : p ≫ 𝔸(n;S) ↘ S = 𝟙 S) :
    parameterSection f p ≫ AffineSpace.map n f = f ≫ p := by
  apply AffineSpace.hom_ext
  · simp [Category.assoc,AffineSpace.map_over,hp]
  · intro j
    change (parameterSection f p).appTop
      ((AffineSpace.map n f).appTop (AffineSpace.coord S j)) =
        f.appTop (p.appTop (AffineSpace.coord S j))
    rw [AffineSpace.map_appTop_coord]
    exact AffineSpace.homOfVector_appTop_coord _ _ _

theorem isPullback_parameterSection {n : Type u} {X S : Scheme.{u}} (f : X ⟶ S)
    (p : S ⟶ 𝔸(n;S)) (hp : p ≫ 𝔸(n;S) ↘ S = 𝟙 S) :
    IsPullback (parameterSection f p) f (AffineSpace.map n f) p := by
  apply IsPullback.of_right (h₁₂ := 𝔸(n;X) ↘ X) (h₂₂ := 𝔸(n;S) ↘ S)
    (v₁₃ := f) _ (parameterSection_map f p hp) (AffineSpace.isPullback_map f).flip
  simpa only [parameterSection_over,hp] using (IsPullback.of_id_fst (f := f))

theorem smooth_parameter_member {n : Type u} {X S : Scheme.{u}} (f : X ⟶ S)
    (p : S ⟶ 𝔸(n;S)) (hp : p ≫ 𝔸(n;S) ↘ S = 𝟙 S)
    (J : 𝔸(n;X).IdealSheafData)
    [Smooth (pullback.snd (J.subschemeι ≫ AffineSpace.map n f) p)] :
    Smooth ((J.comap (parameterSection f p)).subschemeι ≫ f) := by
  let I := J.comap (parameterSection f p)
  have h := (IsPullback.of_hasPullback (parameterSection f p) J.subschemeι).flip.paste_vert
    (isPullback_parameterSection f p hp)
  have he := h.isoPullback
  have hsm : Smooth (pullback.snd (J.subschemeι ≫ AffineSpace.map n f) p) := inferInstance
  have h' : Smooth (pullback.fst (parameterSection f p) J.subschemeι ≫ f) := by
    rw [← h.isoPullback_hom_snd]
    infer_instance
  have hi : I.subschemeι = (J.comapIso (parameterSection f p)).hom ≫
      pullback.fst (parameterSection f p) J.subschemeι := by simp [I]
  rw [hi,Category.assoc]
  infer_instance
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct

namespace NumericalDimensionOne
noncomputable section
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {N : ℕ} {D : WeilDivisor X} {s : Fin (N+1) → X.functionField}

theorem DivisorAffineAtlas.incidence_exists
    (A : DivisorAffineAtlas X D s) (hs : ∀ j, s j ≠ 0) :
    ∃ J : 𝔸(Fin (N+1);X).IdealSheafData, ∀ i,
      J.comap (AffineSpace.map _ (A.cover.f i)) =
        Scheme.IdealSheafData.ofIdealTop (Ideal.span {universalLinearSection (A.coordinate i)}) := by
  apply universal_incidence_exists A.cover.X A.cover.f A.coordinate
  intro i j
  exact divisorProjectiveChart_normalized_transition (A.chart i) (A.chart j) hs

theorem DivisorAffineAtlas.exists_smooth_incidence
    (sX : X ⟶ Spec (.of ℂ)) [IsProper sX] [Smooth sX]
    (A : DivisorAffineAtlas X D s) (hs : ∀ j, s j ≠ 0)
    (T : 𝔸(Fin (N+1);Spec (.of ℂ)).Opens) (hT : genericPoint _ ∈ T) :
    ∃ (J : 𝔸(Fin (N+1);X).IdealSheafData) (p : Spec (.of ℂ) ⟶ 𝔸(Fin (N+1);Spec (.of ℂ))),
      (∀ i, J.comap (AffineSpace.map _ (A.cover.f i)) =
        Scheme.IdealSheafData.ofIdealTop (Ideal.span {universalLinearSection (A.coordinate i)})) ∧
      p ≫ 𝔸(Fin (N+1);Spec (.of ℂ)) ↘ Spec (.of ℂ) = 𝟙 _ ∧ Set.range p ⊆ T ∧
      Smooth (pullback.snd (J.subschemeι ≫ AffineSpace.map _ sX) p) := by
  obtain ⟨J,hJ⟩ := A.incidence_exists hs
  have ha (i) : IsAffine (A.cover.X i) := A.affine i
  obtain ⟨p,hp,hpT,hsmp⟩ := exists_smooth_incidence_member sX A.cover A.coordinate
    (fun i => ⟨(A.chart i).unit_index,by simp [DivisorAffineAtlas.coordinate,
      DivisorProjectiveChart.normalized_index]; rfl⟩) J hJ T hT
  exact ⟨J,p,hJ,hp,hpT,hsmp⟩
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct

namespace NumericalDimensionOne
noncomputable section
universe u
lemma appTop_ne_zero_of_range_basicOpen {X Y : Scheme.{u}} [Nonempty X]
    (f : X ⟶ Y) (a : Γ(Y,⊤)) (h : Set.range f ⊆ Y.basicOpen a) :
    f.appTop a ≠ 0 := by
  intro hz
  obtain ⟨x⟩ := ‹Nonempty X›
  have hx : x ∈ f ⁻¹ᵁ Y.basicOpen a := h ⟨x,rfl⟩
  rw [Scheme.preimage_basicOpen_top,hz] at hx
  simp at hx

theorem generic_mem_linear_parameter_open
    {k : Type u} [Field k] {n : Type u} [Fintype n]
    (r : n → Γ(Spec (.of k),⊤)) (i : n) (hi : r i = 1) :
    genericPoint (𝔸(n;Spec (.of k))) ∈
      (𝔸(n;Spec (.of k))).basicOpen (universalLinearSection r) := by
  classical
  let S := Spec (.of k)
  let c : n → Γ(S,⊤) := fun j => if j = i then 1 else 0
  let p := AffineSpace.homOfVector (𝟙 S) c
  have he : p.appTop (universalLinearSection r) = 1 := by
    simp only [universalLinearSection,map_sum,map_mul,← CommRingCat.comp_apply,
      ← Scheme.Hom.comp_appTop]
    simp [p,c,hi]
  have hpre : p ⁻¹ᵁ (𝔸(n;S)).basicOpen (universalLinearSection r) = ⊤ := by
    rw [Scheme.preimage_basicOpen_top,he,Scheme.basicOpen_one]
  obtain ⟨x⟩ := (inferInstance : Nonempty S)
  apply ((genericPoint_spec (𝔸(n;S))).mem_open_set_iff (TopologicalSpace.Opens.isOpen _)).mpr
  exact ⟨p x,Set.mem_univ _,by have hx : x ∈ (⊤ : S.Opens) := trivial; rwa [← hpre] at hx⟩
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct

namespace NumericalDimensionOne
noncomputable section
universe u

def parameterCoefficient {k : Type u} [Field k] {n : Type u}
    (p : Spec (.of k) ⟶ 𝔸(n;Spec (.of k))) (j : n) : k :=
  (Scheme.ΓSpecIso (.of k)).hom (p.appTop (AffineSpace.coord _ j))

def parameterLinearCombination {k : Type u} [Field k] {K : Type u} [Field K]
    [Algebra k K] {n : Type u} [Fintype n]
    (s : n → K) (p : Spec (.of k) ⟶ 𝔸(n;Spec (.of k))) : K :=
  ∑ j, parameterCoefficient p j • s j
lemma parameter_evaluate_linear {k : Type u} [Field k] {K : Type u} [Field K]
    [Algebra k K] {n : Type u} [Fintype n]
    (s : n → K) (L : K →ₗ[k] k)
    (p : Spec (.of k) ⟶ 𝔸(n;Spec (.of k)))
    (hp : p ≫ 𝔸(n;Spec (.of k)) ↘ Spec (.of k) = 𝟙 _) :
    (Scheme.ΓSpecIso (.of k)).hom
      (p.appTop (universalLinearSection (fun j => (Scheme.ΓSpecIso (.of k)).inv (L (s j))))) =
        L (parameterLinearCombination s p) := by
  classical
  simp only [universalLinearSection,map_sum,map_mul,← CommRingCat.comp_apply,
    ← Scheme.Hom.comp_appTop,hp,Scheme.Hom.id_appTop,CommRingCat.id_apply,
    Iso.inv_hom_id_apply,parameterLinearCombination,map_smul,smul_eq_mul]
  simp only [parameterCoefficient,mul_comm]
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct

namespace NumericalDimensionOne
noncomputable section
universe u

def linearMemberSection {n : Type u} [Fintype n] {X S : Scheme.{u}}
    (f : X ⟶ S) (p : S ⟶ 𝔸(n;S)) (r : n → Γ(X,⊤)) : Γ(X,⊤) :=
  ∑ j, r j * f.appTop (p.appTop (AffineSpace.coord S j))
lemma parameterSection_app_universal {n : Type u} [Fintype n] {X S : Scheme.{u}}
    (f : X ⟶ S) (p : S ⟶ 𝔸(n;S)) (r : n → Γ(X,⊤)) :
    (parameterSection f p).appTop (universalLinearSection r) = linearMemberSection f p r := by
  simp only [universalLinearSection,linearMemberSection,map_sum,map_mul,
    ← CommRingCat.comp_apply,← Scheme.Hom.comp_appTop,parameterSection_over]
  simp only [parameterSection, AffineSpace.homOfVector_appTop_coord,
    Scheme.Hom.id_appTop, CommRingCat.id_apply]
  rfl
@[reassoc]
lemma parameterSection_naturality {n : Type u} {V X S : Scheme.{u}}
    (g : V ⟶ X) (f : X ⟶ S) (p : S ⟶ 𝔸(n;S)) :
    g ≫ parameterSection f p = parameterSection (g ≫ f) p ≫ AffineSpace.map n g := by
  apply AffineSpace.hom_ext
  · simp [Category.assoc,AffineSpace.map_over]
  · intro j
    change g.appTop ((parameterSection f p).appTop (AffineSpace.coord X j)) =
      (parameterSection (g ≫ f) p).appTop
        ((AffineSpace.map n g).appTop (AffineSpace.coord X j))
    rw [AffineSpace.map_appTop_coord]
    simp only [parameterSection, AffineSpace.homOfVector_appTop_coord]
    rfl

theorem parameter_member_chart {n : Type u} [Fintype n] {V X S : Scheme.{u}}
    [IsAffine V] (g : V ⟶ X) (f : X ⟶ S) (p : S ⟶ 𝔸(n;S))
    (J : 𝔸(n;X).IdealSheafData) (r : n → Γ(V,⊤))
    (hJ : J.comap (AffineSpace.map n g) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span {universalLinearSection r})) :
    (J.comap (parameterSection f p)).comap g =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span {linearMemberSection (g ≫ f) p r}) := by
  rw [← Scheme.IdealSheafData.comap_comp,parameterSection_naturality,
    Scheme.IdealSheafData.comap_comp,hJ,idealSheaf_comap_ofIdealTop_affine,
    Ideal.map_span,Set.image_singleton,parameterSection_app_universal]
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct

namespace NumericalDimensionOne
noncomputable section

theorem DivisorAffineAtlas.exists_nonzero_smooth_member
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (sX : X ⟶ Spec (.of ℂ)) [IsProper sX] [Smooth sX]
    {N : ℕ} {D : WeilDivisor X} {s : Fin (N+1) → X.functionField}
    (A : DivisorAffineAtlas X D s) (hs : ∀ j, s j ≠ 0) :
    letI := schemeFieldAlgebra (.of ℂ) sX
    ∃ (J : 𝔸(Fin (N+1);X).IdealSheafData)
      (p : Spec (.of ℂ) ⟶ 𝔸(Fin (N+1);Spec (.of ℂ))),
      (∀ i, J.comap (AffineSpace.map _ (A.cover.f i)) =
        Scheme.IdealSheafData.ofIdealTop (Ideal.span {universalLinearSection (A.coordinate i)})) ∧
      p ≫ 𝔸(Fin (N+1);Spec (.of ℂ)) ↘ Spec (.of ℂ) = 𝟙 _ ∧
      Smooth ((J.comap (parameterSection sX p)).subschemeι ≫ sX) ∧
      parameterLinearCombination s p ≠ 0 := by
  classical
  let := schemeFieldAlgebra (.of ℂ) sX
  obtain ⟨L,hL⟩ := Module.Projective.exists_dual_eq_one ℂ (hs 0)
  let r : Fin (N+1) → Γ(Spec (.of ℂ),⊤) :=
    fun j => (Scheme.ΓSpecIso (.of ℂ)).inv (L (s j))
  have hr : r 0 = 1 := by simp [r,hL]
  let T := (𝔸(Fin (N+1);Spec (.of ℂ))).basicOpen (universalLinearSection r)
  have hT : genericPoint _ ∈ T := generic_mem_linear_parameter_open r 0 hr
  obtain ⟨J,p,hJ,hp,hpT,hsm⟩ := A.exists_smooth_incidence sX hs T hT
  have hsm' := smooth_parameter_member sX p hp J
  refine ⟨J,p,hJ,hp,hsm',?_⟩
  have hne := appTop_ne_zero_of_range_basicOpen p (universalLinearSection r) hpT
  intro hz
  apply hne
  apply (Scheme.ΓSpecIso (.of ℂ)).commRingCatIsoToRingEquiv.injective
  rw [map_zero]
  change (Scheme.ΓSpecIso (.of ℂ)).hom
    (p.appTop (universalLinearSection (fun j => (Scheme.ΓSpecIso (.of ℂ)).inv (L (s j))))) = 0
  rw [parameter_evaluate_linear s L p hp,hz,map_zero]
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct

namespace NumericalDimensionOne
noncomputable section
lemma open_scalar_topIso {X : Scheme} (sX : X ⟶ Spec (.of ℂ))
    (U : X.Opens) (z : ℂ) :
    U.topIso.inv (schemeOpenScalar sX U z) =
      (U.ι ≫ sX).appTop ((Scheme.ΓSpecIso (.of ℂ)).inv z) := by
  have h : sX.appLE ⊤ U (by simp) ≫ U.topIso.inv = (U.ι ≫ sX).appTop := by
    exact (sX.appLE_map (U := ⊤) (V := U) (by simp)
      (eqToHom U.ι_image_top).op).trans (by rfl)
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h)
    ((Scheme.ΓSpecIso (.of ℂ)).inv z)
namespace DivisorProjectiveChart
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {N : ℕ} {D : WeilDivisor X} {s : Fin (N+1) → X.functionField}
    (C : DivisorProjectiveChart X D s)

def member (sX : X ⟶ Spec (.of ℂ))
    (p : Spec (.of ℂ) ⟶ 𝔸(Fin (N+1);Spec (.of ℂ))) : Γ(X,C.domain) :=
  ∑ j, C.normalized j * schemeOpenScalar sX C.domain (parameterCoefficient p j)
lemma member_topIso (sX : X ⟶ Spec (.of ℂ))
    (p : Spec (.of ℂ) ⟶ 𝔸(Fin (N+1);Spec (.of ℂ))) :
    C.domain.topIso.inv (C.member sX p) =
      linearMemberSection (C.domain.ι ≫ sX) p (fun j => C.domain.topIso.inv (C.normalized j)) := by
  simp only [member,linearMemberSection,map_sum,map_mul,open_scalar_topIso,
    parameterCoefficient,Iso.hom_inv_id_apply]

theorem member_generic (sX : X ⟶ Spec (.of ℂ))
    (p : Spec (.of ℂ) ⟶ 𝔸(Fin (N+1);Spec (.of ℂ))) (hs : ∀ j, s j ≠ 0) :
    letI := schemeFieldAlgebra (.of ℂ) sX
    X.presheaf.germ C.domain (genericPoint X) C.generic_mem (C.member sX p) =
      parameterLinearCombination s p / s C.unit_index := by
  let := schemeFieldAlgebra (.of ℂ) sX
  have hc (z : ℂ) : X.presheaf.germ C.domain (genericPoint X) C.generic_mem
      (schemeOpenScalar sX C.domain z) = algebraMap ℂ X.functionField z :=
    RingHom.congr_fun (openScalar_generic sX C.domain C.generic_mem) z
  simp only [member,map_sum,map_mul,C.generic_normalized hs,hc,
    parameterLinearCombination,Algebra.smul_def,div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring
end DivisorProjectiveChart
end
end NumericalDimensionOne

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory TopologicalSpace
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry CategoryTheory TopologicalSpace Limits
open Algebra KaehlerDifferential IsLocalRing TensorProduct

namespace NumericalDimensionOne
noncomputable section
namespace DivisorProjectiveChart
variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    {N : ℕ} {D : WeilDivisor X} {s : Fin (N+1) → X.functionField}
    (C : DivisorProjectiveChart X D s)
lemma nonvanishing_section_order (hs : ∀ j, s j ≠ 0)
    (q : PrimeDivisor X) (hq : q.1 ∈ C.domain) : D q = -X.ord (s C.unit_index) q.1 := by
  let : Nonempty C.domain := ⟨⟨q.1,hq⟩⟩
  have hu := order_stalk_unit q
    (C.coordinate_unit.map (X.presheaf.germ C.domain q.1 hq).hom)
  rw [X.algebraMap_germ_eq_germToFunctionField hq] at hu
  have hv : X.germToFunctionField C.domain (C.coordinate C.unit_index) =
      s C.unit_index*C.equation := C.coordinate_value C.unit_index
  rw [hv,X.ord_mul (hs _) C.equation_ne_zero,← C.equation_order q hq] at hu
  omega

theorem member_divisor_order [CompactSpace X] {F : X.functionField} (hF : F ≠ 0)
    (hs : ∀ j, s j ≠ 0) (q : PrimeDivisor X) (hq : q.1 ∈ C.domain) :
    (D + principalWeilDivisor F) q = X.ord (F / s C.unit_index) q.1 := by
  rw [Finsupp.add_apply,principalWeilDivisor_apply,order_div hF (hs _),
    C.nonvanishing_section_order hs q hq]
  omega
end DivisorProjectiveChart

theorem smooth_ideal_open_comap {X V S : Scheme} (f : X ⟶ S)
    (g : V ⟶ X) [IsOpenImmersion g] (I : X.IdealSheafData)
    [Smooth (I.subschemeι ≫ f)] :
    Smooth ((I.comap g).subschemeι ≫ (g ≫ f)) := by
  rw [← I.comapIso_hom_fst g,Category.assoc,← Category.assoc (pullback.fst _ _),
    pullback.condition]
  simp only [Category.assoc]
  infer_instance
end
end NumericalDimensionOne

end OAI
