import Mathlib
import OAI.AlgebraicGeometry.RelativeTriviality.Coordinates
import OAI.AlgebraicGeometry.RelativeTriviality.Charts

namespace OAI

noncomputable section

namespace CampanaPeternellSix.RelativeLineCharts
open CategoryTheory AlgebraicGeometry
open scoped Polynomial
universe u
variable (R : Type u) [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

lemma rightChartEquiv_constant (a : R) :
    rightChartEquiv R (HomogeneousLocalization.fromZeroRingHom (grading R) _
      (constants R a)) = Polynomial.C a := by
  rw [← chartSwap_constant R a]
  change chartEquiv R ((chartSwap R).symm ((chartSwap R) _)) = _
  rw [RingEquiv.symm_apply_apply, chartEquiv_constant]

def chartRing (i : Fin 2) := HomogeneousLocalization.Away (grading R) (MvPolynomial.X i)
instance (i : Fin 2) : CommRing (chartRing R i) := inferInstanceAs (CommRing (HomogeneousLocalization.Away _ _))
def chartConstants (i : Fin 2) : R →+* chartRing R i :=
  (HomogeneousLocalization.fromZeroRingHom (grading R) _).comp (constants R)
def chartCoordinate (i : Fin 2) : chartRing R i :=
  HomogeneousLocalization.Away.mk (grading R) (MvPolynomial.isHomogeneous_X R i) 1
    (MvPolynomial.X ((Equiv.swap (0 : Fin 2) 1) i))
    (by simpa using MvPolynomial.isHomogeneous_X R ((Equiv.swap (0 : Fin 2) 1) i))
def chartEquivalence (i : Fin 2) : chartRing R i ≃+* R[X] :=
  Fin.cases (chartEquiv R) (fun j : Fin 1 => Fin.cases (rightChartEquiv R) (fun k => Fin.elim0 k) j) i

lemma chartEquivalence_constant (i : Fin 2) (a : R) :
    chartEquivalence R i (chartConstants R i a) = Polynomial.C a := by
  fin_cases i
  · exact chartEquiv_constant R a
  · exact rightChartEquiv_constant R a

lemma chartEquivalence_coordinate (i : Fin 2) :
    chartEquivalence R i (chartCoordinate R i) = Polynomial.X := by
  fin_cases i
  · convert chartEquiv_coordinate R using 1
    simp [chartEquivalence, chartCoordinate, coordinate]
    rfl
  · convert rightChartEquiv_coordinate R using 1
    simp [chartEquivalence, chartCoordinate, rightCoordinate]
    rfl

lemma chartEquivalence_symm_C (i : Fin 2) (a : R) :
    (chartEquivalence R i).symm (Polynomial.C a) = chartConstants R i a :=
  (RingEquiv.symm_apply_eq (chartEquivalence R i)).mpr (chartEquivalence_constant R i a).symm

lemma chartEquivalence_symm_X (i : Fin 2) :
    (chartEquivalence R i).symm Polynomial.X = chartCoordinate R i :=
  (RingEquiv.symm_apply_eq (chartEquivalence R i)).mpr (chartEquivalence_coordinate R i).symm

end CampanaPeternellSix.RelativeLineCharts
namespace CampanaPeternellSix.RelativeProjectiveBaseChange
section
open CategoryTheory AlgebraicGeometry Limits ProjectiveSpectrum HomogeneousIdeal
open CampanaPeternellSix.RelativePolynomialEvaluation
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

def coefficientMap (f : R →+* S) (n : ℕ) : grading R n →+*ᵍ grading S n where
  __ := MvPolynomial.map f
  map_mem h := MvPolynomial.IsHomogeneous.map h f

lemma irrelevant_le_map_coefficientMap (f : R →+* S) (n : ℕ) :
    irrelevant (grading S n) ≤ (irrelevant (grading R n)).map (coefficientMap f n) := by
  apply toIdeal_le_toIdeal_iff.mp
  refine le_trans ?_ (show MvPolynomial.idealOfVars (Fin (n+1)) S ≤ _ from ?_)
  · rw [toIdeal_irrelevant_le]
    intro i hi a ha
    rw [← pow_one (MvPolynomial.idealOfVars _ _)]
    apply (MvPolynomial.mem_pow_idealOfVars_iff 1 a).mpr
    intro k hk
    have hk' : a.coeff k ≠ 0 := MvPolynomial.mem_support_iff.mp hk
    change a.IsHomogeneous i at ha
    have hdeg := ha hk'
    change 1 ≤ ∑ j ∈ k.support, k j
    simpa [Finsupp.weight_apply, Finsupp.sum] using (Nat.succ_le_iff.mpr hi).trans_eq hdeg.symm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have h := Ideal.mem_map_of_mem (coefficientMap f n).toRingHom
      (mem_irrelevant_of_mem (grading R n) (by decide : 0 < 1)
        (MvPolynomial.isHomogeneous_X R i))
    change MvPolynomial.X i ∈ Ideal.map (coefficientMap f n).toRingHom _
    simpa [coefficientMap] using h

def baseMap (f : R →+* S) (n : ℕ) : space S n ⟶ space R n :=
  AlgebraicGeometry.Proj.map (coefficientMap f n) (irrelevant_le_map_coefficientMap f n)

lemma baseMap_coordinates (f : R →+* S) (n : ℕ) :
    CampanaPeternellSix.ProjectiveCoordinates.HasCoordinatePullback
      (grading R n) (grading S n) (MvPolynomial.map f) (baseMap f n) := by
  constructor
  · intro p; rfl
  · intro U s p h
    let : ((baseMap f n).base p.1).1.toIdeal.IsPrime := ((baseMap f n).base p.1).isPrime
    let : p.1.1.toIdeal.IsPrime := p.1.isPrime
    change (HomogeneousLocalization.localRingHom (coefficientMap f n) _ _ _
      (s.val ⟨(baseMap f n).base p.1, p.2⟩)).val = _
    erw [HomogeneousLocalization.val_localRingHom]
    rfl

lemma baseMap_overBase (f : R →+* S) (n : ℕ) :
    baseMap f n ≫ toBase R n = toBase S n ≫ Spec.map (CommRingCat.ofHom f) := by
  apply ext_to_Spec
  simp only [Scheme.Γ_map_op, Scheme.Hom.comp_appTop]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  have hnat := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)
  have he : ((Scheme.ΓSpecIso (.of R)).inv ≫ (Spec.map (CommRingCat.ofHom f)).appTop ≫
        (toBase S n).appTop) a =
      (((Scheme.ΓSpecIso (.of S)).inv ≫ (toBase S n).appTop) (f a)) := by
    rw [← Category.assoc, ← hnat, Category.assoc]
    rfl
  erw [he]
  apply Subtype.ext
  funext p
  let e := baseMap f n
  let s := ((Scheme.ΓSpecIso (.of R)).inv ≫ (toBase R n).appTop) a
  change (((e.c.app (Opposite.op ⊤)) s).val p) =
    ((((Scheme.ΓSpecIso (.of S)).inv ≫ (toBase S n).appTop) (f a)).val p)
  apply HomogeneousLocalization.val_injective
  let h := baseMap_coordinates f n
  erw [h.2 ⊤ s p (h.1 p.1)]
  let : (e.base p.1).1.toIdeal.IsPrime := (e.base p.1).isPrime
  let : p.1.1.toIdeal.IsPrime := p.1.isPrime
  change Localization.localRingHom (e.base p.1).1.toIdeal p.1.1.toIdeal
    (MvPolynomial.map f) (h.1 p.1)
    (s.val ⟨e.base p.1, trivial⟩).val = _
  dsimp only [s]
  erw [toBase_section R n a, toBase_section S n (f a) p.1]
  change Localization.localRingHom (e.base p.1).1.toIdeal p.1.1.toIdeal
    (MvPolynomial.map f) (h.1 p.1)
      (Localization.mk (MvPolynomial.C a) 1) = Localization.mk (MvPolynomial.C (f a)) 1
  simp
  rfl
end
section
open CategoryTheory AlgebraicGeometry Limits ProjectiveSpectrum HomogeneousLocalization
open CampanaPeternellSix.RelativePolynomialEvaluation
open CampanaPeternellSix.RelativeLineCharts (chartRing chartConstants chartCoordinate chartEquivalence
  chartEquivalence_constant chartEquivalence_coordinate chartEquivalence_symm_C chartEquivalence_symm_X)
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

def chartMap (f : R →+* S) (i : Fin 2) : chartRing R i →+* chartRing S i :=
  HomogeneousLocalization.map (coefficientMap f 1) (by
    rintro a ⟨k, rfl⟩
    change MvPolynomial.map f (MvPolynomial.X i ^ k) ∈ Submonoid.powers (MvPolynomial.X i)
    simpa [coefficientMap] using Submonoid.pow_mem (Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) S))
      (Submonoid.mem_powers _) k)

lemma chartMap_constants (f : R →+* S) (i : Fin 2) (a : R) :
    chartMap f i (chartConstants R i a) = chartConstants S i (f a) := by
  apply HomogeneousLocalization.val_injective
  change (HomogeneousLocalization.map (coefficientMap f 1) _
    (HomogeneousLocalization.Away.mk (grading R 1) (MvPolynomial.isHomogeneous_X R i) 0 (MvPolynomial.C a) _)).val =
    (HomogeneousLocalization.Away.mk (grading S 1) (MvPolynomial.isHomogeneous_X S i) 0 (MvPolynomial.C (f a)) _).val
  simp [HomogeneousLocalization.Away.mk, HomogeneousLocalization.map_mk, coefficientMap]
  change Localization.mk (MvPolynomial.map f (MvPolynomial.C a)) _ = _
  simp

lemma chartMap_coordinate (f : R →+* S) (i : Fin 2) :
    chartMap f i (chartCoordinate R i) = chartCoordinate S i := by
  apply HomogeneousLocalization.val_injective
  change (HomogeneousLocalization.map (coefficientMap f 1) _
    (HomogeneousLocalization.Away.mk (grading R 1) (MvPolynomial.isHomogeneous_X R i) 1
      (MvPolynomial.X ((Equiv.swap (0 : Fin 2) 1) i)) _)).val =
    (HomogeneousLocalization.Away.mk (grading S 1) (MvPolynomial.isHomogeneous_X S i) 1
      (MvPolynomial.X ((Equiv.swap (0 : Fin 2) 1) i)) _).val
  simp only [HomogeneousLocalization.Away.mk]
  rw [HomogeneousLocalization.map_mk]
  change Localization.mk (MvPolynomial.map f (MvPolynomial.X ((Equiv.swap (0 : Fin 2) 1) i)))
      ⟨MvPolynomial.map f (MvPolynomial.X i ^ 1), _⟩ =
    Localization.mk (MvPolynomial.X ((Equiv.swap (0 : Fin 2) 1) i)) ⟨MvPolynomial.X i ^ 1, _⟩
  simp

lemma chartMap_polynomial (f : R →+* S) (i : Fin 2) :
    (chartEquivalence S i).toRingHom.comp (chartMap f i) =
      (Polynomial.mapRingHom f).comp (chartEquivalence R i).toRingHom := by
  have h : ((chartEquivalence S i).toRingHom.comp (chartMap f i)).comp
      (chartEquivalence R i).symm.toRingHom = Polynomial.mapRingHom f := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        chartEquivalence_symm_C, chartMap_constants, chartEquivalence_constant]
      simp
    · simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
        chartEquivalence_symm_X, chartMap_coordinate, chartEquivalence_coordinate]
      simp
  apply RingHom.ext
  intro x
  have hx := DFunLike.congr_fun h (chartEquivalence R i x)
  simpa using hx

end
section
open CategoryTheory AlgebraicGeometry Limits ProjectiveSpectrum HomogeneousLocalization
open CampanaPeternellSix.RelativePolynomialEvaluation
open CampanaPeternellSix.RelativeLineCharts (chartRing chartConstants chartCoordinate chartEquivalence
  chartEquivalence_constant chartEquivalence_coordinate chartEquivalence_symm_C chartEquivalence_symm_X)
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

lemma chartMap_pushout (f : R →+* S) (i : Fin 2) :
    IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom (chartConstants R i))
      (CommRingCat.ofHom (chartConstants S i)) (CommRingCat.ofHom (chartMap f i)) := by
  have H : IsPushout (CommRingCat.ofHom f)
      (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))
      (CommRingCat.ofHom (Polynomial.C : S →+* Polynomial S))
      (CommRingCat.ofHom (Polynomial.mapRingHom f)) := by
    algebraize [f, Polynomial.mapRingHom f]
    exact CommRingCat.isPushout_of_isPushout R S (Polynomial R) (Polynomial S)
  refine H.of_iso (Iso.refl _) (Iso.refl _)
    (chartEquivalence R i).symm.toCommRingCatIso
    (chartEquivalence S i).symm.toCommRingCatIso (by simp) ?_ ?_ ?_
  · ext a
    exact chartEquivalence_symm_C R i a
  · ext a
    exact chartEquivalence_symm_C S i a
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    apply (chartEquivalence S i).injective
    have h := DFunLike.congr_fun (chartMap_polynomial f i) ((chartEquivalence R i).symm x)
    simpa using h.symm

lemma chartMap_pullback (f : R →+* S) (i : Fin 2) :
    IsPullback (Spec.map (CommRingCat.ofHom (chartMap f i)))
      (Spec.map (CommRingCat.ofHom (chartConstants S i)))
      (Spec.map (CommRingCat.ofHom (chartConstants R i)))
      (Spec.map (CommRingCat.ofHom f)) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (chartMap_pushout f i)).flip

variable (R) in
def chartInclusion (i : Fin 2) : Spec (.of (chartRing R i)) ⟶ space R 1 :=
  AlgebraicGeometry.Proj.awayι (grading R 1) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X R i) (by decide : 0 < 1)

private lemma isOpenImmersion_iso_inv_comp {X Y Z : Scheme} (e : X ≅ Y)
    (f : X ⟶ Z) [IsOpenImmersion f] : IsOpenImmersion (e.inv ≫ f) :=
  IsOpenImmersion.comp _ _

instance (i : Fin 2) : IsOpenImmersion (chartInclusion R i) := by
  exact isOpenImmersion_iso_inv_comp (AlgebraicGeometry.Proj.basicOpenIsoSpec (grading R 1)
    (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X R i) (by decide : 0 < 1))
    (AlgebraicGeometry.Proj.basicOpen (grading R 1) (MvPolynomial.X i)).ι

@[reassoc] lemma chartInclusion_toBase (i : Fin 2) :
    chartInclusion R i ≫ toBase R 1 = Spec.map (CommRingCat.ofHom (chartConstants R i)) := by
  erw [chartInclusion, toBase, ← Category.assoc, AlgebraicGeometry.Proj.awayι_toSpecZero,
    ← Spec.map_comp]
  rfl

@[simp] lemma coefficientMap_X (f : R →+* S) (n : ℕ) (i : Fin (n+1)) :
    coefficientMap f n (MvPolynomial.X i) = MvPolynomial.X i := by
  change MvPolynomial.map f (MvPolynomial.X i) = _
  simp

lemma awayInclusion_coefficientMap (f : R →+* S) (i : Fin 2)
    (t : MvPolynomial (Fin 2) S) (ht : t ∈ grading S 1 1)
    (he : coefficientMap f 1 (MvPolynomial.X i) = t)
    (hp : Submonoid.powers (MvPolynomial.X i) ≤
      (Submonoid.powers t).comap (coefficientMap f 1)) :
    AlgebraicGeometry.Proj.awayι (grading S 1) t ht (by decide : 0 < 1) ≫ baseMap f 1 =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.map (coefficientMap f 1) hp)) ≫
        chartInclusion R i := by
  subst t
  exact AlgebraicGeometry.Proj.awayι_comp_map (coefficientMap f 1)
    (irrelevant_le_map_coefficientMap f 1) (by decide : 0 < 1)
    (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X R i)

@[reassoc] lemma chartInclusion_baseMap (f : R →+* S) (i : Fin 2) :
    chartInclusion S i ≫ baseMap f 1 =
      Spec.map (CommRingCat.ofHom (chartMap f i)) ≫ chartInclusion R i := by
  exact awayInclusion_coefficientMap f i (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X S i) (coefficientMap_X f 1 i) _

lemma chartInclusion_cartesian (f : R →+* S) (i : Fin 2) :
    IsPullback (Spec.map (CommRingCat.ofHom (chartMap f i))) (chartInclusion S i)
      (chartInclusion R i) (baseMap f 1) := by
  apply IsOpenImmersion.isPullback
  · exact chartInclusion_baseMap f i
  · dsimp only [chartInclusion, baseMap]
    erw [AlgebraicGeometry.Proj.opensRange_awayι, AlgebraicGeometry.Proj.opensRange_awayι,
      AlgebraicGeometry.Proj.map_preimage_basicOpen, coefficientMap_X]

end
open CategoryTheory AlgebraicGeometry Limits ProjectiveSpectrum HomogeneousIdeal
open CampanaPeternellSix.RelativePolynomialEvaluation
open CampanaPeternellSix.RelativeLineCharts (chartRing chartConstants)
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable (R : Type u) [CommRing R]

lemma irrelevant_le_span_variables (n : ℕ) :
    (irrelevant (grading R n)).toIdeal ≤ Ideal.span (Set.range (MvPolynomial.X : Fin (n+1) → MvPolynomial (Fin (n+1)) R)) := by
  rw [toIdeal_irrelevant_le]
  intro i hi a ha
  change a ∈ MvPolynomial.idealOfVars (Fin (n+1)) R
  rw [← pow_one (MvPolynomial.idealOfVars _ _)]
  apply (MvPolynomial.mem_pow_idealOfVars_iff 1 a).mpr
  intro k hk
  have hk' : a.coeff k ≠ 0 := MvPolynomial.mem_support_iff.mp hk
  change a.IsHomogeneous i at ha
  have hdeg := ha hk'
  change 1 ≤ ∑ j ∈ k.support, k j
  simpa [Finsupp.weight_apply, Finsupp.sum] using (Nat.succ_le_iff.mpr hi).trans_eq hdeg.symm

def twoChartCover : (space R 1).OpenCover :=
  (AlgebraicGeometry.Proj.affineOpenCoverOfIrrelevantLESpan (grading R 1)
    (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) R)
    (MvPolynomial.isHomogeneous_X R) (fun _ => by decide : ∀ _ : Fin 2, 0 < 1)
    (irrelevant_le_span_variables R 1)).openCover

variable {R} {S : Type u} [CommRing S]

lemma baseMap_isPullback (f : R →+* S) :
    IsPullback (baseMap f 1) (toBase S 1) (toBase R 1)
      (Spec.map (CommRingCat.ofHom f)) := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (twoChartCover R)
  intro i
  change IsPullback (pullback.snd (baseMap f 1) (chartInclusion R i))
    (pullback.fst (baseMap f 1) (chartInclusion R i) ≫ toBase S 1)
    (chartInclusion R i ≫ toBase R 1) (Spec.map (CommRingCat.ofHom f))
  have h := (chartInclusion_cartesian f i).flip
  refine (chartMap_pullback f i).of_iso h.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ (by simp)
  · simp
  · simp only [Iso.refl_hom, Category.comp_id, ← Category.assoc,
      h.isoPullback_hom_fst]
    exact (chartInclusion_toBase (R := S) i).symm
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact (chartInclusion_toBase (R := R) i).symm

 

theorem projectiveLine_cartesian (R S : Type u) [CommRing R] [CommRing S]
    (f : R →+* S) :
    ∃ g : space S 1 ⟶ space R 1,
      IsPullback g (toBase S 1) (toBase R 1) (Spec.map (CommRingCat.ofHom f)) ∧
      CampanaPeternellSix.ProjectiveCoordinates.HasCoordinatePullback
        (grading R 1) (grading S 1) (MvPolynomial.map f) g :=
  ⟨baseMap f 1, baseMap_isPullback f, baseMap_coordinates f 1⟩

end CampanaPeternellSix.RelativeProjectiveBaseChange

end

end OAI
