import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.EtalePointChart
import OAI.AlgebraicGeometry.Seshadri.Blowup.Gluing

namespace OAI

section
namespace MaximalSeshadri.PlaneBlowup
noncomputable section
open MvPolynomial ReesGrading
variable (K : Type) [Field K]
abbrev PlaneRing := MvPolynomial (Fin 2) K
abbrev originIdeal : Ideal (PlaneRing K) := MvPolynomial.idealOfVars (Fin 2) K

def coordinate (i : Fin 2) : originIdeal K :=
  ⟨X i, Ideal.subset_span (Set.mem_range_self i)⟩

def chartSubstitution (i : Fin 2) : PlaneRing K →+* PlaneRing K :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun j => if j = i then X i else X i * X j)

@[simp] lemma substitution_C (i : Fin 2) (c : K) : chartSubstitution K i (C c) = C c := by
  simp [chartSubstitution]

@[simp] lemma substitution_self (i : Fin 2) : chartSubstitution K i (X i) = X i := by
  simp [chartSubstitution]

@[simp] lemma substitution_other (i j : Fin 2) (h : j ≠ i) :
    chartSubstitution K i (X j) = X i * X j := by
  simp [chartSubstitution, h]

lemma substitution_ideal (i : Fin 2) :
    (originIdeal K).map (chartSubstitution K i) ≤ Ideal.span {X i} := by
  rw [Ideal.map_le_iff_le_comap]
  apply Ideal.span_le.mpr
  rintro _ ⟨j, rfl⟩
  change chartSubstitution K i (X j) ∈ Ideal.span {X i}
  by_cases h : j = i
  · subst j
    rw [substitution_self]
    exact Ideal.subset_span rfl
  · rw [substitution_other _ _ _ h]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

lemma substitution_regular (i : Fin 2) :
    IsRegular (chartSubstitution K i (coordinate K i).val) := by
  change IsRegular (chartSubstitution K i (X i))
  rw [substitution_self]
  exact isRegular_iff_ne_zero.mpr (MvPolynomial.X_ne_zero i)

def toPolynomial (i : Fin 2) : chart (originIdeal K) (coordinate K i) →+* PlaneRing K :=
  chartLift (originIdeal K) (coordinate K i) (chartSubstitution K i)
    (by simpa [coordinate] using substitution_ideal K i) (substitution_regular K i)

@[simp] lemma toPolynomial_base (i : Fin 2) (p : PlaneRing K) :
    toPolynomial K i (chartBase (originIdeal K) (coordinate K i) p) =
      chartSubstitution K i p := chartLift_base _ _ _ _ _ p

lemma toPolynomial_ratio (i j : Fin 2) (hji : j ≠ i) :
    toPolynomial K i (ratio (originIdeal K) (coordinate K i) (coordinate K j)) = X j := by
  have hr : IsRegular (X i : PlaneRing K) :=
    isRegular_iff_ne_zero.mpr (MvPolynomial.X_ne_zero i)
  apply hr.left
  have h := congrArg (toPolynomial K i)
    (base_mul_ratio (originIdeal K) (coordinate K i) (coordinate K j))
  change toPolynomial K i (chartBase (originIdeal K) (coordinate K i) (X i) *
    ratio (originIdeal K) (coordinate K i) (coordinate K j)) =
    toPolynomial K i (chartBase (originIdeal K) (coordinate K i) (X j)) at h
  simpa only [map_mul, toPolynomial_base, substitution_self, substitution_other _ _ _ hji]
    using h

def fromPolynomial (i : Fin 2) : PlaneRing K →+* chart (originIdeal K) (coordinate K i) :=
  MvPolynomial.eval₂Hom
    ((chartBase (originIdeal K) (coordinate K i)).comp MvPolynomial.C)
    (fun j => if j = i then chartBase (originIdeal K) (coordinate K i) (X i)
      else ratio (originIdeal K) (coordinate K i) (coordinate K j))

@[simp] lemma fromPolynomial_C (i : Fin 2) (c : K) :
    fromPolynomial K i (C c) = chartBase (originIdeal K) (coordinate K i) (C c) := by
  simp [fromPolynomial]

@[simp] lemma fromPolynomial_self (i : Fin 2) :
    fromPolynomial K i (X i) = chartBase (originIdeal K) (coordinate K i) (X i) := by
  simp [fromPolynomial]

@[simp] lemma fromPolynomial_other (i j : Fin 2) (h : j ≠ i) :
    fromPolynomial K i (X j) = ratio (originIdeal K) (coordinate K i) (coordinate K j) := by
  simp [fromPolynomial, h]

lemma from_substitution (i : Fin 2) : (fromPolynomial K i).comp (chartSubstitution K i) =
    chartBase (originIdeal K) (coordinate K i) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro j
    by_cases h : j = i
    · subst j; simp
    · simp only [RingHom.comp_apply, substitution_other _ _ _ h, map_mul,
        fromPolynomial_self, fromPolynomial_other _ _ _ h]
      exact base_mul_ratio (originIdeal K) (coordinate K i) (coordinate K j)

lemma to_from (i : Fin 2) : (toPolynomial K i).comp (fromPolynomial K i) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro c; simp
  · intro j
    by_cases h : j = i
    · subst j; simp
    · simp [h, toPolynomial_ratio]

lemma from_to (i : Fin 2) : (fromPolynomial K i).comp (toPolynomial K i) = RingHom.id _ := by
  symm
  apply chartHom_ext (originIdeal K) (coordinate K i) (RingHom.id _)
    ((fromPolynomial K i).comp (toPolynomial K i)) _
    (chart_generator_regular (originIdeal K) (coordinate K i))
  apply RingHom.ext
  intro p
  change chartBase (originIdeal K) (coordinate K i) p =
    fromPolynomial K i (toPolynomial K i (chartBase (originIdeal K) (coordinate K i) p))
  rw [toPolynomial_base]
  exact (RingHom.congr_fun (from_substitution K i) p).symm

def chartEquiv (i : Fin 2) : chart (originIdeal K) (coordinate K i) ≃+* PlaneRing K :=
  { toPolynomial K i with
    invFun := fromPolynomial K i
    left_inv := fun x => RingHom.congr_fun (from_to K i) x
    right_inv := fun x => RingHom.congr_fun (to_from K i) x }

end

noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial ReesGrading
variable (K : Type) [Field K]

def planePresentation : Algebra.SubmersivePresentation K (PlaneRing K) (Fin 2) Empty where
  toGenerators := Algebra.Generators.mvPolynomial K (Fin 2)
  relation i := i.elim
  span_range_relation_eq_ker := by
    rw [Algebra.Generators.ker_eq_ker_aeval_val]
    simp only [Algebra.Generators.mvPolynomial_val, MvPolynomial.aeval_X_left]
    change Ideal.span (Set.range (fun i : Empty => i.elim)) = RingHom.ker (RingHom.id _)
    rw [Set.range_eq_empty, Ideal.span_empty]
    exact ((RingHom.ker_eq_bot_iff_eq_zero (RingHom.id _)).mpr (fun _ h => h)).symm
  map i := i.elim
  map_inj := Function.injective_of_subsingleton _
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_isEmpty, map_one]
    exact isUnit_one

lemma plane_standardSmooth :
    RingHom.IsStandardSmoothOfRelativeDimension 2 (MvPolynomial.C : K →+* PlaneRing K) := by
  change RingHom.IsStandardSmoothOfRelativeDimension 2 (algebraMap K (PlaneRing K))
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact (planePresentation K).isStandardSmoothOfRelativeDimension
    (by simp [Algebra.Presentation.dimension])

def planeCover : (affineBlowup (originIdeal K)).AffineOpenCover :=
  generatorCover (originIdeal K) (coordinate K) rfl

def structureMap : affineBlowup (originIdeal K) ⟶ Spec (.of K) :=
  projection (originIdeal K) ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C)

lemma chart_standardSmooth (i : Fin 2) :
    RingHom.IsStandardSmoothOfRelativeDimension 2
      ((chartBase (originIdeal K) (coordinate K i)).comp MvPolynomial.C) := by
  have h := (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 2)).left (T := chart (originIdeal K) (coordinate K i))
    (MvPolynomial.C : K →+* PlaneRing K) (chartEquiv K i).symm (plane_standardSmooth K)
  convert h using 1
  apply RingHom.ext
  intro c
  exact (fromPolynomial_C K i c).symm

theorem smooth_structureMap : SmoothOfRelativeDimension 2 (structureMap K) := by
  have : ∀ i, IsAffine ((planeCover K).openCover.X i) :=
    fun i => inferInstanceAs (IsAffine (Spec (.of (chart (originIdeal K) (coordinate K i)))))
  apply HasRingHomProperty.of_source_openCover (P := @SmoothOfRelativeDimension.{0} 2)
    (Q := RingHom.Locally (@RingHom.IsStandardSmoothOfRelativeDimension 2))
    (planeCover K).openCover
  intro i
  apply HasRingHomProperty.appTop (P := @SmoothOfRelativeDimension.{0} 2)
  change Fin 2 at i
  change SmoothOfRelativeDimension 2
    ((chartCover (originIdeal K)).f (coordinate K i) ≫
      (projection (originIdeal K) ≫ Spec.map (CommRingCat.ofHom MvPolynomial.C)))
  rw [← Category.assoc, chartCover_projection]
  apply (congrArg (SmoothOfRelativeDimension 2)
    (Spec.map_comp (CommRingCat.ofHom (MvPolynomial.C : K →+* PlaneRing K))
      (CommRingCat.ofHom (chartBase (originIdeal K) (coordinate K i))))).mp
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension.{0} 2)).mpr
  exact RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 2))
    _ (chart_standardSmooth K i)

end

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ReesGrading MaximalSeshadri.Geometry
variable (K : Type) [Field K]

theorem smooth_etale_baseChange {Y B : Scheme}
    (j : Y ⟶ Spec (.of (PlaneRing K))) [Etale j]
    (ρ : B ⟶ Y) (hρ : IsBlowup ((IdealPullback.specIdeal (originIdeal K)).comap j) ρ) :
    SmoothOfRelativeDimension 2
      (ρ ≫ j ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* PlaneRing K))) := by
  let π := projection (originIdeal K)
  let hπ := rees_isBlowup (originIdeal K)
  let e := hρ.iso (hπ.flat_baseChange j)
  have hc : e.hom ≫ pullback.snd j π ≫ structureMap K =
      ρ ≫ j ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* PlaneRing K)) := by
    have he : e.hom ≫ pullback.fst j π = ρ :=
      hρ.iso_hom_comp (hπ.flat_baseChange j)
    calc
      _ = e.hom ≫ (pullback.snd j π ≫ π) ≫
          Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* PlaneRing K)) := by
        simp only [structureMap, π, Category.assoc]
      _ = e.hom ≫ (pullback.fst j π ≫ j) ≫
          Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* PlaneRing K)) := by
        rw [pullback.condition]
      _ = (e.hom ≫ pullback.fst j π) ≫ j ≫
          Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* PlaneRing K)) := by
        simp only [Category.assoc]
      _ = _ := by rw [he]
  rw [← hc]
  have : SmoothOfRelativeDimension 2 (structureMap K) := smooth_structureMap K
  have : SmoothOfRelativeDimension 2 (pullback.snd j π ≫ structureMap K) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)
  exact inferInstanceAs (SmoothOfRelativeDimension (0 + 2) _)

end
end MaximalSeshadri.PlaneBlowup

namespace MaximalSeshadri.PointBlowup
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MaximalSeshadri.Geometry MaximalSeshadri.AlgebraicJets
variable {K S : Type} [Field K] [CommRing S] [Algebra K S]

theorem exists_smooth_point_blowup_neighborhood
    [Algebra.IsStandardSmoothOfRelativeDimension 2 K S] (ρ : S →ₐ[K] K)
    {B : Scheme} (π : B ⟶ Spec (.of S))
    (hπ : IsBlowup (IdealPullback.specIdeal (RingHom.ker ρ)) π) :
    ∃ s : S, ρ s ≠ 0 ∧ SmoothOfRelativeDimension 2
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s)))) π ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (Localization.Away s)))) := by
  obtain ⟨x, s, hs, hx, hj, hI⟩ := exists_centered_etale_point_chart 2 ρ
  let f := (algebraMap S (Localization.Away s)).comp (MvPolynomial.aeval (R := K) x).toRingHom
  let j := Spec.map (CommRingCat.ofHom f)
  have : Etale j := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hj
  let a := Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away s)))
  let θ := pullback.fst a π
  have hθ : IsBlowup ((IdealPullback.specIdeal (PlaneBlowup.originIdeal K)).comap j) θ := by
    have h := hπ.flat_baseChange a
    rw [IdealPullback.specIdeal_comap] at h ⊢
    simpa only [hI] using h
  have ht := PlaneBlowup.smooth_etale_baseChange K j θ hθ
  have hc : j ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* PlaneBlowup.PlaneRing K)) =
      Spec.map (CommRingCat.ofHom (algebraMap K (Localization.Away s))) := by
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    simp [f, ← IsScalarTower.algebraMap_apply K S (Localization.Away s)]
  rw [hc] at ht
  exact ⟨s, hs, ht⟩

end
end MaximalSeshadri.PointBlowup


end

end OAI
