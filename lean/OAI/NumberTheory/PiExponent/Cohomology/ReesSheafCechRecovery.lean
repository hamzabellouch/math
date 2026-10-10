import OAI.NumberTheory.PiExponent.Ampleness.ReesProductAugmentation
import OAI.NumberTheory.PiExponent.Approximation.AdditiveKernelTransport
import OAI.NumberTheory.PiExponent.Cohomology.CechZeroAdditive
import OAI.NumberTheory.PiExponent.Cohomology.FreeCechSections
import OAI.NumberTheory.PiExponent.Cohomology.ReesCechRecovery
import OAI.NumberTheory.PiExponent.Cohomology.ReesCohomologySetup
import OAI.NumberTheory.PiExponent.Cohomology.ReesSheafCechNaturality

namespace OAI

namespace PiExponent.ReesSheafCechRecovery
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ReesGrading PiExponentSeshadri.ModuleFlasque
open PiExponent.GeometrySupport PiExponent.ReesSheafCechBase PiExponent.ReesSheafCechNaturality
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedCech
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance 1001] AddCommGroup.toAddCommMonoid
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow PiExponentSeshadri.Geometry.PresentsPullbackIdeal
  PiExponent.ExceptionalAffineChart.sectionsEquiv PiExponent.ExceptionalAffineChart.representedSectionsEquiv
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

private abbrev schemeFreeOpen (X : Scheme) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

private local instance cochainAddCommGroup (n q : ℕ) :
    AddCommGroup
      (CechHigher.Cochain (affineBlowup I).ringCatSheaf (opens I a) (exceptionalPower I n) q) :=
  inferInstanceAs (AddCommGroup (∀ t : Fin (q + 1) → J,
    schemeFreeOpen (affineBlowup I) (CechHigher.intersection (opens I a) t) ⟶
      exceptionalPower I n))

def gradedCycles (n q : ℕ) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    AddSubgroup (GradedCech.Cochain (grading (J := J) (R := R)) (integerPiece I)
      MvPolynomial.X variable_mem n q) := by
  letI := presentationAlgebra I a
  letI := gradedScalarAction I a
  exact (GradedCech.differentialHom (grading (J := J) (R := R)) (integerPiece I)
    MvPolynomial.X variable_mem n q).ker

instance gradedCyclesGroup (n q : ℕ) : AddCommGroup (gradedCycles I a n q) :=
  AddSubgroup.toAddCommGroup _

@[instance_reducible] def groupAddZero {A : Type*} (G : AddCommGroup A) : AddZero A := by
  letI := G
  infer_instance

@[instance_reducible] def groupAddZeroClass {A : Type*} (G : AddCommGroup A) : AddZeroClass A := by
  letI := G
  infer_instance

instance (priority := 2000) gradedCyclesAddZero (n q : ℕ) : AddZero (gradedCycles I a n q) :=
  groupAddZero (gradedCyclesGroup I a n q)

instance (priority := 2000) gradedCyclesAddZeroClass (n q : ℕ) :
    AddZeroClass (gradedCycles I a n q) :=
  groupAddZeroClass (gradedCyclesGroup I a n q)

def cyclesEquiv (n q : ℕ) :
    CechZeroAdditive.cycles (affineBlowup I).ringCatSheaf (opens I a) (exceptionalPower I n) q ≃+
      gradedCycles I a n q := by
  letI := presentationAlgebra I a
  letI := gradedScalarAction I a
  exact AdditiveKernelTransport.kernelEquiv
    (cochainEquiv I a n q) (cochainEquiv I a n (q+1))
    (CechZeroAdditive.differentialHom (affineBlowup I).ringCatSheaf
      (opens I a) (exceptionalPower I n) q)
    (GradedCech.differentialHom (grading (J := J) (R := R)) (integerPiece I)
      MvPolynomial.X variable_mem n q)
    (fun c => cochainEquiv_differential I a n q c)

def ordinaryAugmentation (n : ℕ) : ↥(I^n : Ideal R) →+ gradedCycles I a n 0 := by
  letI := presentationAlgebra I a
  letI := gradedScalarAction I a
  exact ((GradedCech.augmentation (grading (J := J) (R := R)) (integerPiece I)
    MvPolynomial.X variable_mem n).comp (ordinaryPowerEquivIntegerPiece I n).toAddMonoidHom).codRestrict
    (gradedCycles I a n 0) (fun b =>
      GradedCech.differential_augmentation _ _ _ _ _ _)

def globalCyclesEquiv (ha : Ideal.span (Set.range fun j => (a j).val) = I) (n : ℕ) :
    (schemeFreeOpen (affineBlowup I) ⊤ ⟶ exceptionalPower I n) ≃+
      gradedCycles I a n 0 := by
  letI : AddCommGroup (freeOpen (affineBlowup I).ringCatSheaf ⊤ ⟶ exceptionalPower I n) :=
    Preadditive.homGroup (C := (affineBlowup I).Modules) _ _
  exact (CechZeroAdditive.sectionsEquiv (affineBlowup I).ringCatSheaf (opens I a)
    (exceptionalPower I n) ⊤ (fun _ => le_top) (by rw [iSup_opens I a ha])).trans
      (cyclesEquiv I a n 0)

def ordinarySectionHom (ha : Ideal.span (Set.range fun j => (a j).val) = I) (n : ℕ) :
    ↥(I^n : Ideal R) →+ (schemeFreeOpen (affineBlowup I) ⊤ ⟶ exceptionalPower I n) :=
  (globalCyclesEquiv I a ha n).symm.toAddMonoidHom.comp (ordinaryAugmentation I a n)

def ordinaryGlobalSection (ha : Ideal.span (Set.range fun j => (a j).val) = I) (n : ℕ) :
    ↥(I^n : Ideal R) →+ Γ(exceptionalPower I n, ⊤) :=
  (freeOpenSectionsEquiv ⊤ (exceptionalPower I n)).toAddMonoidHom.comp
    (ordinarySectionHom I a ha n)

theorem ordinarySectionHom_restriction
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) (n : ℕ)
    (b : ↥(I^n : Ideal R)) (t : Fin 1 → J) :
    tupleHomEquiv I a n 0 t
      (CechHigher.augmentation (affineBlowup I).ringCatSheaf (opens I a)
        (exceptionalPower I n) ⊤ (fun _ => le_top) (ordinarySectionHom I a ha n b) t) =
      ReesProductAugmentation.ordinaryFraction I a (tupleSet t) n b := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  have h := (globalCyclesEquiv I a ha n).apply_symm_apply (ordinaryAugmentation I a n b)
  have hv := congrFun (congrArg Subtype.val h) t
  change _ = GradedCech.augmentation (grading (J := J) (R := R)) (integerPiece I)
    MvPolynomial.X variable_mem n (ordinaryPowerEquivIntegerPiece I n b) t at hv
  exact hv.trans (ReesProductAugmentation.augmentation_eq_ordinaryFraction I a n b t)

theorem ordinarySectionHom_chartValue
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) (n : ℕ)
    (b : ↥(I^n : Ideal R)) (t : Fin 1 → J) :
    (ReesProductPower.chartPowerMap I a (tuple_mem 0 t 0) n
      (tupleHomEquiv I a n 0 t
        (CechHigher.augmentation (affineBlowup I).ringCatSheaf (opens I a)
          (exceptionalPower I n) ⊤ (fun _ => le_top)
          (ordinarySectionHom I a ha n b) t))).val =
      ReesProductChart.chartBase I a (tupleSet t) b.val := by
  rw [ordinarySectionHom_restriction]
  exact ReesProductAugmentation.chartPowerMap_ordinaryFraction I a (tuple_mem 0 t 0) n b

theorem ordinarySectionHom_frozenChartValue
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) (n : ℕ)
    (b : ↥(I^n : Ideal R)) (t : Fin 1 → J) :
    (ReesFrozenPower.pieceEquiv I a (tuple_mem 0 t 0) n
      (tupleHomEquiv I a n 0 t
        (CechHigher.augmentation (affineBlowup I).ringCatSheaf (opens I a)
          (exceptionalPower I n) ⊤ (fun _ => le_top)
          (ordinarySectionHom I a ha n b) t))).val =
      ReesFrozenChart.base I a (tupleSet t) b.val := by
  apply (ReesFrozenChart.coordinateEquiv I a (tupleSet t)).injective
  rw [ReesFrozenPower.coordinate_pieceEquiv, ordinarySectionHom_chartValue]
  exact ((ReesFrozenChart.coordinateEquiv I a (tupleSet t)).apply_symm_apply _).symm

variable [IsNoetherianRing R]

theorem eventually_recovery_and_primitives
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Function.Bijective (ordinaryGlobalSection I a ha n) ∧
      ∀ q : ℕ, CechHigher.HasPrimitives (affineBlowup I).ringCatSheaf
        (opens I a) (exceptionalPower I n) q := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  obtain ⟨N, hN⟩ := ReesCechRecovery.eventually_ordinary_power_recovery I a ha
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hpositive, hrecovery⟩ := hN n hn
  have hb : Function.Bijective (ordinaryAugmentation I a n) := by
    apply (Function.bijective_iff_existsUnique _).mpr
    intro c
    obtain ⟨b, hb, hu⟩ := hrecovery c.val c.property
    refine ⟨b, Subtype.ext hb, ?_⟩
    intro z hz
    exact hu z (congrArg Subtype.val hz)
  constructor
  · exact (freeOpenSectionsEquiv ⊤ (exceptionalPower I n)).bijective.comp
      ((globalCyclesEquiv I a ha n).symm.bijective.comp hb)
  · intro q
    exact AdditiveKernelTransport.transport_primitives
      (cochainEquiv I a n q) (cochainEquiv I a n (q+1)) (cochainEquiv I a n (q+2))
      (CechZeroAdditive.differentialHom (affineBlowup I).ringCatSheaf
        (opens I a) (exceptionalPower I n) q)
      (CechZeroAdditive.differentialHom (affineBlowup I).ringCatSheaf
        (opens I a) (exceptionalPower I n) (q+1))
      (GradedCech.differentialHom (grading (J := J) (R := R)) (integerPiece I)
        MvPolynomial.X variable_mem n q)
      (GradedCech.differentialHom (grading (J := J) (R := R)) (integerPiece I)
        MvPolynomial.X variable_mem n (q+1))
      (fun c => cochainEquiv_differential I a n q c)
      (fun c => cochainEquiv_differential I a n (q+1) c) (hpositive q)

theorem eventually_recovery
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Function.Bijective (ordinaryGlobalSection I a ha n) := by
  obtain ⟨N, hN⟩ := eventually_recovery_and_primitives I a ha
  exact ⟨N, fun n hn => (hN n hn).1⟩

theorem eventually_recovery_and_cohomology
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Function.Bijective (ordinaryGlobalSection I a ha n) ∧
      ∀ (q : ℕ) (x : CategoryTheory.Abelian.Ext.{1} (C := (affineBlowup I).Modules)
        (schemeFreeOpen (affineBlowup I) ⊤) (exceptionalPower I n) (q+1)), x = 0 := by
  obtain ⟨N, hN⟩ := eventually_recovery_and_primitives I a ha
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hb, hp⟩ := hN n hn
  refine ⟨hb, ?_⟩
  intro q x
  let : (exceptionalPower I n).IsQuasicoherent :=
    ReesCohomologySetup.exceptionalPower_isQuasicoherent I n
  exact FreeCechSections.affine_ext_succ_eq_zero (affineBlowup I) (exceptionalPower I n)
    (opens I a) ⊤ (fun _ => le_top) (by rw [iSup_opens I a ha])
    (tuple_isAffine I a) q (hp q) x

end
end PiExponent.ReesSheafCechRecovery

end OAI
