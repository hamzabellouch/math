import OAI.Analysis.Pureness.States.FiniteFamilyCarrier
import OAI.Analysis.Pureness.Quasitrace.QuasitraceBaseExtremal
import OAI.Analysis.Pureness.Quasitrace.ComplexQuasitracePullback

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def CompatibleFiniteQuasitrace.toTwoQuasitrace (F : CompatibleFiniteQuasitrace A) :
    TwoQuasitrace A where
  base := (F.level 1).comap (scalarMatrixHom (ι := Fin 1)).toNonUnitalStarAlgHom
  matrix := F.level 2
  extension x := (F.inclusion (show 1 ≤ 2 from by decide) (scalarMatrixHom x)).symm

lemma CompatibleFiniteQuasitrace.toTwoQuasitrace_unit (F : CompatibleFiniteQuasitrace A)
    (hF : F.level 1 1=1) : F.toTwoQuasitrace.base 1=1 := by
  change F.level 1 (scalarMatrixHom 1)=1
  rwa [map_one]

def finiteQuasitraceBaseMap : FiniteQuasitraceCoordinates A →ₗ[ℝ] (A → ℂ) where
  toFun g x := g 1 (scalarMatrixHom (ι := Fin 1) x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [PartialOrder A] [StarOrderedRing A] in
lemma continuous_finiteQuasitraceBaseMap :
    Continuous (finiteQuasitraceBaseMap (A := A)) :=
  continuous_pi fun x => (continuous_apply (scalarMatrixHom (ι := Fin 1) x)).comp
    (continuous_apply 1)

def normalizedFiniteBaseQuasitraceCarrier : Set (A → ℂ) :=
  finiteQuasitraceBaseMap '' (normalizedFiniteQuasitraceCarrier (A := A))

theorem mem_normalizedFiniteBaseQuasitraceCarrier (g : A → ℂ) :
    g ∈ normalizedFiniteBaseQuasitraceCarrier ↔
      ∃ F : CompatibleFiniteQuasitrace A,
        (∀ n, Monotone (fun a : Positive (FinMatrix A n) => (F.level n a.1).re)) ∧
        F.level 1 1=1 ∧ F.toTwoQuasitrace.base.toFun=g := by
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact ⟨finiteQuasitraceFromCoordinates p hp,hp.2.1,hp.2.2.1,rfl⟩
  · rintro ⟨F,hmono,hF,rfl⟩
    exact ⟨F.coordinates,F.coordinates_mem hmono hF,rfl⟩

theorem isCompact_normalizedFiniteBaseQuasitraceCarrier :
    IsCompact (normalizedFiniteBaseQuasitraceCarrier (A := A)) :=
  isCompact_normalizedFiniteQuasitraceCarrier.image continuous_finiteQuasitraceBaseMap

theorem convex_normalizedFiniteBaseQuasitraceCarrier :
    Convex ℝ (normalizedFiniteBaseQuasitraceCarrier (A := A)) :=
  convex_normalizedFiniteQuasitraceCarrier.linear_image finiteQuasitraceBaseMap

theorem normalizedFiniteBaseQuasitraceCarrier_subset :
    normalizedFiniteBaseQuasitraceCarrier (A := A) ⊆ normalizedBaseQuasitraceCarrier := by
  intro g hg
  obtain ⟨F,hmono,hF,rfl⟩ := (mem_normalizedFiniteBaseQuasitraceCarrier g).mp hg
  exact (mem_normalizedBaseQuasitraceCarrier _).mpr
    ⟨F.toTwoQuasitrace,F.toTwoQuasitrace_unit hF,rfl⟩

theorem normalizedFiniteBaseQuasitraceCarrier_eq_closure_extremePoints :
    normalizedFiniteBaseQuasitraceCarrier (A := A) =
      closure (convexHull ℝ ((normalizedFiniteBaseQuasitraceCarrier (A := A)).extremePoints ℝ)) :=
  (closure_convexHull_extremePoints isCompact_normalizedFiniteBaseQuasitraceCarrier
    convex_normalizedFiniteBaseQuasitraceCarrier).symm

theorem finiteQuasitrace_additive_of_base_extremePoints
    (hext : (normalizedFiniteBaseQuasitraceCarrier (A := A)).extremePoints ℝ ⊆
      additiveQuasitraceFunctions)
    (F : CompatibleFiniteQuasitrace A)
    (hmono : ∀ n, Monotone (fun a : Positive (FinMatrix A n) => (F.level n a.1).re))
    (hF : F.level 1 1=1) :
    ∀ a b, F.toTwoQuasitrace.base (a+b)=F.toTwoQuasitrace.base a+F.toTwoQuasitrace.base b := by
  have hs : normalizedFiniteBaseQuasitraceCarrier (A := A) ⊆ additiveQuasitraceFunctions := by
    rw [normalizedFiniteBaseQuasitraceCarrier_eq_closure_extremePoints]
    exact closure_minimal (convexHull_min hext convex_additiveQuasitraceFunctions)
      isClosed_additiveQuasitraceFunctions
  exact hs ((mem_normalizedFiniteBaseQuasitraceCarrier _).mpr ⟨F,hmono,hF,rfl⟩)
end CuntzPureness

end

end OAI
