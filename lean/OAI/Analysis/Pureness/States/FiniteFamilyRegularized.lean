import OAI.Analysis.Pureness.States.FiniteFamilyPullback

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup
open scoped NNReal ENNReal CStarAlgebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma finiteSpectralQuasitraceFamily_monotone
    (d : finiteCuntzSubmonoid (A := A) →+ ℝ≥0∞) (hd : Monotone d)
    (hlsc : ∀ n, LowerSemicontinuous (fun M : Positive (FinMatrix A n) => d (finitePositiveClass n M)))
    (hfinite : ∀ x, d x ≠ ⊤) (n : ℕ) :
    Monotone (fun a : Positive (FinMatrix A n) =>
      ((finiteSpectralQuasitraceFamily d hd hlsc hfinite).level n a.1).re) := by
  intro a b hab
  simp only [finiteSpectralQuasitraceFamily_positive,Complex.ofReal_re]
  exact (finiteSpectralPositiveQuasitrace d hd hlsc hfinite n).monotone hab

variable [Nontrivial A]
variable (hsimple : TopologicallySimple A) (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)

def normalizedRegularizedStateFiniteFamily : CompatibleFiniteQuasitrace A :=
  (finiteSpectralQuasitraceFamily (regularizedFiniteDimension f.toAddHom f.monotone)
    (regularizedFiniteDimension_monotone f.toAddHom f.monotone)
    (regularizedState_dimension_lsc y f) (regularizedState_dimension_finite hsimple y hy f)).scale
    ⟨(regularizedFiniteDimension f.toAddHom f.monotone finiteUnitClass).toReal⁻¹,
      inv_nonneg.mpr ENNReal.toReal_nonneg⟩

omit [Nontrivial A] in
lemma normalizedRegularizedStateFiniteFamily_monotone (n : ℕ) :
    Monotone (fun a : Positive (FinMatrix A n) =>
      ((normalizedRegularizedStateFiniteFamily hsimple y hy f).level n a.1).re) :=
  CompatibleFiniteQuasitrace.scale_monotone _
    (finiteSpectralQuasitraceFamily_monotone _ _ _ _) _ n

omit [Nontrivial A] in
lemma normalizedRegularizedStateFiniteFamily_base (x : A) :
    (normalizedRegularizedStateFiniteFamily hsimple y hy f).toTwoQuasitrace.base x =
      (normalizedRegularizedStateTwoQuasitrace hsimple y hy f).base x := by
  change (((regularizedFiniteDimension f.toAddHom f.monotone finiteUnitClass).toReal⁻¹ : ℝ) : ℂ)*
    (finiteSpectralPositiveQuasitrace _ _ _ _ 1).complexValue (scalarMatrixHom x) =
      (((regularizedFiniteDimension f.toAddHom f.monotone finiteUnitClass).toReal⁻¹ : ℝ) : ℂ)*
        ((finiteSpectralPositiveQuasitrace _ _ _ _ 1).comap
          (scalarMatrixHom (ι := Fin 1)).toNonUnitalStarAlgHom).complexValue x
  rw [PositiveQuasitrace.comap_complexValue]
  rfl

lemma normalizedRegularizedStateFiniteFamily_unit :
    (normalizedRegularizedStateFiniteFamily hsimple y hy f).level 1 1=1 := by
  have h := normalizedRegularizedStateFiniteFamily_base hsimple y hy f 1
  rw [normalizedRegularizedStateTwoQuasitrace_unit] at h
  change (normalizedRegularizedStateFiniteFamily hsimple y hy f).level 1 (scalarMatrixHom 1)=1 at h
  rwa [map_one] at h

theorem normalizedRegularizedState_mem_finiteBaseCarrier :
    (normalizedRegularizedStateTwoQuasitrace hsimple y hy f).base.toFun ∈
      normalizedFiniteBaseQuasitraceCarrier :=
  (mem_normalizedFiniteBaseQuasitraceCarrier _).mpr
    ⟨normalizedRegularizedStateFiniteFamily hsimple y hy f,
      normalizedRegularizedStateFiniteFamily_monotone hsimple y hy f,
      normalizedRegularizedStateFiniteFamily_unit hsimple y hy f,
      funext (normalizedRegularizedStateFiniteFamily_base hsimple y hy f)⟩

theorem normalizedRegularizedState_additive_of_finiteBase_extremePoints
    (hext : (normalizedFiniteBaseQuasitraceCarrier (A := A)).extremePoints ℝ ⊆
      additiveQuasitraceFunctions) :
    ∀ a b, (normalizedRegularizedStateTwoQuasitrace hsimple y hy f).base (a+b)=
      (normalizedRegularizedStateTwoQuasitrace hsimple y hy f).base a+
      (normalizedRegularizedStateTwoQuasitrace hsimple y hy f).base b := by
  have h := finiteQuasitrace_additive_of_base_extremePoints hext
    (normalizedRegularizedStateFiniteFamily hsimple y hy f)
    (normalizedRegularizedStateFiniteFamily_monotone hsimple y hy f)
    (normalizedRegularizedStateFiniteFamily_unit hsimple y hy f)
  simpa only [normalizedRegularizedStateFiniteFamily_base] using h
end CuntzPureness

end

end OAI
