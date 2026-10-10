import Mathlib
import OAI.Computability.VertexCover.Analysis.IntegralUpdate
import OAI.Computability.VertexCover.Analysis.Restriction

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.Restriction
open MeasureTheory
open scoped BigOperators

namespace EnergyForm

section Integral
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]

theorem continuous_integrable (f : C(X, ℝ)) : Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem continuous_mul_integrable (f g : C(X, ℝ)) :
    Integrable (fun x => f x * g x) μ :=
  (f.continuous.mul g.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

noncomputable def integral : EnergyForm C(X, ℝ) where
  form :=
    { toFun := fun f =>
        { toFun := fun g => ∫ x, f x * g x ∂μ
          map_add' := fun g h => by
            simp only [ContinuousMap.add_apply, mul_add]
            exact integral_add (continuous_mul_integrable μ f g)
              (continuous_mul_integrable μ f h)
          map_smul' := fun a g => by
            simp only [ContinuousMap.smul_apply, smul_eq_mul]
            simp_rw [mul_left_comm (f _) a]
            exact integral_const_mul _ _ }
      map_add' := fun f g => by
        ext h
        simp only [LinearMap.add_apply, ContinuousMap.add_apply, add_mul]
        exact integral_add (continuous_mul_integrable μ f h)
          (continuous_mul_integrable μ g h)
      map_smul' := fun a f => by
        ext g
        simp only [LinearMap.smul_apply, ContinuousMap.smul_apply, smul_eq_mul]
        simp_rw [mul_assoc]
        exact integral_const_mul _ _ }
  symm f g := by
    change (∫ x, f x * g x ∂μ) = ∫ x, g x * f x ∂μ
    simp only [mul_comm]
  nonneg f := integral_nonneg (fun x => mul_self_nonneg (f x))

@[simp] theorem integral_form (f g : C(X, ℝ)) :
    (integral μ).form f g = ∫ x, f x * g x ∂μ := rfl

@[simp] theorem integral_energy (f : C(X, ℝ)) :
    (integral μ).energy f = ∫ x, (f x)^2 ∂μ := by
  simp only [energy, integral_form, pow_two]

end Integral

namespace Projection
section Averaging
variable {ι X : Type*} [Fintype ι] [DecidableEq ι]
  [TopologicalSpace X] [CompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

noncomputable def updateFunction (i : ι) (f : C(ι → X, ℝ)) : C(X, C(ι → X, ℝ)) :=
  ContinuousMap.curry ⟨fun p : X × (ι → X) => f (Function.update p.2 i p.1),
    f.continuous.comp (continuous_snd.update i continuous_fst)⟩

omit [Fintype ι] [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [BorelSpace X] in
@[simp] theorem updateFunction_apply (i : ι) (f : C(ι → X, ℝ)) (x : X) (s : ι → X) :
    updateFunction i f x s = f (Function.update s i x) := rfl

omit [Fintype ι] [SecondCountableTopology X] in
theorem updateFunction_integrable (i : ι) (f : C(ι → X, ℝ)) :
    Integrable (updateFunction i f) μ :=
  (updateFunction i f).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

noncomputable def averageMap (i : ι) : C(ι → X, ℝ) →ₗ[ℝ] C(ι → X, ℝ) where
  toFun f := ∫ x, updateFunction i f x ∂μ
  map_add' f g := by
    have he : (fun x => updateFunction i (f + g) x) =
        (fun x => updateFunction i f x + updateFunction i g x) := by
      funext x
      ext s
      rfl
    rw [he, integral_add (updateFunction_integrable μ i f)
      (updateFunction_integrable μ i g)]
  map_smul' a f := by
    have he : (fun x => updateFunction i (a • f) x) =
        (fun x => a • updateFunction i f x) := by
      funext x
      ext s
      rfl
    rw [he, integral_smul]
    rfl

omit [Fintype ι] [SecondCountableTopology X] in
@[simp] theorem averageMap_apply (i : ι) (f : C(ι → X, ℝ)) (s : ι → X) :
    averageMap μ i f s = ∫ x, f (Function.update s i x) ∂μ :=
  ContinuousMap.integral_apply (updateFunction_integrable μ i f) s

omit [Fintype ι] [SecondCountableTopology X] in
theorem average_update (i : ι) (f : C(ι → X, ℝ)) (s : ι → X) (x : X) :
    averageMap μ i f (Function.update s i x) = averageMap μ i f s := by
  simp only [averageMap_apply, Function.update_idem]

omit [Fintype ι] [SecondCountableTopology X] in
theorem average_idem (i : ι) (f : C(ι → X, ℝ)) :
    averageMap μ i (averageMap μ i f) = averageMap μ i f := by
  ext s
  simp only [averageMap_apply, Function.update_idem]
  simp

theorem integral_average_mul_fixed (i : ι) (f g : C(ι → X, ℝ))
    (hg : ∀ s x, g (Function.update s i x) = g s) :
    (∫ s, averageMap μ i f s * g s ∂Measure.pi (fun _ : ι => μ)) =
      ∫ s, f s * g s ∂Measure.pi (fun _ : ι => μ) := by
  have hi : Integrable (fun p : (ι → X) × X =>
      f (Function.update p.1 i p.2) * g (Function.update p.1 i p.2))
      ((Measure.pi (fun _ : ι => μ)).prod μ) :=
    ((f.continuous.comp (continuous_fst.update i continuous_snd)).mul
      (g.continuous.comp (continuous_fst.update i continuous_snd))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ s, ∫ x, f (Function.update s i x) * g (Function.update s i x)
        ∂μ ∂Measure.pi (fun _ : ι => μ) := by
      simp only [hg, integral_mul_const, averageMap_apply]
    _ = ∫ x, ∫ s, f (Function.update s i x) * g (Function.update s i x)
        ∂Measure.pi (fun _ : ι => μ) ∂μ := integral_integral_swap hi
    _ = _ := VertexCover.Product.integral_update μ i (continuous_mul_integrable _ f g)

noncomputable def average (i : ι) :
    (integral (Measure.pi (fun _ : ι => μ))).Projection where
  toLinearMap := averageMap μ i
  idem := average_idem μ i
  selfAdjoint f g := by
    change (∫ s, averageMap μ i f s * g s ∂Measure.pi (fun _ : ι => μ)) =
      ∫ s, f s * averageMap μ i g s ∂Measure.pi (fun _ : ι => μ)
    have h₁ := integral_average_mul_fixed μ i g (averageMap μ i f)
      (average_update μ i f)
    have h₂ := integral_average_mul_fixed μ i f (averageMap μ i g)
      (average_update μ i g)
    calc
      _ = ∫ s, g s * averageMap μ i f s ∂Measure.pi (fun _ : ι => μ) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun s => mul_comm _ _)
      _ = ∫ s, averageMap μ i g s * averageMap μ i f s
          ∂Measure.pi (fun _ : ι => μ) := h₁.symm
      _ = ∫ s, averageMap μ i f s * averageMap μ i g s
          ∂Measure.pi (fun _ : ι => μ) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun s => mul_comm _ _)
      _ = _ := h₂

@[simp] theorem average_apply (i : ι) (f : C(ι → X, ℝ)) (s : ι → X) :
    average μ i f s = ∫ x, f (Function.update s i x) ∂μ := averageMap_apply μ i f s

theorem average_invariant (i : ι) (f : C(ι → X, ℝ)) (s : ι → X) (x : X) :
    average μ i f (Function.update s i x) = average μ i f s := average_update μ i f s x

theorem average_commute (i j : ι) (f : C(ι → X, ℝ)) :
    average μ i (average μ j f) = average μ j (average μ i f) := by
  by_cases hij : i = j
  · subst j
    rfl
  ext s
  simp only [average_apply]
  have hi : Integrable (fun p : X × X =>
      f (Function.update (Function.update s i p.1) j p.2)) (μ.prod μ) :=
    (f.continuous.comp ((continuous_const.update i continuous_fst).update j
      continuous_snd)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_integral_swap hi]
  simp only [Function.update_comm hij]

end Averaging
end Projection
end EnergyForm
end VertexCover.Restriction


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
