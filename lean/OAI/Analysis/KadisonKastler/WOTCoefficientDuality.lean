import OAI.Analysis.KadisonKastler.FiniteCoefficientFactorization
import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
import Mathlib.Analysis.LocallyConvex.WeakDual

namespace OAI

/-! # Finite coefficient form of a weak-operator continuous functional

The defining weak topology first gives a finite coefficient expression.
Finite polar duality then chooses coefficients with sharp Hilbert norms.
-/

namespace KadisonKastler

open scoped BigOperators InnerProductSpace

noncomputable section

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem wot_functional_finite_coefficients (f : (H →WOT[ℂ] H) →L[ℂ] ℂ) :
    ∃ (ι : Type u) (_ : Fintype ι) (x y : ι → H),
      f.comp (ContinuousLinearMap.WOTofCLM (𝕜₂ := ℂ)) = finiteOperatorCoefficient x y := by
  classical
  let v : (H × StrongDual ℂ H) → (H →WOT[ℂ] H) →ₗ[ℂ] ℂ :=
    fun p => (LinearMap.proj p).comp (ContinuousLinearMapWOT.inducingFn (RingHom.id ℂ) H H)
  have hspan : f.toLinearMap ∈ Submodule.span ℂ (Set.range v) := by
    rw [LinearMap.mem_span_iff_continuous]
    have ht : (⨅ p, TopologicalSpace.induced (v p) inferInstance) =
        ContinuousLinearMapWOT.instTopologicalSpace (σ := RingHom.id ℂ) (E := H) (F := H) := by
      change _ = TopologicalSpace.induced
        (ContinuousLinearMapWOT.inducingFn (RingHom.id ℂ) H H) _
      rw [induced_to_pi]
      rfl
    rw [ht]
    exact f.continuous
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hspan
  let x : c.support → H := fun p => c p • p.val.1
  let y : c.support → H := fun p => (InnerProductSpace.toDual ℂ H).symm p.val.2
  refine ⟨↥c.support, inferInstance, x, y, ?_⟩
  apply ContinuousLinearMap.ext
  intro S
  have h := congrArg (fun g : (H →WOT[ℂ] H) →ₗ[ℂ] ℂ =>
    g (ContinuousLinearMapWOT.ofCLM S)) hc
  rw [Finsupp.sum, LinearMap.sum_apply] at h
  rw [← Finset.sum_coe_sort] at h
  change (∑ p : c.support, c p * p.val.2 (S p.val.1)) =
    f (ContinuousLinearMapWOT.ofCLM S) at h
  change f (ContinuousLinearMapWOT.ofCLM S) = _
  rw [← h, finiteOperatorCoefficient_apply]
  apply Finset.sum_congr rfl
  intro p _
  change c p * p.val.2 (S p.val.1) =
    inner ℂ ((InnerProductSpace.toDual ℂ H).symm p.val.2) (S (c p • p.val.1))
  rw [map_smul, inner_smul_right]
  congr 1
  have he := congrArg (fun g : StrongDual ℂ H => g (S p.val.1))
    ((InnerProductSpace.toDual ℂ H).apply_symm_apply p.val.2)
  exact he.symm

theorem wot_functional_sharp_coefficients (f : (H →WOT[ℂ] H) →L[ℂ] ℂ) :
    ∃ (n : ℕ) (x y : Fin n → H),
      f.comp (ContinuousLinearMap.WOTofCLM (𝕜₂ := ℂ)) = finiteOperatorCoefficient x y ∧
      (∑ i, ‖x i‖ ^ 2) ≤ ‖f.comp (ContinuousLinearMap.WOTofCLM (𝕜₂ := ℂ))‖ ∧
      (∑ i, ‖y i‖ ^ 2) ≤ ‖f.comp (ContinuousLinearMap.WOTofCLM (𝕜₂ := ℂ))‖ := by
  obtain ⟨ι, hι, a, b, hab⟩ := wot_functional_finite_coefficients f
  let := hι
  rw [hab]
  exact finite_coefficient_factorization a b

end

end KadisonKastler

end OAI
