import OAI.Analysis.IrrationalRotation.Sampling.SeparatedCharacterFrequencies
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Topology.MetricSpace.Equicontinuity

namespace OAI

noncomputable section

namespace Invariant233
namespace CharacterWeakConvergence

open MeasureTheory Filter Set
open scoped Topology NNReal

section Integral
variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
  [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsProbabilityMeasure μ]

def pullbackIntegral (φ : C(X, Y)) : C(Y, ℂ) →L[ℂ] ℂ :=
  let L : C(Y, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ x, f (φ x) ∂μ
      map_add' := by
        intro f g
        exact integral_add
          (f.continuous.comp φ.continuous |>.integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _))
          (g.continuous.comp φ.continuous |>.integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _))
      map_smul' := by
        intro c f
        simp only [ContinuousMap.smul_apply, integral_smul, RingHom.id_apply] }
  L.mkContinuous 1 (fun f => by
    have h := norm_integral_le_of_norm_le_const
      (μ := μ) (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm (φ x)))
    change ‖∫ x, f (φ x) ∂μ‖ ≤ 1 * ‖f‖
    simpa using h)

@[simp] theorem pullbackIntegral_apply (φ : C(X, Y)) (f : C(Y, ℂ)) :
    pullbackIntegral μ φ f = ∫ x, f (φ x) ∂μ := rfl

theorem pullbackIntegral_norm_le (φ : C(X, Y)) : ‖pullbackIntegral μ φ‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  have h := norm_integral_le_of_norm_le_const
    (μ := μ) (Filter.Eventually.of_forall (fun x => f.norm_coe_le_norm (φ x)))
  simpa using h

end Integral

theorem tendsto_of_dense_span
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : ℕ → E →L[ℂ] ℂ) (M : E →L[ℂ] ℂ) (C : ℝ≥0)
    (hL : ∀ n, ‖L n‖₊ ≤ C) (s : Set E)
    (hs : (Submodule.span ℂ s).topologicalClosure = ⊤)
    (hconv : ∀ f ∈ s, Tendsto (fun n => L n f) atTop (𝓝 (M f)))
    (f : E) : Tendsto (fun n => L n f) atTop (𝓝 (M f)) := by
  let S : Submodule ℂ E :=
    { carrier := {f | Tendsto (fun n => L n f) atTop (𝓝 (M f))}
      zero_mem' := by simp
      add_mem' := by
        intro f g hf hg
        simpa only [Set.mem_ofPred_eq, map_add] using hf.add hg
      smul_mem' := by
        intro c f hf
        simpa only [Set.mem_ofPred_eq, map_smul] using hf.const_smul c }
  have hclosed : IsClosed (S : Set E) := by
    apply Equicontinuous.isClosed_setOfPred_tendsto _ M.continuous
    exact (LipschitzWith.uniformEquicontinuous (fun n => (L n : E → ℂ)) C
      (fun n => (L n).lipschitzWith.weaken (hL n))).equicontinuous
  have hsS : Submodule.span ℂ s ≤ S := Submodule.span_le.mpr hconv
  have htop : (⊤ : Submodule ℂ E) ≤ S := by
    rw [← hs]
    exact Submodule.topologicalClosure_minimal _ hsS hclosed
  exact htop (Submodule.mem_top)

local instance circleVolumeProbability :
    IsProbabilityMeasure (volume : Measure (AddCircle (1 : ℝ))) :=
  ⟨by simp [AddCircle.measure_univ]⟩

theorem integral_mFourier_eq_zero {m : ℕ} {v : Fin m → ℤ} (hv : v ≠ 0) :
    (∫ y : UnitAddTorus (Fin m), UnitAddTorus.mFourier v y) = 0 := by
  change (∫ y : Fin m → AddCircle (1 : ℝ), ∏ i, fourier (v i) (y i)) = 0
  rw [integral_fintype_prod_volume_eq_prod]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (SeparatedCharacterFrequencies.integral_fourier_eq_zero hi)

theorem tendsto_integral_joint_characters
    (q : ℕ → ℕ → ℕ) (m : ℕ)
    (hq : ∀ j i, 0 < q j i) (hmono : ∀ j, Monotone (q j))
    (hgap : ∀ i, i + 1 < m → Tendsto
      (fun j => (q j (i + 1) : ℝ) / (q j i : ℝ)) atTop atTop)
    (f : C(UnitAddTorus (Fin m), ℂ)) :
    Tendsto (fun j => ∫ x : AddCircle (1 : ℝ),
      f (fun i : Fin m => (q j i.val : ℤ) • x)) atTop
      (𝓝 (∫ y : UnitAddTorus (Fin m), f y)) := by
  let φ : ℕ → C(AddCircle (1 : ℝ), UnitAddTorus (Fin m)) := fun j =>
    ⟨fun x i => (q j i.val : ℤ) • x, by fun_prop⟩
  let L : ℕ → C(UnitAddTorus (Fin m), ℂ) →L[ℂ] ℂ :=
    fun j => pullbackIntegral volume (φ j)
  let M : C(UnitAddTorus (Fin m), ℂ) →L[ℂ] ℂ :=
    pullbackIntegral volume (ContinuousMap.id _)
  have hL : ∀ j, ‖L j‖₊ ≤ (1 : ℝ≥0) := by
    intro j
    exact_mod_cast pullbackIntegral_norm_le volume (φ j)
  have hconv : ∀ g ∈ Set.range (UnitAddTorus.mFourier (d := Fin m)),
      Tendsto (fun j => L j g) atTop (𝓝 (M g)) := by
    rintro _ ⟨v, rfl⟩
    by_cases hv : v = 0
    · subst v
      simp only [UnitAddTorus.mFourier_zero]
      simp [L, M, pullbackIntegral_apply]
    · let v' : ℕ → ℤ := fun n => if h : n < m then v ⟨n, h⟩ else 0
      have hv' : ∃ i < m, v' i ≠ 0 := by
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
        refine ⟨i.val, i.isLt, ?_⟩
        simpa [v'] using hi
      have hprod : ∀ j (x : AddCircle (1 : ℝ)),
          UnitAddTorus.mFourier v (φ j x) =
            ∏ i ∈ Finset.range m, fourier (v' i) ((q j i : ℤ) • x) := by
        intro j x
        change (∏ i : Fin m, fourier (v i) ((q j i.val : ℤ) • x)) = _
        simpa [v'] using Fin.prod_univ_eq_prod_range
          (fun i => fourier (v' i) ((q j i : ℤ) • x)) m
      have hevent : ∀ᶠ j in atTop, L j (UnitAddTorus.mFourier v) = 0 := by
        filter_upwards [SeparatedCharacterFrequencies.eventually_integral_product_fourier_eq_zero
          v' q m hq hmono hgap hv'] with j hj
        change (∫ x : AddCircle (1 : ℝ), UnitAddTorus.mFourier v (φ j x)) = 0
        simpa only [hprod] using hj
      have hM : M (UnitAddTorus.mFourier v) = 0 := integral_mFourier_eq_zero hv
      rw [hM]
      exact tendsto_const_nhds.congr' (hevent.mono fun _ h => h.symm)
  exact tendsto_of_dense_span L M 1 hL _
    UnitAddTorus.span_mFourier_closure_eq_top hconv f

end CharacterWeakConvergence
end Invariant233

end

end OAI
