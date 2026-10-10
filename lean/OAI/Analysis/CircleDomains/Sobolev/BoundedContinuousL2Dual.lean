import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Isomorphisms

namespace OAI

/-! The L² representation of a functional on bounded continuous tests.
Only the bound through their actual L² image is required. -/
open Set Filter MeasureTheory
open scoped BoundedContinuousFunction ENNReal
noncomputable section
namespace CircleDomainRigidity

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

lemma exists_L2_pairing_of_boundedContinuous_bound
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ]
    (F : (Z →ᵇ ℝ) →ₗ[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hF : ∀ f, F f ≤ C * ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖) :
    ∃ g : Lp ℝ 2 σ, ‖g‖ ≤ C ∧
      ∀ f : Z →ᵇ ℝ, (∫ z, g z * f z ∂σ) = F f := by
  let Q : (Z →ᵇ ℝ) →ₗ[ℝ] Lp ℝ 2 σ :=
    (BoundedContinuousFunction.toLp 2 σ ℝ).toLinearMap
  have hbound (f : Z →ᵇ ℝ) : ‖F f‖ ≤ C * ‖Q f‖ := by
    rw [Real.norm_eq_abs,abs_le]
    refine ⟨?_,hF f⟩
    have hn := hF (-f)
    change -(C * ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖) ≤ F f
    simpa only [map_neg,norm_neg,neg_neg] using neg_le_neg hn
  have hk : Q.ker ≤ F.ker := by
    intro f hf
    change Q f = 0 at hf
    change F f = 0
    have hn := hbound f
    rw [hf,norm_zero,mul_zero] at hn
    exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
  let L : Q.range →ₗ[ℝ] ℝ :=
    ((Q.ker).liftQ F hk).comp Q.quotKerEquivRange.symm.toLinearMap
  have hL (f : Z →ᵇ ℝ) : L ⟨Q f,LinearMap.mem_range_self Q f⟩ = F f := by
    simp [L]
  have hLb (v : Q.range) : ‖L v‖ ≤ C * ‖v‖ := by
    obtain ⟨f,hf⟩ := v.property
    have hv : v = ⟨Q f,LinearMap.mem_range_self Q f⟩ := Subtype.ext hf.symm
    rw [hv,hL]
    exact hbound f
  let Lc : Q.range →L[ℝ] ℝ := L.mkContinuous C hLb
  obtain ⟨G,hG,hGn⟩ := exists_extension_norm_eq Q.range Lc
  let g : Lp ℝ 2 σ := (InnerProductSpace.toDual ℝ (Lp ℝ 2 σ)).symm G
  refine ⟨g,?_,?_⟩
  · have hnorm : ‖Lc‖ ≤ C := Lc.opNorm_le_bound hC hLb
    calc
      ‖g‖ = ‖G‖ := (InnerProductSpace.toDual ℝ (Lp ℝ 2 σ)).symm.norm_map G
      _ = ‖Lc‖ := hGn
      _ ≤ C := hnorm
  · intro f
    have hq : Q f =ᵐ[σ] f := BoundedContinuousFunction.coeFn_toLp 2 σ ℝ f
    calc
      (∫ z, g z * f z ∂σ) = inner ℝ g (Q f) := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hq] with z hz
        simp only [Real.inner_apply,hz]
      _ = G (Q f) := InnerProductSpace.toDual_symm_apply
      _ = Lc ⟨Q f,LinearMap.mem_range_self Q f⟩ := hG ⟨Q f,LinearMap.mem_range_self Q f⟩
      _ = F f := hL f

end CircleDomainRigidity

end

end OAI
