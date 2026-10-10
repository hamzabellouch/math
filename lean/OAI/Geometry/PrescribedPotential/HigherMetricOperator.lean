import Mathlib
import OAI.Geometry.PrescribedPotential.CompletedResolvent
import OAI.Geometry.PrescribedPotential.CutoffHigher
import OAI.Geometry.PrescribedPotential.GlobalParametrix

namespace OAI

/-! Higher Metric Operator. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory TemperedDistribution LineDeriv
open scoped SchwartzMap ContDiff Classical BoundedContinuousFunction
namespace MetricLocalization
open EllipticKernel SobolevChart
variable {n : ℕ}

lemma differential_cutoff_bound_integer
    (c : BasisIndex n → BasisIndex n → EC n →ᵇ ℂ)
    (hc : ∀ i j, (c i j : EC n → ℂ).HasTemperateGrowth) (κ : 𝓢(EC n, ℂ)) (k : ℕ) :
    CoreBound ((k : ℝ)+2) (k : ℝ) (fun f =>
      schwartzDifferential c (SchwartzMap.smulLeftCLM ℂ κ f)) := by
  have hd (i j : BasisIndex n) : CoreBound ((k : ℝ)+2) (k : ℝ) (fun f =>
      SchwartzMap.smulLeftCLM ℂ (c i j) (∂_{stdOrthonormalBasis ℝ (EC n) i}
        (∂_{stdOrthonormalBasis ℝ (EC n) j} (SchwartzMap.smulLeftCLM ℂ κ f)))) := by
    simp_rw [schwartz_second_product, map_add, schwartz_product_assoc (hc i j)]
    apply CoreBound.add
    · exact (coreBound_product_integer _ k).comp
        ((coreBound_deriv _ (s := (k : ℝ)+1) (t := (k : ℝ)) (by linarith)).comp
          (coreBound_deriv _ (s := (k : ℝ)+2) (t := (k : ℝ)+1) (by linarith)))
    · apply CoreBound.add
      · apply CoreBound.add
        · exact (coreBound_product_integer _ k).comp
            (coreBound_deriv _ (s := (k : ℝ)+2) (t := (k : ℝ)) (by linarith))
        · exact (coreBound_product_integer _ k).comp
            (coreBound_deriv _ (s := (k : ℝ)+2) (t := (k : ℝ)) (by linarith))
      · exact (coreBound_product_integer _ k).comp (CoreBound.id (by linarith))
  change CoreBound ((k : ℝ)+2) (k : ℝ) (fun f => schwartzDifferential c (SchwartzMap.smulLeftCLM ℂ κ f))
  simp only [schwartzDifferential, sum_apply,
    ContinuousLinearMap.comp_apply, lineDerivOpCLM_apply]
  exact CoreBound.sum Finset.univ _ (fun i _ => CoreBound.sum Finset.univ _ (fun j _ => hd i j))
end MetricLocalization

namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart MetricLocalization
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)

lemma complexL_piece_bound_integer (k : ℕ) (p : ι) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Smooth A,
      ‖D.localizers.embed (k : ℝ) (globalize (D.patch p).index (D.outerCutoff p)
        ((D.patch p).differential (SchwartzMap.smulLeftCLM ℂ (D.cutoff p).val (D.forcing p f))))‖ ≤
        C*‖D.localizers.embed ((k : ℝ)+2) f‖ := by
  obtain ⟨B,hB,hb⟩ := globalize_integer_bound D.localizers (D.patch p).index (D.outerCutoff p) k
  obtain ⟨C,hC,hc⟩ := differential_cutoff_bound_integer (D.patch p).coefficients
    (D.patch p).coefficients_temperate (D.cutoff p).val k
  refine ⟨B*C,mul_nonneg hB hC,fun f => ?_⟩
  apply (hb ((D.patch p).differential (SchwartzMap.smulLeftCLM ℂ (D.cutoff p).val (D.forcing p f)))).trans
  have hr := (hc (D.forcing p f)).trans
    (mul_le_mul_of_nonneg_left (D.forcing_bound p ((k : ℝ)+2) f) hC)
  simpa only [mul_assoc, ParametrixPatch.differential] using mul_le_mul_of_nonneg_left hr hB

lemma complexL_bound_integer (k : ℕ) :
    D.localizers.BoundedCore ((k : ℝ)+2) (k : ℝ) (complexL g) := by
  choose C hC hc using D.complexL_piece_bound_integer k
  refine ⟨∑ p,C p,Finset.sum_nonneg (fun p _ => hC p),fun f => ?_⟩
  rw [D.complexL_reconstruction, map_sum, Finset.sum_mul]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun p _ => hc p f))

def completedLOrder (k : ℕ) : D.localizers.Sobolev ((k : ℝ)+2) →L[ℝ] D.localizers.Sobolev (k : ℝ) :=
  D.localizers.extendCore ((k : ℝ)+2) (k : ℝ) (complexL g)

lemma completedLOrder_embed (k : ℕ) (f : Smooth A) :
    D.completedLOrder k (D.localizers.embed ((k : ℝ)+2) f) = D.localizers.embed (k : ℝ) (complexL g f) :=
  D.localizers.extendCore_embed (D.complexL_bound_integer k) f

lemma completedLOrder_lower (k : ℕ) (u : D.localizers.Sobolev ((k : ℝ)+2)) :
    D.localizers.lower (k : ℝ) 0 (D.completedLOrder k u) =
      D.completedL (D.localizers.lower ((k : ℝ)+2) 2 u) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  change D.localizers.lower (k : ℝ) 0 (D.localizers.extendCore _ _ _ u) = _
  rw [D.localizers.lower_extendCore hk _ (D.complexL_bound_integer k)
    ((D.complexL_bound_integer k).target_mono hk)]
  exact (D.localizers.extendCore_lower (by linarith) (complexL g) D.complexL_bound
    ((D.complexL_bound_integer k).target_mono hk) u).symm
end GluingData
end GlobalElliptic

end
end

end OAI
