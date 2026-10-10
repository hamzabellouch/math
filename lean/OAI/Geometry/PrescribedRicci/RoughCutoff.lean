import Mathlib
import OAI.Geometry.PrescribedRicci.ChartSobolevAlgebra

namespace OAI

/-! Rough Cutoff. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory TemperedDistribution LineDeriv
open scoped SchwartzMap BoundedContinuousFunction ContDiff Classical ComplexOrder MatrixOrder
namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def cutoffTerm (k : ℕ) (hk : Module.finrank ℝ E < k) (κ : 𝓢(E,ℂ))
    (v w : E) (u : L2 E) : L2 E :=
  productCoord k hk (schwartzCoord (k:ℝ) (∂_{v} κ)) (derivativeCoord ((k:ℝ)+1) w u) +
  productCoord k hk (schwartzCoord (k:ℝ) (∂_{w} κ)) (derivativeCoord ((k:ℝ)+1) v u) +
  productCoord k hk (schwartzCoord (k:ℝ) (∂_{v} (∂_{w} κ)))
    (lowerCoord ((k:ℝ)+1) (k:ℝ) (by linarith) u)

lemma cutoffTerm_continuous (k : ℕ) (hk : Module.finrank ℝ E < k) (κ : 𝓢(E,ℂ))
    (v w : E) : Continuous (cutoffTerm k hk κ v w) := by
  unfold cutoffTerm
  fun_prop

lemma cutoffTerm_schwartz (k : ℕ) (hk : Module.finrank ℝ E < k) (κ f : 𝓢(E,ℂ))
    (v w : E) : cutoffTerm k hk κ v w (schwartzCoord ((k:ℝ)+1) f) =
    schwartzCoord (k:ℝ)
      (SchwartzMap.smulLeftCLM ℂ (∂_{v} κ : 𝓢(E,ℂ)) (∂_{w} f) +
        SchwartzMap.smulLeftCLM ℂ (∂_{w} κ : 𝓢(E,ℂ)) (∂_{v} f) +
        SchwartzMap.smulLeftCLM ℂ (∂_{v} (∂_{w} κ) : 𝓢(E,ℂ)) f) := by
  simp only [cutoffTerm,derivativeCoord_schwartz,add_sub_cancel_right,
    lowerCoord_schwartz,productCoord_schwartz,schwartzCoord_add]

end SobolevChart
namespace MetricLocalization
open EllipticKernel SobolevChart FrozenPoisson
variable {n : ℕ}

def roughCutoff (H : Matrix (Fin n) (Fin n) ℂ) (k : ℕ)
    (hk : Module.finrank ℝ (EC n) < k) (κ : 𝓢(EC n,ℂ))
    (a : BasisIndex n → BasisIndex n → L2 (EC n)) (u : L2 (EC n)) : L2 (EC n) :=
  ∑ i, ∑ j, (
    (traceBilin H (rankTwo (stdOrthonormalBasis ℝ (EC n) i)
      (stdOrthonormalBasis ℝ (EC n) j)) : ℂ) •
        cutoffTerm k hk κ (stdOrthonormalBasis ℝ (EC n) i) (stdOrthonormalBasis ℝ (EC n) j) u +
    productCoord k hk (a i j)
      (cutoffTerm k hk κ (stdOrthonormalBasis ℝ (EC n) i) (stdOrthonormalBasis ℝ (EC n) j) u))

lemma roughCutoff_continuous (H : Matrix (Fin n) (Fin n) ℂ) (k : ℕ)
    (hk : Module.finrank ℝ (EC n) < k) (κ : 𝓢(EC n,ℂ)) :
    Continuous (fun p : (BasisIndex n → BasisIndex n → L2 (EC n)) × L2 (EC n) =>
      roughCutoff H k hk κ p.1 p.2) := by
  unfold roughCutoff
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  let T := (BasisIndex n → BasisIndex n → L2 (EC n)) × L2 (EC n)
  have hc : Continuous (fun p : T => cutoffTerm k hk κ
      (stdOrthonormalBasis ℝ (EC n) i) (stdOrthonormalBasis ℝ (EC n) j) p.2) :=
    (cutoffTerm_continuous k hk κ _ _).comp continuous_snd
  have ha : Continuous (fun p : T => p.1 i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_fst)
  exact (hc.const_smul (traceBilin H (rankTwo (stdOrthonormalBasis ℝ (EC n) i)
    (stdOrthonormalBasis ℝ (EC n) j)) : ℂ)).add (((productCoord k hk).continuous.comp ha).clm_apply hc)

lemma roughCutoff_schwartz (H : Matrix (Fin n) (Fin n) ℂ) (k : ℕ)
    (hk : Module.finrank ℝ (EC n) < k) (κ f : 𝓢(EC n,ℂ))
    (a : SmoothCoefficients (BasisIndex n) (EC n)) :
    roughCutoff H k hk κ (fun i j => schwartzCoord (k:ℝ) (a i j))
      (schwartzCoord ((k:ℝ)+1) f) =
    schwartzCoord (k:ℝ) (schwartzCutoffError (extendedCoefficient H (coefficientBCF a)) κ f) := by
  rw [schwartzCutoffError_firstOrder _
    (extendedCoefficient_temperate H _ (fun i j => (a i j).hasTemperateGrowth))]
  simp only [roughCutoff,cutoffTerm_schwartz,productCoord_schwartz,
    schwartzCoord_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← schwartzCoord_smul,← schwartzCoord_add]
  congr 1
  ext x
  simp only [add_apply,smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply
      (SchwartzMap.smulLeftCLM ℂ _ _).hasTemperateGrowth]
  simp only [add_apply,smul_eq_mul,
    SchwartzMap.smulLeftCLM_apply_apply (extendedCoefficient_temperate H (coefficientBCF a)
      (fun i j => (a i j).hasTemperateGrowth) i j),
    SchwartzMap.smulLeftCLM_apply_apply (a i j).hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply (∂_{stdOrthonormalBasis ℝ (EC n) i} κ).hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply (∂_{stdOrthonormalBasis ℝ (EC n) j} κ).hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply (∂_{stdOrthonormalBasis ℝ (EC n) i}
      (∂_{stdOrthonormalBasis ℝ (EC n) j} κ)).hasTemperateGrowth]
  simp only [extendedCoefficient,BoundedContinuousFunction.add_apply,BoundedContinuousFunction.const_apply]
  change _ = ((traceBilin H (rankTwo _ _) : ℂ)+a i j x) * _ * _ +
    ((traceBilin H (rankTwo _ _) : ℂ)+a i j x) * _ * _ +
    ((traceBilin H (rankTwo _ _) : ℂ)+a i j x) * _ * _
  ring

end MetricLocalization

end
end

end OAI
