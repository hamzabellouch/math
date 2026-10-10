import OAI.Analysis.NuclearUltrapower.HilbertUltraproduct
import OAI.Analysis.KadisonSimilarity.FreeProduct.BaseCommutatorCompression

namespace OAI

/-! Coordinatewise commutator estimates pass to the Hilbert ultrapower,
and then to any reducing closed subspace. -/

noncomputable section
namespace KadisonSimilarity

open NuclearUltrapower
open scoped ENNReal

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual operator map on the Hilbert ultrapower respects commutators. -/
theorem hilbertUltraproduct_commutator (ω : Ultrafilter ι)
    (T X : lp (fun _ : ι => H →L[ℂ] H) ∞) :
    commutator (HilbertUltraproduct.map ω T) (HilbertUltraproduct.map ω X) =
      HilbertUltraproduct.map ω (T * X - X * T) := by
  change commutator (HilbertUltraproduct.operatorRep ω T)
    (HilbertUltraproduct.operatorRep ω X) =
      HilbertUltraproduct.operatorRep ω (T * X - X * T)
  simp only [commutator, map_sub, map_mul]

/-- Only an eventual coordinate bound is required, exactly as in the
small-corner lifting argument. -/
theorem norm_hilbertUltraproduct_commutator_le (ω : Ultrafilter ι)
    (T X : lp (fun _ : ι => H →L[ℂ] H) ∞) {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ᶠ i in (ω : Filter ι), ‖commutator (T i) (X i)‖ ≤ c) :
    ‖commutator (HilbertUltraproduct.map ω T) (HilbertUltraproduct.map ω X)‖ ≤ c := by
  rw [hilbertUltraproduct_commutator]
  apply HilbertUltraproduct.map_norm_le ω _ c hc
  exact hbound

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Compression to a reducing subspace preserves a commutator estimate.
The operator being tested need not preserve that subspace. -/
theorem norm_reducing_compression_commutator_le (V : K →ₗᵢ[ℂ] H)
    (T X : H →L[ℂ] H) (X₀ : K →L[ℂ] K)
    (hXV : X.comp V.toContinuousLinearMap = V.toContinuousLinearMap.comp X₀)
    (hXVstar : X.adjoint.comp V.toContinuousLinearMap =
      V.toContinuousLinearMap.comp X₀.adjoint)
    {c : ℝ} (hbound : ‖commutator T X‖ ≤ c) :
    ‖commutator (V.toContinuousLinearMap.adjoint.comp (T.comp V.toContinuousLinearMap)) X₀‖
      ≤ c := by
  have hAdj : V.toContinuousLinearMap.adjoint.comp X =
      X₀.comp V.toContinuousLinearMap.adjoint := by
    have h := congrArg ContinuousLinearMap.adjoint hXVstar
    simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint] using h
  have heq : commutator
      (V.toContinuousLinearMap.adjoint.comp (T.comp V.toContinuousLinearMap)) X₀ =
      V.toContinuousLinearMap.adjoint.comp ((commutator T X).comp V.toContinuousLinearMap) := by
    symm
    simp only [commutator, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_sub,
      ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_assoc]
    rw [hXV]
    simp only [← ContinuousLinearMap.comp_assoc]
    rw [hAdj]
  rw [heq]
  calc
    ‖V.toContinuousLinearMap.adjoint.comp ((commutator T X).comp V.toContinuousLinearMap)‖
        ≤ ‖V.toContinuousLinearMap.adjoint‖ *
          (‖commutator T X‖ * ‖V.toContinuousLinearMap‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖commutator T X‖ * 1) := by
      apply mul_le_mul
      · simpa only [ContinuousLinearMap.adjoint.norm_map] using V.norm_toContinuousLinearMap_le
      · exact mul_le_mul_of_nonneg_left V.norm_toContinuousLinearMap_le (norm_nonneg _)
      · positivity
      · norm_num
    _ ≤ c := by simpa only [one_mul, mul_one] using hbound

end KadisonSimilarity

end

end OAI
