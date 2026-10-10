import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.CascadeBlockLaw
import OAI.Probability.SKBarriers.Hierarchy.CascadeRebase
import OAI.Probability.SKBarriers.Replicas.ReplicaOverlap

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
open Matrix
attribute [local instance 1900] cascadeNormedGroup cascadeNormedSpace
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section CascadeBlockTrace
variable {E S : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype S] [Nonempty S]

theorem cascadeMean_regular {I : Type} (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (L : S → CascadeSpace E n →L[ℝ] ℝ) (v : S → I → ℝ)
    (hv : ∀ s i, |v s i| ≤ 1) (i : I) :
    Continuous (fun z => finiteMean (cascadeSpinWeight n m c L z) v i) ∧
      ∀ z, ‖finiteMean (cascadeSpinWeight n m c L z) v i‖ ≤ 1 := by
  constructor
  · simp only [finiteMean_apply]
    exact continuous_finsetSum _ (fun s _ => (cascadeSpinWeight_regular n m c L s).1.mul continuous_const)
  · intro z
    exact finiteMean_abs_le_one _ v (cascadeSpinWeight_nonneg n m c L z)
      (cascadeSpinWeight_sum n m c L z) hv i

theorem cascadeBlock_trace (N n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (L : S → CascadeSpace (CascadeSpace E N) n →L[ℝ] ℝ)
    (p a : ℝ) (hp : 0 < p) (ha : 0 < a) (hl : p ≤ 1)
    (hm : ∀ i, p ≤ m i) (hmu : ∀ i, m i ≤ 1) (hmono : Monotone m)
    (v : S → Fin N → ℝ) (hvb : ∀ s i, |v s i| ≤ 1)
    (hv : ∀ s i, L s (cascadeLift n (parameterNoise (E := E) N (coordinateAxis N i))) = a*v s i)
    (x : E) :
    let F := cascadePressure n m (affineLogPartition c L)
    let P := cascadeSpinWeight n m c L
    let W := fun s => cascadeMoment N (fun _ => p) F (fun z => P z s) x
    let C := finiteCovariance W v
    let X := fun i z => finiteMean (P z) v i
    (C*C).trace ≤ (N : ℝ)*(∑ i, (cascadeMoment N (fun _ => p) F (fun z => (X i z)^2) x-
      (cascadeMoment N (fun _ => p) F (X i) x)^2))+(N : ℝ)/(a^2*p^2) := by
  dsimp only
  let F := cascadePressure n m (affineLogPartition c L)
  let P := cascadeSpinWeight n m c L
  let X : Fin N → CascadeSpace E N → ℝ := fun i z => finiteMean (P z) v i
  let c' := rebaseConstants n c L (cascadeLift N x)
  let L' := rebaseLinears n L (parameterNoise (E := E) N)
  let F' := cascadePressure n m (affineLogPartition c' L')
  let P' := cascadeSpinWeight n m c' L'
  let μ := (fiberGaussian N 0).tilted (fun z => p*F' z)
  have hF : BoundedDerivs F := cascadePressure_boundedDerivs n m _ (affineLogPartition_boundedDerivs c L)
  have hF' : BoundedDerivs F' := cascadePressure_boundedDerivs n m _ (affineLogPartition_boundedDerivs c' L')
  let := fiberGaussian_tilted_probability N _ (hF'.const_mul p) 0
  have hFe (z : ParameterSpace N) : F' z = F (parameterEmbed N x z) := by
    rw [parameterEmbed_eq]
    exact cascadePressure_rebase n m c L (cascadeLift N x) (parameterNoise (E := E) N) z
  have hPe (z : ParameterSpace N) (s : S) : P' z s = P (parameterEmbed N x z) s := by
    rw [parameterEmbed_eq]
    exact cascadeSpinWeight_rebase n m c L (cascadeLift N x) (parameterNoise (E := E) N) z s
  have hM (g : CascadeSpace E N → ℝ) (hg : Continuous g) {B : ℝ} (hB : 0 ≤ B)
      (hb : ∀ z, ‖g z‖ ≤ B) :
      cascadeMoment N (fun _ => p) F g x = ∫ z, g (parameterEmbed N x z) ∂μ := by
    rw [cascadeMoment_const_integral N p F g hF hg hB hb x]
    congr 1
    exact congrArg (fun h => (fiberGaussian N 0).tilted h) (funext fun z => congrArg (p*·) (hFe z).symm)
  have hW : (fun s => cascadeMoment N (fun _ => p) F (fun z => P z s) x) = integratedWeights P' μ := by
    funext s
    rw [hM _ (cascadeSpinWeight_regular n m c L s).1 (by norm_num : (0 : ℝ) ≤ 1)
      (cascadeSpinWeight_regular n m c L s).2]
    exact integral_congr_ae (ae_of_all _ (fun z => (hPe z s).symm))
  have hX (i : Fin N) : MemLp (fun z => finiteMean (P' z) v i) 2 μ := by
    have hr := cascadeMean_regular n m c' L' v hvb i
    exact (HasExpGrowth.of_bounded (by norm_num : (0 : ℝ) ≤ 1) hr.2).memLp_two_tilted_fiberGaussian
      N _ (hF'.const_mul p) hr.1 0
  have hXe (i : Fin N) (z : ParameterSpace N) : finiteMean (P' z) v i = X i (parameterEmbed N x z) := by
    unfold X
    congr 2
    exact funext (hPe z)
  have hV : (covarianceMatrix (fun i z => finiteMean (P' z) v i) μ).trace =
      ∑ i, (cascadeMoment N (fun _ => p) F (fun z => (X i z)^2) x-
        (cascadeMoment N (fun _ => p) F (X i) x)^2) := by
    unfold Matrix.trace
    apply Finset.sum_congr rfl
    intro i _
    change cov[fun z => finiteMean (P' z) v i,fun z => finiteMean (P' z) v i;μ] = _
    rw [covariance_eq_sub (hX i) (hX i)]
    have R := cascadeMean_regular n m c L v hvb i
    have hxc : Continuous (X i) := R.1
    have hxsc : Continuous (fun z => (X i z)^2) := hxc.pow 2
    rw [hM (fun z => (X i z)^2) hxsc (by norm_num : (0 : ℝ) ≤ 1) (fun z => by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (R.2 z)),
      hM (X i) hxc (by norm_num : (0 : ℝ) ≤ 1) R.2]
    simp only [Pi.mul_apply,hXe,pow_two]
  have hv' (s : S) (i : Fin N) : L' s (cascadeLift n (coordinateAxis N i)) = a*v s i := by
    change L s (cascadeMapCLM n (parameterNoise (E := E) N) (cascadeLift n (coordinateAxis N i))) = _
    rw [cascadeMapCLM_lift]
    exact hv s i
  have H := cascadeGaussian_conditional_trace N n m c' L' p a 0 hp ha hl hm hmu hmono v hvb hv'
  change (finiteCovariance (integratedWeights P' μ) v*finiteCovariance (integratedWeights P' μ) v).trace ≤
    (N : ℝ)*(covarianceMatrix (fun i z => finiteMean (P' z) v i) μ).trace+(N : ℝ)/(a^2*p^2) at H
  rw [hV,← hW] at H
  exact H
end CascadeBlockTrace
end SK.Analytic

end
end

end

end OAI
