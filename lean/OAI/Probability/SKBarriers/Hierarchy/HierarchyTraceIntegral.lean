import Mathlib
import OAI.Probability.SKBarriers.Gaussian.BlockStein
import OAI.Probability.SKBarriers.Hierarchy.HierarchyBlockTrace
import OAI.Probability.SKBarriers.Scalar.CovarianceRegular

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section TraceIntegral
variable {S : Type} [Fintype S] [Nonempty S]

theorem hierarchyBlock_trace_integral (a N d : ℕ) (hN : 0 < N)
    (m : Fin (a+(N+d)) → ℝ) (U : S → ParameterSpace (a+(N+d)) →L[ℝ] ℝ)
    (p scale : ℝ) (hp : 0 < p) (ha : 0 < scale) (hl : p ≤ 1)
    (hb : ∀ i : Fin N, m ⟨a+i,by omega⟩ = p)
    (hm : ∀ i : Fin d, p ≤ m ⟨a+N+i,by omega⟩)
    (hmu : ∀ i : Fin d, m ⟨a+N+i,by omega⟩ ≤ 1)
    (hmono : Monotone (fun i : Fin d => m ⟨a+N+i,by omega⟩))
    (v : S → Fin N → ℝ) (hvb : ∀ s i, |v s i| ≤ 1)
    (hv : ∀ s i, U s (parameterBlocks a N d (cascadeLift d
      (parameterNoise (E := ParameterSpace a) N (coordinateAxis N i)))) = scale*v s i) :
    (∫ z, hierarchyTraceSquare (a+(N+d)) m U v ⟨a,by omega⟩ z
      ∂hierarchyPathLaw (a+(N+d)) m (affineLogPartition (fun _ => 0) U) 0)/(N : ℝ)^2 ≤
      hierarchyMeanOverlap (a+(N+d)) m U (fun i s => v s i) ⟨a+N,by omega⟩-
      hierarchyMeanOverlap (a+(N+d)) m U (fun i s => v s i) ⟨a,by omega⟩+
      1/((N : ℝ)*scale^2*p^2) := by
  let n := a+(N+d)
  let f := affineLogPartition (fun _ => 0) U
  have hf := affineLogPartition_boundedDerivs (fun _ => 0) U
  let μ := hierarchyPathLaw n m f 0
  let := hierarchyPathLaw_probability n m f hf 0
  let j : Fin (n+1) := ⟨a,by dsimp [n]; omega⟩
  let l : Fin (n+1) := ⟨a+N,by dsimp [n]; omega⟩
  let M := fun (i : Fin N) (q : Fin (n+1)) => hierarchySpinMean n m U (fun s => v s i) q
  have hr (i : Fin N) (q : Fin (n+1)) : Continuous (M i q) ∧ ∀ z, ‖M i q z‖ ≤ 1 :=
    hierarchySpinMean_regular n m U (fun s => v s i) (by norm_num)
      (fun s => by simpa only [Real.norm_eq_abs] using hvb s i) q
  have hsq (i : Fin N) (q : Fin (n+1)) : ∀ z, ‖(M i q z)^2‖ ≤ 1 := by
    intro z
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) ((hr i q).2 z)
  have hI (i : Fin N) (q : Fin (n+1)) : Integrable (fun z => (M i q z)^2) μ :=
    hierarchyPathLaw_integrable n m f _ hf ((hr i q).1.pow 2) (hsq i q) 0
  let T := fun (i : Fin N) => hierarchyMomentLevel n m f (fun z => (M i l z)^2) j
  have hT (i : Fin N) : Integrable (T i) μ := by
    have h := hierarchyMomentLevel_bounded_continuous n m f (fun z => (M i l z)^2)
      hf ((hr i l).1.pow 2) (by norm_num : (0 : ℝ) ≤ 1) (hsq i l) j
    exact hierarchyPathLaw_integrable n m f _ hf h.1 h.2 0
  have hTI (i : Fin N) : (∫ z, T i z ∂μ) = ∫ z, (M i l z)^2 ∂μ :=
    hierarchyPathLaw_moment_integral n m f _ hf ((hr i l).1.pow 2) (by norm_num) (hsq i l) j 0
  have hpoint (z : ParameterSpace n) : hierarchyTraceSquare n m U v j z ≤
      (N : ℝ)*(∑ i, (T i z-(M i j z)^2))+(N : ℝ)/(scale^2*p^2) :=
    hierarchyBlock_conditional_trace a N d m U p scale hp ha hl hb hm hmu hmono v hvb hv z
  have hsum : Integrable (fun z => ∑ i : Fin N, (T i z-(M i j z)^2)) μ :=
    integrable_finsetSum _ (fun i _ => (hT i).sub (hI i j))
  have hint := integral_mono (hierarchyTraceSquare_integrable n m U v hvb j 0)
    (((integrable_finsetSum _ (fun i _ => (hT i).sub (hI i j))).const_mul (N : ℝ)).add
      (integrable_const ((N : ℝ)/(scale^2*p^2)))) hpoint
  have hexp (q : Fin (n+1)) :
      (∑ i, ∫ z, (M i q z)^2 ∂μ) = (N : ℝ)*hierarchyMeanOverlap n m U (fun i s => v s i) q := by
    unfold hierarchyMeanOverlap hierarchyMeanSquare normalizedSquare
    rw [integral_div,integral_finsetSum _ (fun i _ => hI i q)]
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    field_simp
  change (∫ z, hierarchyTraceSquare n m U v j z ∂μ) ≤
    ∫ z, (N : ℝ)*(∑ i : Fin N, (T i z-(M i j z)^2))+(N : ℝ)/(scale^2*p^2) ∂μ at hint
  rw [integral_add (hsum.const_mul (N : ℝ))
    (integrable_const ((N : ℝ)/(scale^2*p^2))),integral_const_mul,
    integral_finsetSum (f := fun i z => T i z-(M i j z)^2) Finset.univ (fun i _ => (hT i).sub (hI i j))] at hint
  simp only [integral_sub (hT _) (hI _ j),hTI,Finset.sum_sub_distrib,hexp] at hint
  have hc : (∫ _ : ParameterSpace n, (N : ℝ)/(scale^2*p^2) ∂μ) = (N : ℝ)/(scale^2*p^2) := by simp
  rw [hc] at hint
  change (∫ z, hierarchyTraceSquare n m U v j z ∂μ)/(N : ℝ)^2 ≤ _
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  apply (div_le_iff₀ (sq_pos_of_pos hn)).2
  calc
    _ ≤ (N : ℝ)*(↑N*hierarchyMeanOverlap n m U (fun i s => v s i) l-
      ↑N*hierarchyMeanOverlap n m U (fun i s => v s i) j)+↑N/(scale^2*p^2) := hint
    _ = _ := by field_simp [ne_of_gt hn,ne_of_gt ha,ne_of_gt hp]; ring
end TraceIntegral
end SK.Analytic

end
end

end

end OAI
