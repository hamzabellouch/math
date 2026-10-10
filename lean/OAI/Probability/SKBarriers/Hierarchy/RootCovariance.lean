import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarHierarchyAverageAlgebra
import OAI.Probability.SKBarriers.Replicas.TripleRecursiveExpansion

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic
section Covariance
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem covariance_small_field {a b X : Ω → ℝ} {c M L : ℝ}
    (ha : Integrable a μ) (hb : Integrable b μ) (hab : Integrable (fun z => a z*b z) μ)
    (hX : Integrable X μ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hs : ∀ z, |a z-c| ≤ L*|X z|) (hbM : ∀ z, |b z| ≤ M) :
    |(∫ z, a z*b z ∂μ)-(∫ z,a z ∂μ)*(∫ z,b z ∂μ)| ≤ 2*M*L*(∫ z,|X z| ∂μ) := by
  have hd : Integrable (fun z => a z-c) μ := ha.sub (integrable_const c)
  have hdb : Integrable (fun z => (a z-c)*b z) μ := by
    convert hab.sub (hb.const_mul c) using 1
    ext point
    simp only [Pi.sub_apply]
    ring
  have h1 : |∫ z, (a z-c)*b z ∂μ| ≤ M*L*(∫ z,|X z| ∂μ) := by
    calc
      _ ≤ ∫ z, |(a z-c)*b z| ∂μ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun z => (a z-c)*b z)
      _ ≤ ∫ z, M*L*|X z| ∂μ := by
        apply integral_mono_ae hdb.abs (hX.abs.const_mul (M*L))
        exact ae_of_all _ (fun z => by
          change |(a z-c)*b z| ≤ M*L*|X z|
          rw [abs_mul]
          calc
            _ ≤ |a z-c| * M := mul_le_mul_of_nonneg_left (hbM z) (abs_nonneg _)
            _ ≤ (L*|X z|)*M := mul_le_mul_of_nonneg_right (hs z) hM
            _ = _ := by ring)
      _ = _ := integral_const_mul _ _
  have h2 : |∫ z, a z-c ∂μ| ≤ L*(∫ z,|X z| ∂μ) := by
    calc
      _ ≤ ∫ z, |a z-c| ∂μ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun z => a z-c)
      _ ≤ ∫ z, L*|X z| ∂μ := integral_mono_ae hd.abs (hX.abs.const_mul L) (ae_of_all _ hs)
      _ = _ := integral_const_mul _ _
  have h3 : |∫ z,b z ∂μ| ≤ M := by
    calc
      _ ≤ ∫ z,|b z| ∂μ := by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm b
      _ ≤ ∫ _ : Ω,M ∂μ := integral_mono_ae hb.abs (integrable_const M) (ae_of_all _ hbM)
      _ = M := by simp
  have he : (∫ z, a z*b z ∂μ)-(∫ z,a z ∂μ)*(∫ z,b z ∂μ)=
      (∫ z,(a z-c)*b z ∂μ)-(∫ z,a z-c ∂μ)*(∫ z,b z ∂μ) := by
    have hfun : (fun z => (a z-c)*b z)=fun z => a z*b z-c*b z := by funext z; ring
    rw [hfun,integral_sub hab (hb.const_mul c),integral_const_mul,integral_sub ha (integrable_const c)]
    simp only [integral_const,probReal_univ,one_smul]
    ring
  rw [he]
  calc
    _ ≤ |∫ z,(a z-c)*b z ∂μ|+|(∫ z,a z-c ∂μ)*(∫ z,b z ∂μ)| := abs_sub _ _
    _ ≤ M*L*(∫ z,|X z| ∂μ)+(L*(∫ z,|X z| ∂μ))*M := by
      rw [abs_mul]
      exact add_le_add h1 (mul_le_mul h2 h3 (abs_nonneg _) (by positivity))
    _ = _ := by ring
end Covariance

attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarHierarchyAverage_covariance_small (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i,m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {f A B : ℝ → ℝ} (hf : BoundedDerivs f) (hfL : LipschitzWith 1 f)
    (hA : BoundedScalar A) (hB : BoundedScalar B) {M L : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L) (hBM : ∀ x, |B x| ≤ M)
    (hAL : ∀ x, |A x-A 0| ≤ L*|x|) :
    |scalarHierarchyAverage n m v f (fun x => A x*B x) 0-
      scalarHierarchyAverage n m v f A 0*scalarHierarchyAverage n m v f B 0| ≤
        2*M*L*Real.sqrt (2*(∑ i,(v i)^2)+4*(∑ i,(v i)^2)^2) := by
  let X := coordinateLinear n v
  let F := f ∘ X
  let μ := hierarchyPathLaw n m F 0
  have hF : BoundedDerivs F := hf.compCLM X
  let := hierarchyPathLaw_probability n m F hF 0
  have hX : Integrable X μ := (HasExpGrowth.linear X).integrable_hierarchyPathLaw n m hF X.continuous 0
  have hXsq : Integrable (fun z => (X z)^2) μ := ((HasExpGrowth.linear X).pow 2).integrable_hierarchyPathLaw
    n m hF (X.continuous.pow 2) 0
  have hXi : MemLp X 2 μ := (memLp_two_iff_integrable_sq X.continuous.aestronglyMeasurable).2 hXsq
  have hAs : Integrable (A ∘ X) μ := by
    simpa only [zero_add,Function.comp_def,μ,F,X] using scalarHierarchyAverage_integrable hf hA n m v 0
  have hBs : Integrable (B ∘ X) μ := by
    simpa only [zero_add,Function.comp_def,μ,F,X] using scalarHierarchyAverage_integrable hf hB n m v 0
  have hAB : BoundedScalar (fun x => A x*B x) := by
    obtain ⟨Ca,hCa,ha⟩ := hA.bounded
    obtain ⟨Cb,hCb,hb⟩ := hB.bounded
    exact ⟨hA.continuous.mul hB.continuous,⟨Ca*Cb,mul_nonneg hCa hCb,fun x => by
      rw [abs_mul]; exact mul_le_mul (ha x) (hb x) (abs_nonneg _) hCa⟩⟩
  have hABs : Integrable (fun z => A (X z)*B (X z)) μ := by
    simpa only [zero_add,Function.comp_def,μ,F,X] using scalarHierarchyAverage_integrable hf hAB n m v 0
  have H := covariance_small_field hAs hBs hABs hX hM hL (fun z => hAL (X z)) (fun z => hBM (X z))
  have hS := hierarchy_square_bound n m hm hmono F hF (fun i => |v i|) (fun i => abs_nonneg _)
    (fun z i => by
      have H := scalar_composition_coordinate_bound hf hfL X z (coordinateAxis n i)
      simpa only [F,X,coordinateLinear_coordinateAxis] using H) 0 v
  have hsum : (∑ i, |v i| * |v i|)=∑ i,(v i)^2 := by
    apply Finset.sum_congr rfl; intro i _; rw [← sq_abs]; ring
  rw [hsum] at hS
  have hS' : (∫ z,(X z)^2 ∂μ) ≤ 2*(∑ i,(v i)^2)+4*(∑ i,(v i)^2)^2 := by nlinarith [hS]
  have hE : (∫ z,|X z| ∂μ) ≤ Real.sqrt (2*(∑ i,(v i)^2)+4*(∑ i,(v i)^2)^2) := by
    have H := abs_integral_mul_le_sqrt_of_bound (fun z => |X z|) (fun _ => (1:ℝ)) hXi.abs
      aestronglyMeasurable_const (ae_of_all _ (fun _ => by norm_num))
    simp only [mul_one,sq_abs,abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))] at H
    exact H.trans (Real.sqrt_le_sqrt hS')
  rw [scalarHierarchyAverage_integral hf hAB,scalarHierarchyAverage_integral hf hA,
    scalarHierarchyAverage_integral hf hB]
  simp only [zero_add]
  simpa only [μ,F,X,Function.comp_def] using H.trans (mul_le_mul_of_nonneg_left hE (by positivity))

end SK.Analytic

end
end

end OAI
