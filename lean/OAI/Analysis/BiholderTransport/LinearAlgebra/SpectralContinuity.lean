import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.UniformMiddle

namespace OAI

section
section
noncomputable section
open Filter
open scoped Topology

namespace WeakMTWTransport
section SpectralContinuity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma ordered_eigenvalues_positive_crossing {A B : E →L[ℝ] E}
    (hA : A.toLinearMap.IsSymmetric) (hB : B.toLinearMap.IsSymmetric)
    {c C : ℝ}
    (h : ∀ v, c*‖v‖^2 ≤ inner ℝ (B v) v-inner ℝ (A v) v ∧
      inner ℝ (B v) v-inner ℝ (A v) v ≤ C*‖v‖^2)
    {n : ℕ} (hn : Module.finrank ℝ E = n) (i : Fin n) :
    hA.eigenvalues hn i+c ≤ hB.eigenvalues hn i ∧
      hB.eigenvalues hn i ≤ hA.eigenvalues hn i+C := by
  have H1 := ordered_eigenvalue_quadratic_comparison hA hB (a := 1) (b := -c)
    (by norm_num) (fun v => by have := (h v).1; change inner ℝ (A v) v ≤ 1*inner ℝ (B v) v+(-c)*‖v‖^2; linarith) hn i
  have H2 := ordered_eigenvalue_quadratic_comparison hB hA (a := 1) (b := C)
    (by norm_num) (fun v => by have := (h v).2; change inner ℝ (B v) v ≤ 1*inner ℝ (A v) v+C*‖v‖^2; linarith) hn i
  constructor <;> linarith

end SpectralContinuity
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section MiddleSpectrum
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

def middleHessianOperator (z : TangentBundle 𝓘(ℝ,Model n) M) (h T : ℝ) :
    TangentSpace 𝓘(ℝ,Model n) (sprayFlow h z).1 →L[ℝ]
      TangentSpace 𝓘(ℝ,Model n) (sprayFlow h z).1 :=
  (InnerProductSpace.toDual ℝ _).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (middleHessian z h T)

omit [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma inner_middleHessianOperator (z : TangentBundle 𝓘(ℝ,Model n) M) (h T : ℝ)
    (v w : TangentSpace 𝓘(ℝ,Model n) (sprayFlow h z).1) :
    inner ℝ (middleHessianOperator z h T v) w = middleHessian z h T v w :=
  InnerProductSpace.toDual_symm_apply

lemma middleHessianOperator_symmetric {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hz : z.2 ∈ minimizingVectors z.1) {h T : ℝ}
    (hh : 0 < h) (hh1 : h < 1) (hT : h < T) (hT1 : T ≤ 1) :
    (middleHessianOperator z h T).toLinearMap.IsSymmetric := by
  intro v w
  change inner ℝ (middleHessianOperator z h T v) w = inner ℝ v (middleHessianOperator z h T w)
  rw [real_inner_comm (middleHessianOperator z h T w) v,inner_middleHessianOperator,inner_middleHessianOperator,
    middleHessian_apply,middleHessian_apply,
    normalHessian_symm (proper_prefix_reverse_in_injectivityDomain hz hh hh1),
    normalHessian_symm (proper_suffix_in_injectivityDomain hz hh hT hT1)]

lemma shortened_middle_operator_positive {z : TangentBundle 𝓘(ℝ,Model n) M}
    (hz : z.2 ∈ minimizingVectors z.1) {δ : ℝ} (hd : 0 ≤ δ) (hdhalf : δ ≤ 1/2) :
    (middleHessianOperator z (1/4) (1-δ)).toLinearMap.IsPositive := by
  refine ⟨middleHessianOperator_symmetric hz (by norm_num) (by norm_num)
    (by linarith) (by linarith),?_⟩
  intro v
  change 0 ≤ inner ℝ (middleHessianOperator z (1/4) (1-δ) v) v
  rw [inner_middleHessianOperator]
  obtain ⟨c,C,hc,hC,H⟩ := uniform_middleHessian_crossing (n := n) (M := M)
  have H1 := (H z hz δ hd hdhalf v).1
  have H0 := middleHessian_one_nonneg hz (show (0:ℝ) < 1/4 by norm_num)
    (show (1/4:ℝ) < 1 by norm_num) v
  have Hpos := mul_nonneg (mul_nonneg hc.le hd) (sq_nonneg ‖v‖)
  linarith

lemma uniform_middle_ordered_crossing :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z : TangentBundle 𝓘(ℝ,Model n) M,
      ∀ hz : z.2 ∈ minimizingVectors z.1, ∀ δ : ℝ, ∀ hd : 0 ≤ δ, ∀ hdhalf : δ ≤ 1/2,
      ∀ i : Fin (Module.finrank ℝ (TangentSpace 𝓘(ℝ,Model n) (sprayFlow (1/4) z).1)),
      (shortened_middle_operator_positive hz (show (0:ℝ) ≤ 0 by norm_num)
        (show (0:ℝ) ≤ 1/2 by norm_num)).isSymmetric.eigenvalues rfl i + c*δ ≤
        (shortened_middle_operator_positive hz hd hdhalf).isSymmetric.eigenvalues rfl i ∧
      (shortened_middle_operator_positive hz hd hdhalf).isSymmetric.eigenvalues rfl i ≤
        (shortened_middle_operator_positive hz (show (0:ℝ) ≤ 0 by norm_num)
          (show (0:ℝ) ≤ 1/2 by norm_num)).isSymmetric.eigenvalues rfl i + C*δ := by
  obtain ⟨c,C,hc,hC,H⟩ := uniform_middleHessian_crossing (n := n) (M := M)
  refine ⟨c,C,hc,hC,?_⟩
  intro z hz δ hd hdhalf i
  apply ordered_eigenvalues_positive_crossing
  intro v
  simpa only [inner_middleHessianOperator,sub_zero,mul_assoc] using H z hz δ hd hdhalf v

end MiddleSpectrum
end WeakMTWTransport

end

end

end

end OAI
