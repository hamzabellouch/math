import Mathlib
import OAI.Analysis.BiholderTransport.Calculus.SecondDerivativeSlice
import OAI.Analysis.BiholderTransport.LinearAlgebra.DividedHessian
import OAI.Analysis.BiholderTransport.Regularity.NormMinMax

namespace OAI

section
section
noncomputable section
open scoped BigOperators

namespace WeakMTWTransport
section PositiveSingular
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma eigenbasis_operator_norm_expansion {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ E=n) (v : E) :
    ‖A v‖^2 = ∑ j, (hA.eigenvalues hn j)^2*((hA.eigenvectorBasis hn).repr v j)^2 := by
  rw [eigenbasis_norm_expansion (hA.eigenvectorBasis hn)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hA.eigenvectorBasis_apply_self_apply]
  simp only [RCLike.ofReal_real_eq_id,id_eq,mul_pow]

lemma positive_norm_lower_spectral_slice {A : E →ₗ[ℝ] E} (hA : A.IsPositive)
    {n : ℕ} (hn : Module.finrank ℝ E=n) (i : Fin n) (v : E)
    (hv : ∀ j : Fin n, i < j → (hA.isSymmetric.eigenvectorBasis hn).repr v j=0) :
    (hA.isSymmetric.eigenvalues hn i)^2*‖v‖^2≤‖A v‖^2 := by
  rw [eigenbasis_operator_norm_expansion hA.isSymmetric hn,
    eigenbasis_norm_expansion (hA.isSymmetric.eigenvectorBasis hn),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hji : j ≤ i
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ (hA.nonneg_eigenvalues hn i)
      (hA.isSymmetric.eigenvalues_antitone hn hji) 2
  · rw [hv j (lt_of_not_ge hji)]; simp

lemma positive_norm_upper_spectral_slice {A : E →ₗ[ℝ] E} (hA : A.IsPositive)
    {n : ℕ} (hn : Module.finrank ℝ E=n) (i : Fin n) (v : E)
    (hv : ∀ j : Fin n, j < i → (hA.isSymmetric.eigenvectorBasis hn).repr v j=0) :
    ‖A v‖^2≤(hA.isSymmetric.eigenvalues hn i)^2*‖v‖^2 := by
  rw [eigenbasis_operator_norm_expansion hA.isSymmetric hn,
    eigenbasis_norm_expansion (hA.isSymmetric.eigenvectorBasis hn),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hij : i ≤ j
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ (hA.nonneg_eigenvalues hn j)
      (hA.isSymmetric.eigenvalues_antitone hn hij) 2
  · rw [hv j (lt_of_not_ge hij)]; simp

lemma positive_singularValues_eq_eigenvalues {A : E →ₗ[ℝ] E} (hA : A.IsPositive)
    {n : ℕ} (hn : Module.finrank ℝ E=n) (i : Fin n) :
    A.singularValues i=hA.isSymmetric.eigenvalues hn i := by
  have hG := A.isSymmetric_adjoint_comp_self
  have hApos := hA.nonneg_eigenvalues hn i
  have hspos := A.singularValues_nonneg i
  apply le_antisymm
  · obtain ⟨v,hv,hgv,hav⟩ := paired_basis_slice (hG.eigenvectorBasis hn)
      (hA.isSymmetric.eigenvectorBasis hn) i
    have h1 := quadratic_lower_spectral_slice hG hn i v hgv
    have h2 := positive_norm_upper_spectral_slice hA hn i v hav
    simp only [LinearMap.comp_apply,LinearMap.adjoint_inner_left,
      real_inner_self_eq_norm_sq] at h1
    rw [←A.sq_singularValues_fin hn] at h1
    have hp : 0<‖v‖^2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv)
    have hsq := (mul_le_mul_iff_left₀ hp).mp (h1.trans h2)
    nlinarith
  · obtain ⟨v,hv,hav,hgv⟩ := paired_basis_slice (hA.isSymmetric.eigenvectorBasis hn)
      (hG.eigenvectorBasis hn) i
    have h1 := positive_norm_lower_spectral_slice hA hn i v hav
    have h2 := quadratic_upper_spectral_slice hG hn i v hgv
    simp only [LinearMap.comp_apply,LinearMap.adjoint_inner_left,
      real_inner_self_eq_norm_sq] at h2
    rw [←A.sq_singularValues_fin hn] at h2
    have hp : 0<‖v‖^2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv)
    have hsq := (mul_le_mul_iff_left₀ hp).mp (h1.trans h2)
    nlinarith

end PositiveSingular
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section CrossingDerivative
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma normalHessian_radial_derivative_value {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈injectivityDomain x)
    (v : TangentSpace 𝓘(ℝ,Model n) x) :
    HasDerivAt (fun s : ℝ => normalHessian x (s • p) v v)
      (normalHessian x p v v-radialCrossingValue x p v) 1 := by
  let X := TangentSpace 𝓘(ℝ,Model n) x
  let B := doubleNormalCost (n := n) x x
  have hB : ContDiffAt ℝ 3 B (0,p) :=
    (doubleNormalCost_self_contDiffAt hp).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)
  have hD := hasDerivAt_source_hessian_line (a := (0:X)) (b := p)
    (w := p) (t := 1) (v := v) hB
  have heq : (fun s : ℝ => fderiv ℝ (fderiv ℝ (fun a : X => B (a,p+(s-1) • p))) 0 v v)=
      (fun s : ℝ => normalHessian x (s • p) v v) := by
    funext s
    have hs : p+(s-1) • p=s • p := by module
    rw [hs]
    rfl
  rw [heq] at hD
  have hS := second_derivative_source_slice (a := (0:X)) (b := p)
    (hB.of_le (by norm_num)) v v
  change normalHessian x p v v = _ at hS
  convert hD using 1
  dsimp only [radialCrossingValue]
  rw [←hS]
  ring

lemma divided_normalHessian_derivative_value {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} {t : ℝ} (ht : t≠0)
    (hp : t • p∈injectivityDomain x) (v : TangentSpace 𝓘(ℝ,Model n) x) :
    HasDerivAt (fun s : ℝ => normalHessian x (s • p) v v / s)
      (-(radialCrossingValue x (t • p) v/t^2)) t := by
  have hlin : HasDerivAt (fun s : ℝ => s/t) (1/t) t := (hasDerivAt_id t).div_const t
  have hder' : HasDerivAt (fun r : ℝ => normalHessian x (r • (t • p)) v v)
      (normalHessian x (t • p) v v-radialCrossingValue x (t • p) v) (t/t) := by
    simpa only [div_self ht] using normalHessian_radial_derivative_value hp v
  have hcomp := hder'.comp (h := fun s : ℝ => s/t) t hlin
  have heq : (fun s : ℝ => normalHessian x ((s/t) • (t • p)) v v)=
      (fun s : ℝ => normalHessian x (s • p) v v) := by
    funext s
    rw [smul_smul,div_mul_cancel₀ s ht]
  simp only [Function.comp_def] at hcomp
  rw [heq] at hcomp
  have H := hcomp.div (hasDerivAt_id t) ht
  simp only [id_eq] at H
  convert H using 1
  all_goals first | rfl | (field_simp [ht]; ring)
end CrossingDerivative
end WeakMTWTransport

end

end

end

end OAI
