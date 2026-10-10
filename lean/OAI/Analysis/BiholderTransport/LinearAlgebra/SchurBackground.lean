import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.HessianBounds
import OAI.Analysis.BiholderTransport.LinearAlgebra.SchurCalculus
import OAI.Analysis.BiholderTransport.Regularity.NormMinMax
import OAI.Analysis.BiholderTransport.LinearAlgebra.JoinOperator
import OAI.Analysis.BiholderTransport.LinearAlgebra.ShearConvexity

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section SchurBackground
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma splitJoinHessianOperator_pairing_fixed {x : M}
    {p : TangentSpace 𝓘(ℝ,Model n) x} (hp : p∈minimizingVectors x)
    {t : ℝ} (ht : 0<t) (ht1 : t<1) (a k : TangentSpace 𝓘(ℝ,Model n) x) :
    inner ℝ (splitJoinHessianOperator x t p a) k=
      fderiv ℝ (fderiv ℝ (splitNormalAction x t p)) (0,p) (0,a) (0,k) := by
  rw [inner_splitJoinHessianOperator]
  have hleft := contracted_minimizer_mem_injectivityDomain hp ht ht1
  have hright := proper_suffix_in_injectivityDomain
    (z := (⟨x,p⟩ : TangentBundle 𝓘(ℝ,Model n) M)) hp ht ht1 le_rfl
  have hD := (diagonalSplitAction_contDiffAt hleft hright).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hB := (fixedSplitAction_contDiffAt hp ht ht1).of_le
    (m := 2) (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  rw [←second_derivative_target_slice hD,←second_derivative_target_slice hB]
  rfl

lemma schur_operator_inverse {x : M} {p : TangentSpace 𝓘(ℝ,Model n) x}
    (hp : p∈minimizingVectors x) {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (K : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x)
    (hK : ∀ v k, fderiv ℝ (fderiv ℝ (splitNormalAction x t p)) (0,p) (0,K v) (0,k)=inner ℝ k v) :
    ∀ v, splitJoinHessianOperator x t p (K v)=v := by
  intro v
  apply ext_inner_right ℝ
  intro k
  rw [splitJoinHessianOperator_pairing_fixed hp ht ht1,hK,real_inner_comm]

lemma uniform_radial_Schur_background :
    ∃ C : ℝ, 0<C ∧ ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      p∈minimizingVectors x → ∀ δ∈Ioc (0:ℝ) (1/2),
      ∃ K : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x,
        Function.Bijective K ∧ K.toLinearMap.IsPositive ∧
        (∀ v, splitJoinHessianOperator x (1/2) ((1-δ) • p) (K v)=v) ∧
        (∀ v, radialHessianDefectBilinear x p δ v v=δ*inner ℝ (K v) v+
          δ*(‖v‖^2-2*normalHessian x (((1-δ)/2) • p) v v)) ∧
        ∀ v, |radialHessianDefectBilinear x p δ v v-δ*inner ℝ (K v) v|≤C*δ*‖v‖^2 := by
  obtain ⟨C,hC,H⟩ := uniform_prefixHessian_bounds (n := n) (M := M)
  refine ⟨1+2*C,by positivity,?_⟩
  intro x p hp δ hd
  have hI := contracted_minimizer_mem_injectivityDomain hp
    (show 0<1-δ by linarith [hd.2]) (show 1-δ<1 by linarith [hd.1])
  obtain ⟨K,hK,hKs,hKn,hInv,hS⟩ := exists_splitAction_schur_operator hI
    (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)
  have hKpos : K.toLinearMap.IsPositive := ⟨hKs,hKn⟩
  have hEq (v : TangentSpace 𝓘(ℝ,Model n) x) :
      radialHessianDefectBilinear x p δ v v=δ*inner ℝ (K v) v+
        δ*(‖v‖^2-2*normalHessian x (((1-δ)/2) • p) v v) := by
    rw [radialHessianDefect_apply,hS,smul_smul,real_inner_self_eq_norm_sq]
    have he : (1/2:ℝ)*(1-δ)=(1-δ)/2 := by ring
    rw [he]
    ring
  refine ⟨K,hK,hKpos,schur_operator_inverse
    (injectivityDomain_subset_minimizingVectors x hI) (by norm_num) (by norm_num) K hInv,hEq,?_⟩
  intro v
  rw [hEq,add_sub_cancel_left,abs_mul,abs_of_pos hd.1]
  have hB := H x p hp ((1-δ)/2) (by constructor <;> linarith [hd.1,hd.2]) v v
  have htri := abs_sub (‖v‖^2) (2*normalHessian x (((1-δ)/2) • p) v v)
  rw [abs_of_nonneg (sq_nonneg ‖v‖),abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at htri
  have hB' : |‖v‖^2-2*normalHessian x (((1-δ)/2) • p) v v|≤(1+2*C)*‖v‖^2 := by
    nlinarith
  have HH := mul_le_mul_of_nonneg_left hB' hd.1.le
  nlinarith only [HH]

end SchurBackground
end WeakMTWTransport

end

end

section

noncomputable section
open scoped BigOperators

namespace WeakMTWTransport
section InverseSpectrum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma diagonal_quadratic_expansion {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (μ : Fin n → ℝ)
    (hμ : ∀ j, A (b j)=μ j • b j) (v : E) :
    inner ℝ (A v) v=∑ j, μ j*(b.repr v j)^2 := by
  have hcoord (j : Fin n) : b.repr (A v) j=μ j*b.repr v j := by
    rw [b.repr_apply_apply,b.repr_apply_apply,←hA _ _,hμ,real_inner_smul_left]
  have H := b.repr.inner_map_map (A v) v
  rw [←H,PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hcoord]
  simp only [RCLike.inner_apply,conj_trivial]
  ring

lemma ordered_eigenvalues_of_diagonal_basis {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ E=n) (b : OrthonormalBasis (Fin n) ℝ E)
    (μ : Fin n → ℝ) (hμ : ∀ j, A (b j)=μ j • b j) (hm : Antitone μ) (i : Fin n) :
    hA.eigenvalues hn i=μ i := by
  apply le_antisymm
  · obtain ⟨v,hv,hav,hbv⟩ := paired_basis_slice (hA.eigenvectorBasis hn) b i
    have h1 := quadratic_lower_spectral_slice hA hn i v hav
    have h2 : inner ℝ (A v) v≤μ i*‖v‖^2 := by
      rw [diagonal_quadratic_expansion hA b μ hμ,eigenbasis_norm_expansion b,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      by_cases hij : i≤j
      · exact mul_le_mul_of_nonneg_right (hm hij) (sq_nonneg _)
      · rw [hbv j (lt_of_not_ge hij)]; simp
    exact (mul_le_mul_iff_left₀ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv))).mp (h1.trans h2)
  · obtain ⟨v,hv,hbv,hav⟩ := paired_basis_slice b (hA.eigenvectorBasis hn) i
    have h1 : μ i*‖v‖^2≤ inner ℝ (A v) v := by
      rw [diagonal_quadratic_expansion hA b μ hμ,eigenbasis_norm_expansion b,Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      by_cases hji : j ≤ i
      · exact mul_le_mul_of_nonneg_right (hm hji) (sq_nonneg _)
      · rw [hbv j (lt_of_not_ge hji)]; simp
    have h2 := quadratic_upper_spectral_slice hA hn i v hav
    exact (mul_le_mul_iff_left₀ (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hv))).mp (h1.trans h2)

lemma positive_eigenvalues_of_injective {A : E →ₗ[ℝ] E} (hA : A.IsPositive)
    (hi : Function.Injective A) {n : ℕ} (hn : Module.finrank ℝ E=n) (i : Fin n) :
    0<hA.isSymmetric.eigenvalues hn i := by
  apply lt_of_le_of_ne (hA.nonneg_eigenvalues hn i)
  intro h
  have H := hA.isSymmetric.apply_eigenvectorBasis hn i
  rw [←h] at H
  simp only [RCLike.ofReal_real_eq_id,id_eq,zero_smul] at H
  have H0 := hi (H.trans (map_zero A).symm)
  have H1 := (hA.isSymmetric.eigenvectorBasis hn).norm_eq_one i
  rw [H0,norm_zero] at H1
  norm_num at H1

lemma ordered_eigenvalues_inverse {A K : E →ₗ[ℝ] E}
    (hA : A.IsPositive) (hK : K.IsSymmetric)
    (hi : Function.Injective A) (hAK : ∀ v, A (K v)=v)
    {n : ℕ} (hn : Module.finrank ℝ E=n) (i : Fin n) :
    hK.eigenvalues hn i=(hA.isSymmetric.eigenvalues hn i.rev)⁻¹ := by
  let b := (hA.isSymmetric.eigenvectorBasis hn).reindex Fin.revPerm
  let μ : Fin n → ℝ := fun j => (hA.isSymmetric.eigenvalues hn j.rev)⁻¹
  have hμ (j : Fin n) : K (b j)=μ j • b j := by
    apply hi
    rw [hAK,map_smul]
    have he : A (b j)=hA.isSymmetric.eigenvalues hn j.rev • b j := by
      simpa only [b,OrthonormalBasis.reindex_apply,Fin.revPerm_symm,Fin.revPerm_apply,
        RCLike.ofReal_real_eq_id,id_eq]
        using hA.isSymmetric.apply_eigenvectorBasis hn j.rev
    rw [he,smul_smul]
    dsimp only [μ]
    rw [inv_mul_cancel₀ (positive_eigenvalues_of_injective hA hi hn j.rev).ne',one_smul]
  apply ordered_eigenvalues_of_diagonal_basis hK hn b μ hμ _ i
  intro j k hjk
  exact inv_le_inv₀ (positive_eigenvalues_of_injective hA hi hn k.rev)
    (positive_eigenvalues_of_injective hA hi hn j.rev) |>.mpr
      (hA.isSymmetric.eigenvalues_antitone hn (Fin.rev_le_rev.mpr hjk))

end InverseSpectrum
end WeakMTWTransport

end

end

end

end OAI
