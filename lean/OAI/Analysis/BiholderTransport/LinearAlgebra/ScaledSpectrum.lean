import Mathlib
import OAI.Analysis.BiholderTransport.CostGeometry.RadialSingular
import OAI.Analysis.BiholderTransport.LinearAlgebra.SchurBackground

namespace OAI

section
section
noncomputable section
namespace WeakMTWTransport
section ScaledSpectrum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma ordered_eigenvalues_nonneg_smul {A : E →ₗ[ℝ] E} (hA : A.IsSymmetric)
    {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : Module.finrank ℝ E=n) (i : Fin n) :
    (hA.smul (show starRingEnd ℝ c=c by simp)).eigenvalues hn i=
      c*hA.eigenvalues hn i := by
  apply ordered_eigenvalues_of_diagonal_basis _ hn (hA.eigenvectorBasis hn)
    (fun j => c*hA.eigenvalues hn j)
  · intro j
    simp only [LinearMap.smul_apply,hA.apply_eigenvectorBasis hn,
      RCLike.ofReal_real_eq_id,id_eq,smul_smul]
  · intro j k hjk
    exact mul_le_mul_of_nonneg_left (hA.eigenvalues_antitone hn hjk) hc

lemma reciprocal_spectrum_bounds {a b c C δ S L : ℝ}
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hC : 0<C) (hδ : 0 ≤ δ)
    (hS : 0<S) (hL : 0<L) (hlo : a*S ≤ c*L) (hup : L ≤ C*b*S) :
    (1/(C*b))*δ/S ≤ δ*L⁻¹ ∧ δ*L⁻¹ ≤ (c/a)*δ/S := by
  constructor
  · have he : (1/(C*b))*δ/S=δ/(C*b*S) := by ring
    rw [he,←div_eq_mul_inv]
    exact (div_le_div_iff₀ (mul_pos (mul_pos hC hb) hS) hL).2
      (mul_le_mul_of_nonneg_left hup hδ)
  · have hden : (a/c)*S ≤ L := by
      rw [div_mul_eq_mul_div,div_le_iff₀ hc]
      simpa only [mul_comm c L] using hlo
    have H := div_le_div_of_nonneg_left hδ (mul_pos (div_pos ha hc) hS) hden
    have he : δ/((a/c)*S)=(c/a)*δ/S := by
      field_simp
    rw [he,div_eq_mul_inv] at H
    exact H

end ScaledSpectrum
end WeakMTWTransport

end

end

section

noncomputable section
open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff

namespace WeakMTWTransport
section RadialSpectrum
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
local instance (x : M) : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ,Model n) x) :=
  inferInstanceAs (FiniteDimensional ℝ (Model n))

lemma uniform_radial_inverse_profile :
    ∃ l u B : ℝ, 0<l ∧ 0<u ∧ 0<B ∧
      ∀ x : M, ∀ p : TangentSpace 𝓘(ℝ,Model n) x,
      p∈minimizingVectors x → ∀ δ∈Ioc (0:ℝ) (1/2),
      ∃ (K : TangentSpace 𝓘(ℝ,Model n) x →L[ℝ] TangentSpace 𝓘(ℝ,Model n) x)
        (hK : K.toLinearMap.IsPositive), Function.Bijective K ∧
        (∀ v, |radialHessianDefectBilinear x p δ v v-δ*inner ℝ (K v) v|≤B*δ*‖v‖^2) ∧
        ∀ i : Fin (Module.finrank ℝ (Model n)),
          l*δ/((endpointExpDifferential x p).toLinearMap.singularValues i.rev+δ) ≤
            δ*hK.isSymmetric.eigenvalues rfl i ∧
          δ*hK.isSymmetric.eigenvalues rfl i ≤
            u*δ/((endpointExpDifferential x p).toLinearMap.singularValues i.rev+δ) := by
  obtain ⟨a,b,ha,hb,H⟩ := uniform_radial_singular_shortening (n := n) (M := M)
  obtain ⟨c,C,hc,hC,J⟩ := uniform_join_exp_ordered_comparison (n := n) (M := M)
  obtain ⟨B,hB,BG⟩ := uniform_radial_Schur_background (n := n) (M := M)
  refine ⟨1/(C*b),c/a,B,div_pos (by norm_num) (mul_pos hC hb),div_pos hc ha,hB,?_⟩
  intro x p hp δ hd
  obtain ⟨K,hKb,hK,hInv,hEq,hBg⟩ := BG x p hp δ hd
  refine ⟨K,hK,hKb,hBg,?_⟩
  intro i
  let A := splitJoinHessianOperator x (1/2) ((1-δ) • p)
  have hmin := minimizingVectors_smul hp
    (show 0 ≤ 1-δ by linarith [hd.2]) (show 1-δ ≤ 1 by linarith [hd.1])
  have hA : A.toLinearMap.IsPositive := splitJoinHessianOperator_positive hmin
    (show (0:ℝ)<1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)
  have hAi : Function.Injective A := (LinearMap.injective_iff_surjective (f := A.toLinearMap)).mpr
    (fun v => ⟨K v,hInv v⟩)
  have heig := ordered_eigenvalues_inverse hA hK.isSymmetric hAi hInv rfl i
  rw [heig]
  have hR := H x p hp δ ⟨hd.1.le,hd.2⟩ i.rev
  have hJ := J x ((1-δ) • p) hmin (1/2) (by constructor <;> norm_num) i.rev
  let S := (endpointExpDifferential x p).toLinearMap.singularValues i.rev+δ
  let R := (endpointExpDifferential x ((1-δ) • p)).toLinearMap.singularValues i.rev
  let L := hA.isSymmetric.eigenvalues rfl i.rev
  change a*S ≤ R ∧ R ≤ b*S at hR
  change L ≤ C*R ∧ R ≤ c*L at hJ
  have hS : 0<S := add_pos_of_nonneg_of_pos
    ((endpointExpDifferential x p).toLinearMap.singularValues_nonneg i.rev) hd.1
  have hL : 0<L := positive_eigenvalues_of_injective hA hAi rfl i.rev
  have hlo : a*S ≤ c*L := hR.1.trans hJ.2
  have hup : L ≤ C*b*S := by
    simpa only [mul_assoc] using hJ.1.trans (mul_le_mul_of_nonneg_left hR.2 hC.le)
  exact reciprocal_spectrum_bounds ha hb hc hC hd.1.le hS hL hlo hup

end RadialSpectrum
end WeakMTWTransport

end

end

end

end OAI
