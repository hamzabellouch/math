import OAI.Combinatorics.PerfectMatching.Separable

namespace OAI

universe u_1 u_2

section

noncomputable section
open scoped BigOperators
open Matrix
namespace MatchingEntropy

theorem spectral_diagonal {I : Type*} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℝ} (hC : C.IsHermitian) (e : I) :
    C e e = ∑ i, hC.eigenvalues i * (hC.eigenvectorBasis i e)^2 := by
  have hh := congrArg (fun A : Matrix I I ℝ => A e e) hC.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hh
  simpa only [mul_apply, diagonal_apply, star_eq_conjTranspose, conjTranspose_apply,
    star_trivial, Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq,
    mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Matrix.IsHermitian.eigenvectorUnitary_apply, pow_two, mul_comm, mul_left_comm,
    mul_assoc] using hh

theorem covariance_weighted_rank {I : Type*} [Fintype I] [DecidableEq I]
    {C : Matrix I I ℝ} (hC : C.PosSemidef) (w : I → ℝ)
    (hsecond : ∀ u : I → ℝ,
      u ⬝ᵥ (C *ᵥ u) ≤ ∑ e, w e * ((C *ᵥ u) e)^2) :
    (C.rank : ℝ) ≤ ∑ e, w e * C e e := by
  let eig := hC.isHermitian.eigenvalues
  let b := hC.isHermitian.eigenvectorBasis
  have heig : ∀ i, 0 ≤ eig i := hC.eigenvalues_nonneg
  have hone : ∀ i, eig i ≠ 0 → 1 ≤ eig i * (∑ e, w e * (b i e)^2) := by
    intro i hi
    let v : I → ℝ := b i
    have hv : v ⬝ᵥ v=1 := by
      have hn := b.orthonormal.1 i
      have hb : inner ℝ (b i) (b i)=1 := by
        rw [real_inner_self_eq_norm_sq, hn]
        norm_num
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using hb
    have he : C *ᵥ v=eig i • v := hC.isHermitian.mulVec_eigenvectorBasis i
    have hs := hsecond v
    rw [he] at hs
    simp only [dotProduct_smul, smul_eq_mul, hv, mul_one, Pi.smul_apply] at hs
    have heq : (∑ e, w e*(eig i * v e)^2) =
        (eig i)^2 * (∑ e, w e*(v e)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      ring
    rw [heq] at hs
    have hp : 0 < eig i := lt_of_le_of_ne (heig i) (Ne.symm hi)
    nlinarith
  rw [hC.isHermitian.rank_eq_card_non_zero_eigs]
  calc
    (Fintype.card {i // eig i ≠ 0} : ℝ) = ∑ i : {i // eig i ≠ 0}, (1:ℝ) := by simp
    _ ≤ ∑ i : {i // eig i ≠ 0}, eig i * (∑ e, w e*(b i e)^2) :=
      Finset.sum_le_sum fun i _ => hone i i.property
    _ = ∑ i, eig i * (∑ e, w e*(b i e)^2) := by
      exact sum_subtype_supported (fun i => eig i ≠ 0)
        (fun i => eig i * (∑ e, w e*(b i e)^2))
        (by intro i hi; rw [not_ne_iff.mp hi, zero_mul])
    _ = ∑ e, w e * C e e := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [spectral_diagonal hC.isHermitian e, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp [eig, b]
      ring

end MatchingEntropy
end
end

end OAI
