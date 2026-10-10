import OAI.Analysis.FreeEntropy.SpectralParameters

namespace OAI

noncomputable section
open Finset
open scoped ComplexConjugate
namespace FiniteEntropySeparation
variable {p d : ℕ} [NeZero p]
 theorem spectralGood_blocks (hd : 0<d) {δ Δ : ℝ} (hδ : 0<δ) (hΔ : 0<Δ) (hδΔ : δ≤Δ/4)
    (hsep : ∀i j : Fin p,i≠j → Δ≤|equidiscreteAtom p i-equidiscreteAtom p j|)
    (hq : ∀l : Fin p,∀r : ℝ,|r-equidiscreteAtom p l|≤δ → (3:ℝ)/4≤((spectralBasis p l).eval r)^2)
    (a : MatrixCoordinates (p+1) d) (ha : spectralGood p δ Δ (matrixMoment a)) :
    ∃f : Fin d → Fin p,balancedBlocks f ∧ ∃U : unitary (Matrix (Fin d) (Fin d) ℂ),
      (p:ℝ)*d/2≤‖coordinateMask (blockMask f) (rotateCoordinates U a)‖^2 := by
  classical
  let x := (hermitianMatrix_isHermitian a (Fin.last p)).eigenvalues
  let U := (hermitianMatrix_isHermitian a (Fin.last p)).eigenvectorUnitary
  let b := rotateCoordinates U a
  let y := equidiscreteAtom p
  let f := clusterLabel y δ x
  have hd' : (0:ℝ)<d := by exact_mod_cast hd
  have hp' : (0:ℝ)<p := by exact_mod_cast NeZero.pos p
  have hdiag : hermitianMatrix b (Fin.last p)=Matrix.diagonal (fun j => (x j:ℂ)) := diagonal_eigenvalues a _
  have hm (l : Fin p) : (∑j : Fin d,((spectralBasis p l).eval (x j))^2)≤9*(d:ℝ)/(8*p) := by
    have hh := ha.2.1 l
    rw [univariateMoment_matrix] at hh
    simp only [Polynomial.eval_pow] at hh
    have hh' := mul_lt_mul_of_pos_left hh hd'
    rw [← mul_assoc,mul_inv_cancel₀ (ne_of_gt hd'),one_mul] at hh'
    exact hh'.le.trans_eq (by ring)
  have hb : ((badSpectrum y δ x).card:ℝ)≤badFraction p*d := by
    have hh := ha.2.2
    rw [univariateMoment_matrix] at hh
    simp only [Polynomial.eval_pow,spectralAnnihilator_eval] at hh
    have hh' := mul_lt_mul_of_pos_left hh hd'
    rw [← mul_assoc,mul_inv_cancel₀ (ne_of_gt hd'),one_mul] at hh'
    have hb' := (badSpectrum_product_bound y hδ.le x).trans hh'.le
    have he : (d:ℝ)*(badFraction p*δ^(2*p))=(badFraction p*d)*δ^(2*p) := by ring
    rw [he] at hb'
    exact (mul_le_mul_iff_left₀ (pow_pos hδ _)).mp hb'
  have hb1 : ((badSpectrum y δ x).card:ℝ)≤(d:ℝ)/(2*p) := by
    apply hb.trans
    have hh := mul_le_mul_of_nonneg_right (min_le_right (1/4096:ℝ) (1/(2*p))) hd'.le
    simpa [badFraction,mul_comm,div_eq_mul_inv] using hh
  have hb2 : ((badSpectrum y δ x).card:ℝ)≤(d:ℝ)/4096 := by
    apply hb.trans
    have hh := mul_le_mul_of_nonneg_right (min_le_left (1/4096:ℝ) (1/(2*p))) hd'.le
    simpa [badFraction,mul_comm,div_eq_mul_inv] using hh
  have hf : balancedBlocks f := by
    intro l
    have hh := clusterLabel_rank_bound y δ x (fun l r => (spectralBasis p l).eval r) hq hm hb1 l
    exact_mod_cast hh
  refine ⟨f,hf,U,?_⟩
  rw [blockMask_matrixEnergy]
  have henergy (i : Fin p) : (d:ℝ)/2≤∑j : Fin d,∑k : Fin d,if f j=f k then Complex.normSq (hermitianMatrix b i.castSucc j k) else 0 := by
    let A := hermitianMatrix b i.castSucc
    have hA : A.IsHermitian := hermitianMatrix_isHermitian b i.castSucc
    have hsecond : 3*(d:ℝ)/4≤hsNorm A^2 := by
      have hh := (ha.1 i).1
      rw [← matrixMoment_rotate U a, matrixMoment_second_hs] at hh
      have hh' := mul_lt_mul_of_pos_left hh hd'
      rw [← mul_assoc,mul_inv_cancel₀ (ne_of_gt hd'),one_mul] at hh'
      exact le_of_lt (by convert hh' using 1 ; ring)
    have hfour : (Matrix.trace (A^4)).re≤4*(d:ℝ) := by
      have hh := (ha.1 i).2.1
      rw [← matrixMoment_rotate U a,matrixMoment_fourth_trace] at hh
      have hh' := mul_lt_mul_of_pos_left hh hd'
      rw [← mul_assoc,mul_inv_cancel₀ (ne_of_gt hd'),one_mul] at hh'
      exact hh'.le.trans_eq (by ring)
    have hc : (∑j : Fin d,∑k : Fin d,(x j-x k)^2*Complex.normSq (A j k))≤Δ^2*d/64 := by
      have hh := (ha.1 i).2.2
      have he : commutatorMoment (matrixMoment b) i.castSucc (Fin.last p)=commutatorMoment (matrixMoment a) i.castSucc (Fin.last p) := by
        unfold commutatorMoment
        simp only [b,matrixMoment_rotate]
      rw [← he,commutatorMoment_matrix,hdiag,hsNorm_sq] at hh
      simp only [commutator_diagonal_entry] at hh
      have hh' := mul_lt_mul_of_pos_left hh hd'
      rw [← mul_assoc,mul_inv_cancel₀ (ne_of_gt hd'),one_mul] at hh'
      exact hh'.le.trans_eq (by ring)
    apply clustered_energy_lower y δ Δ x hsep hδΔ hΔ (fun j k => Complex.normSq (A j k))
      (fun j k => Complex.normSq_nonneg _) (hermitian_entry_symmetric A hA)
    · simpa only [hsNorm_sq] using hsecond
    · exact (hermitian_row_fourth A hA).trans hfour
    · exact hc
    · exact hb2
  have hh := sum_le_sum (fun i (_ : i∈(univ:Finset (Fin p))) => henergy i)
  simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_div_assoc] using hh
end FiniteEntropySeparation

end

end OAI
