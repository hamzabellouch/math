import Mathlib
import OAI.Analysis.SymmetricDomains.NashCellIntrinsicRank
import OAI.Analysis.SymmetricDomains.SemialgebraicBoundaryFiniteNash
import OAI.Analysis.SymmetricDomains.CenteredChartGerms
import OAI.Analysis.SymmetricDomains.Centered

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Topology MeasureTheory
open scoped Classical

theorem isSemialgebraic_centered_nash_cover {n : ℕ} {S : Set (Affine n)} (hS : IsSemialgebraic S) :
    ∃ C : Finset (NashPatch (n+n)), (∀ p ∈ C, 0 ∈ p.domain) ∧
      ∀ z, z ∈ S ↔ ∃ p ∈ C, z ∈ p.complexMap '' p.domain := by
  obtain ⟨C,h0,hC⟩ := (polynomialSignSet_finite_nash_cover (n+n) _ (isSemialgebraic_real_image hS)).centered
  refine ⟨C,h0,fun z => ?_⟩
  rw [← (complexRealEquiv n).injective.mem_set_image,hC]
  apply exists_congr
  intro p
  apply and_congr_right
  intro _
  change (∃ x ∈ p.domain, p.toFun x = complexRealEquiv n z) ↔
    ∃ x ∈ p.domain, (complexRealEquiv n).symm (p.toFun x) = z
  apply exists_congr
  intro x
  apply and_congr_right
  intro _
  exact (complexRealEquiv n).symm_apply_eq.symm

namespace NashPatch
noncomputable def complexRank {n : ℕ} (p : NashPatch (n+n)) (x : Fin p.dim → ℝ) : ℕ :=
  Matrix.rank (fun j i => fderiv ℝ (fun y => p.complexMap y j) x (Pi.single i 1))

theorem principal_rank_dichotomy {n m : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (Q : MvPolynomial (Fin n) ℂ)
    (hcharts : ∀ q ∈ MvPolynomial.zeroLocus ℂ I, MvPolynomial.eval q Q ≠ 0 →
      ∃ W : Set (Affine n), W ⊆ MvPolynomial.zeroLocus ℂ I ∧
        IsOpen ((Subtype.val : MvPolynomial.zeroLocus ℂ I → Affine n) ⁻¹' W) ∧ q ∈ W ∧
        ∃ B : Set (Affine m), IsOpen B ∧ Nonempty (Biholomorph W B))
    (p : NashPatch (n+n)) (h0 : 0 ∈ p.domain)
    (hpI : ∀ x ∈ p.domain, p.complexMap x ∈ MvPolynomial.zeroLocus ℂ I)
    (hpQ : ∀ x ∈ p.domain, MvPolynomial.eval (p.complexMap x) Q ≠ 0) :
    (∃ P : MvPolynomial (Fin n) ℂ, P ∉ I ∧
      ∀ x ∈ p.domain, MvPolynomial.eval (p.complexMap x) P = 0) ∨
      volume {x | x ∈ p.domain ∧ p.complexRank x < m} = 0 := by
  obtain ⟨W,hWI,hW,hpW,B,hB,⟨e⟩⟩ := hcharts _ (hpI 0 h0) (hpQ 0 h0)
  obtain ⟨F,G,hF0,hF,hG,hGF,_hFG,hFV⟩ := e.centered_chart_germs hWI hW hB hpW
  rcases nash_cell_intrinsic_rank_dichotomy (MvPolynomial.zeroLocus ℂ I) F G hF
    (hF0 ▸ hG) hGF hFV p.domain p.isOpen_domain p.isConnected_domain.isPreconnected h0
    p.complexMap p.analytic_complexMap hpI p.semialgebraic_complexMap_re p.semialgebraic_complexMap_im with h | h
  · left
    obtain ⟨P,⟨y,hy,hyP⟩,hpP⟩ := h
    exact ⟨P,fun hPI => hyP (hy P hPI),hpP⟩
  · exact Or.inr h

end NashPatch
end

open Set
open scoped Classical

theorem complex_polynomial_real_syntax {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    ∃ A B : MvPolynomial (Fin n ⊕ Fin n) ℝ, ∀ z : Affine n,
      MvPolynomial.eval (realCoordinates z) A = (MvPolynomial.eval z P).re ∧
      MvPolynomial.eval (realCoordinates z) B = (MvPolynomial.eval z P).im := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨MvPolynomial.C a.re,MvPolynomial.C a.im,by simp⟩
  | add P Q hp hq =>
    obtain ⟨A,B,h⟩ := hp
    obtain ⟨C,D,k⟩ := hq
    exact ⟨A+C,B+D,by intro z; simp only [map_add,Complex.add_re,Complex.add_im,(h z).1,(h z).2,(k z).1,(k z).2]; trivial⟩
  | mul_X P j hp =>
    obtain ⟨A,B,h⟩ := hp
    refine ⟨A*MvPolynomial.X (.inl j)-B*MvPolynomial.X (.inr j),
      A*MvPolynomial.X (.inr j)+B*MvPolynomial.X (.inl j),?_⟩
    intro z
    simp only [map_sub,map_mul,map_add,MvPolynomial.eval_X,Complex.mul_re,Complex.mul_im]
    rw [(h z).1,(h z).2]
    exact ⟨rfl,by dsimp [realCoordinates]⟩

lemma isSemialgebraic_polynomial_zero {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    IsSemialgebraic {z : Affine n | MvPolynomial.eval z P = 0} := by
  obtain ⟨A,B,h⟩ := complex_polynomial_real_syntax P
  convert (IsSemialgebraic.zero A).inter (IsSemialgebraic.zero B) using 1
  ext z
  simp only [mem_inter_iff,mem_ofPred_eq,(h z).1,(h z).2,Complex.ext_iff,Complex.zero_re,Complex.zero_im]

lemma isSemialgebraic_polynomial_nonzero {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    IsSemialgebraic {z : Affine n | MvPolynomial.eval z P ≠ 0} :=
  (isSemialgebraic_polynomial_zero P).compl

end Release061

end

end OAI
