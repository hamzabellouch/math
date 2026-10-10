import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff
open Finset Classical
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.Localization
open Matrix Finset
open scoped ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem norm_pow_le_gram_trace {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℂ) (m : ℕ) :
    ‖M‖^(2*m) ≤ ((M.conjTranspose*M)^m).trace.re := by
  let A := M.conjTranspose*M
  have hA : A.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self M
  let e := hA.isHermitian.eigenvalues
  have he : ∀ i,0≤e i := hA.eigenvalues_nonneg
  have hn : ‖A‖=‖fun i => (e i:ℂ)‖ := by
    conv_lhs => rw [hA.isHermitian.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply,←Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary,CStarRing.norm_coe_unitary_mul,Matrix.l2_opNorm_diagonal]
    rfl
  have ht : (A^m).trace.re=∑ i,e i^m := by
    have hp : A^m=Unitary.conjStarAlgAut ℂ _ hA.isHermitian.eigenvectorUnitary
        ((Matrix.diagonal (fun i => (e i:ℂ)))^m) := by
      rw [map_pow]
      congr 1
      exact hA.isHermitian.spectral_theorem
    rw [hp,Unitary.conjStarAlgAut_apply,Matrix.trace_mul_cycle,Unitary.coe_star_mul_self,
      one_mul,Matrix.diagonal_pow,Matrix.trace_diagonal]
    simp only [Complex.re_sum,Pi.pow_apply,←Complex.ofReal_pow,Complex.ofReal_re]
  obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image (univ:Finset ι) e univ_nonempty
  have hnorm : ‖fun i => (e i:ℂ)‖=e i := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (he i)).mpr
      intro j
      simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (he j)] using hmax j (mem_univ j)
    · have := norm_le_pi_norm (fun i => (e i:ℂ)) i
      simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (he i)] using this
  have hgram : ‖M‖^2=‖A‖ := by
    simpa only [A,pow_two] using (Matrix.l2_opNorm_conjTranspose_mul_self M).symm
  change ‖M‖^(2*m) ≤ (A^m).trace.re
  rw [pow_mul,hgram,hn,hnorm,ht]
  exact single_le_sum (fun j hj => pow_nonneg (he j) m) (mem_univ i)

end
end OrdinaryCorrelations.Localization

end

end OAI
