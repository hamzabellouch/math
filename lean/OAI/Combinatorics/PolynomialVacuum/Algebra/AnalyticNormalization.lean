import OAI.Combinatorics.PolynomialVacuum.Algebra.AnalyticResolvent
import OAI.Combinatorics.PolynomialVacuum.Algebra.EmptyNonzero
import OAI.Combinatorics.PolynomialVacuum.Pairing.PairingTarget

namespace OAI

namespace PolynomialVacuumAlgebra
namespace AnalyticVacuum
open Classical Filter
open scoped Topology

theorem normalizedVacuum_homogeneous (N : ℕ) (s : Fin (N+1) → Spin) :
    normalizedVacuum (N+1) (fun _=>1) s=physicalProjection N s (fun _=>.zero) := by
  let v : (Fin (N+1) → Spin) → ℂ:=fun r=>physicalProjection N r (fun _=>.zero)
  have hv : (spectralMatrix (N+1) (fun _=>1)).mulVec v=rowDenominator (N+1) (fun _=>1) • v := by
    rw [spectralMatrix_one,rowDenominator_one,Matrix.smul_mulVec]
    congr 1
    funext r
    exact congrFun (congrFun (physicalProjection_left_fixed N) r) (fun _=>.zero)
  have he:=normalizedVacuum_eq_ratio (N+1) (fun _=>1) v hv (vacuumResolvent_det_ne_zero _) (by simp [v]) s
  simpa [v] using he

@[simp] theorem normalizedVacuum_empty (N : ℕ) : normalizedVacuum N (fun _=>1) (fun _=>.zero)=1 := by
  cases N with
  | zero =>
    have hv : (spectralMatrix 0 (fun _=>1)).mulVec (fun _=>1)=rowDenominator 0 (fun _=>1) • (fun _=>1) := by
      funext s
      simp [spectralMatrix,transferMatrix,rowKernel,rowDenominator,trainDenominator,
        Matrix.mulVec,dotProduct,sum_spin,charge,PolynomialVacuumCylinder.zeta_eq_I]
    simpa using normalizedVacuum_eq_ratio 0 (fun _=>1) (fun _=>1) hv (vacuumResolvent_det_ne_zero 0) one_ne_zero (fun _=>.zero)
  | succ N => rw [normalizedVacuum_homogeneous,physicalProjection_empty]

theorem normalizedVacuum_eventually_ratio (N : ℕ) (s : Fin N → Spin) :
    ∀ᶠ X in nhds (fun _ : Fin N => (1:ℂ)),
      MvPolynomial.eval X (polynomialVacuum N (fun _=>Spin.zero))≠0 →
      normalizedVacuum N X s=MvPolynomial.eval X (polynomialVacuum N s)/MvPolynomial.eval X (polynomialVacuum N (fun _=>Spin.zero)) := by
  filter_upwards [fusion_eventually_ne_zero N,vacuumResolvent_eventually_ne_zero N] with X hf hd
  intro h0
  exact normalizedVacuum_eq_ratio N X (spectralPolynomial N X) (spectralPolynomial_eigen N X hf) hd h0 s

 

theorem actual_analytic_normalization :
    PolynomialVacuumCylinder.AnalyticNormalization polynomialVacuum normalizedVacuum :=
  ⟨polynomialVacuum_empty_ne_zero,analytic_normalizedVacuum,
    normalizedVacuum_eventually_ratio,normalizedVacuum_empty⟩
end AnalyticVacuum
end PolynomialVacuumAlgebra

end OAI
