import OAI.Combinatorics.PolynomialVacuum.Algebra.SpectralEigenvector
import OAI.Combinatorics.PolynomialVacuum.Cylinder.Resolvent

namespace OAI

namespace PolynomialVacuumAlgebra
namespace AnalyticVacuum
open Classical Filter
open scoped Topology

noncomputable def vacuumResolvent (N : ℕ) (X : Fin N → ℂ) : Matrix (Fin N → Spin) (Fin N → Spin) ℂ :=
  rowDenominator N X • 1-spectralMatrix N X+emptyMatrix N
noncomputable def normalizedVacuum (N : ℕ) (X : Fin N → ℂ) (s : Fin N → Spin) : ℂ :=
  (vacuumResolvent N X).adjugate s (fun _=>.zero)/(vacuumResolvent N X).det

theorem vacuumResolvent_one (N : ℕ) : vacuumResolvent (N+1) (fun _=>1)=
    exchangeDenominator t 1^(N+1) • (1-physicalTransfer (N+1) zeta)+emptyMatrix (N+1) := by
  simp only [vacuumResolvent,rowDenominator_one,spectralMatrix_one,smul_sub]

theorem vacuumResolvent_det_ne_zero (N : ℕ) : (vacuumResolvent N (fun _=>1)).det≠0 := by
  cases N with
  | zero =>
    have he : vacuumResolvent 0 (fun _=>1)=1 := by
      ext s r
      have hs : s=(fun _=>Spin.zero) := Subsingleton.elim _ _
      have hr : r=(fun _=>Spin.zero) := Subsingleton.elim _ _
      subst s; subst r
      simp [vacuumResolvent,rowDenominator,spectralMatrix,transferMatrix,rowKernel,
        trainDenominator,emptyMatrix,sum_spin,charge,PolynomialVacuumCylinder.zeta_eq_I]
    rw [he,Matrix.det_one]; exact one_ne_zero
  | succ N =>
    rw [vacuumResolvent_one]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp
      (physical_resolvent_isUnit N _ (pow_ne_zero _ honeycombDenominator_ne_zero))).ne_zero

theorem analytic_vacuumResolvent (N : ℕ) (X : Fin N → ℂ) (s r : Fin N → Spin) :
    AnalyticAt ℂ (fun Y=>vacuumResolvent N Y s r) X := by
  have hd:=analytic_trainDenominator N 0 t (extendData N) (fun j=>analytic_extendData N j X)
  have hm:=analytic_transferMatrix N zeta t (extendData N) (fun j=>analytic_extendData N j X) s r
  change AnalyticAt ℂ (fun Y=>rowDenominator N Y*(1 : Matrix _ _ ℂ) s r-spectralMatrix N Y s r+emptyMatrix N s r) X
  exact ((hd.mul analyticAt_const).sub hm).add analyticAt_const

theorem analytic_normalizedVacuum (N : ℕ) (s : Fin N → Spin) :
    AnalyticAt ℂ (fun X=>normalizedVacuum N X s) (fun _=>1) :=
  (analytic_matrix_adjugate _ (analytic_vacuumResolvent N _) s _).div
    (analytic_matrix_det _ (analytic_vacuumResolvent N _)) (vacuumResolvent_det_ne_zero N)

theorem vacuumResolvent_eventually_ne_zero (N : ℕ) :
    ∀ᶠ X in nhds (fun _ : Fin N => (1:ℂ)),(vacuumResolvent N X).det≠0 :=
  (analytic_matrix_det _ (analytic_vacuumResolvent N _)).continuousAt.eventually_ne (vacuumResolvent_det_ne_zero N)

theorem resolvent_fixed_relation (N : ℕ) (X : Fin N → ℂ) (v : (Fin N → Spin) → ℂ)
    (hv : (spectralMatrix N X).mulVec v=rowDenominator N X • v) (s : Fin N → Spin) :
    (vacuumResolvent N X).det*v s=(vacuumResolvent N X).adjugate s (fun _=>.zero)*v (fun _=>.zero) := by
  have ha : (vacuumResolvent N X).mulVec v=Pi.single (fun _=>.zero) (v (fun _=>.zero)) := by
    rw [vacuumResolvent,Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,hv,
      sub_self,zero_add,emptyMatrix_mulVec]
  have he:=congrArg (vacuumResolvent N X).adjugate.mulVec ha
  rw [Matrix.mulVec_mulVec,Matrix.adjugate_mul,Matrix.smul_mulVec,Matrix.one_mulVec] at he
  have hh:=congrFun he s
  simpa [Matrix.mulVec,dotProduct,Pi.single_apply] using hh

theorem normalizedVacuum_eq_ratio (N : ℕ) (X : Fin N → ℂ) (v : (Fin N → Spin) → ℂ)
    (hv : (spectralMatrix N X).mulVec v=rowDenominator N X • v)
    (hd : (vacuumResolvent N X).det≠0) (h0 : v (fun _=>.zero)≠0) (s : Fin N → Spin) :
    normalizedVacuum N X s=v s/v (fun _=>.zero) := by
  unfold normalizedVacuum
  apply (div_eq_div_iff hd h0).mpr
  simpa [mul_comm] using (resolvent_fixed_relation N X v hv s).symm

end AnalyticVacuum
end PolynomialVacuumAlgebra

end OAI
