import OAI.Analysis.Laughlin.FourBody.Coefficients
import OAI.Analysis.Laughlin.Spin.Specializations

namespace OAI

namespace Laughlin.Spin
open scoped Topology
open Filter

noncomputable def fourBodyLimitCoefficient (r D T p j k : ℕ) : ℝ :=
  if r ≤ j+k then Real.sqrt 2 *
    couplingPolynomialCoefficient (Real.sqrt (1/2)) (Real.sqrt (1/2)) r (j+k-r) j *
    couplingPolynomialCoefficient (Real.sqrt (1/2)) (Real.sqrt (1/2)) (D-r) (T-D) p else 0

theorem source_fourBody_coefficient_tendsto (r D T p j k : ℕ)
    (hrD : r ≤ D) (hDT : D ≤ T) (hT : p+j+k=T) :
    Tendsto (fun Q : ℕ => fourBodyCoefficient Q r D T p j k) atTop
      (𝓝 (fourBodyLimitCoefficient r D T p j k)) := by
  by_cases hr : r ≤ j+k
  · simp only [fourBodyCoefficient,fourBodyLimitCoefficient,ite_eq_left hr]
    have hI := source_fourBody_inner_coupling_tendsto r (j+k) j hr (by omega)
    have hO := source_fourBody_outer_coupling_tendsto r (D-r) (T-r) p (by omega) (by omega)
    have he : T-r-(D-r)=T-D := by omega
    rw [he] at hO
    exact (tendsto_const_nhds.mul hI).mul hO
  · simp only [fourBodyCoefficient,fourBodyLimitCoefficient,ite_eq_right hr]
    exact tendsto_const_nhds

end Laughlin.Spin

end OAI
