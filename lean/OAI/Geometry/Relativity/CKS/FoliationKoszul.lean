import OAI.Geometry.Relativity.CKS.FoliationFirstJet

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open Matrix
open scoped BigOperators

 def lowerKoszul (dg : Fin 3 → AmbientMat) (i j k : Fin 3) : ℝ :=
  (dg i j k+dg j i k-dg k i j)/2

 def normalCovariantFirstJet (U : ℝ) (γ : Mat) (s : Point)
    (dU : Fin 3 → ℝ) (dγ : Fin 3 → Mat) (ds : Fin 3 → Point)
    (i k : Fin 3) : ℝ :=
  ∑ j, (foliationMetric U γ s j k*foliationNormalDerivative U s (dU i) (ds i) j+
    foliationNormal U s j * lowerKoszul
      (fun t => foliationMetricDerivative U γ s (dU t) (dγ t) (ds t)) i j k)

theorem foliation_chi_koszul {U : ℝ} (_hU : U ≠ 0) {γ : Mat} (hγ : γ.IsHermitian)
    (s : Point) (dU : Fin 3 → ℝ) (dγ : Fin 3 → Mat) (ds : Fin 3 → Point)
    (hdγ : ∀ i, (dγ i).IsHermitian) (a b : Fin 2) :
    normalCovariantFirstJet U γ s dU dγ ds a.succ b.succ =
      U/2 * (dγ 0 a b - ∑ c, (s c*dγ c.succ a b+
        γ c b*ds a.succ c+γ a c*ds b.succ c)) := by
  fin_cases a <;> fin_cases b <;>
    simp [normalCovariantFirstJet,lowerKoszul,foliationMetric,foliationMetricDerivative,
      foliationNormal,foliationNormalDerivative,metricBlock,Matrix.of_apply,
      Fin.sum_univ_three,Fin.sum_univ_two,
      hermitian_real_symmetry hγ 0 1,
      hermitian_real_symmetry (hdγ 0) 0 1,
      hermitian_real_symmetry (hdγ 1) 0 1,
      hermitian_real_symmetry (hdγ 2) 0 1]
  all_goals field_simp [_hU]
  all_goals ring

theorem foliation_acceleration_koszul {U : ℝ} (hU : U ≠ 0) {γ : Mat} (hγ : γ.IsHermitian)
    (s : Point) (dU : Fin 3 → ℝ) (dγ : Fin 3 → Mat) (ds : Fin 3 → Point)
    (hdγ : ∀ i, (dγ i).IsHermitian) (a : Fin 2) :
    (∑ i, foliationNormal U s i * normalCovariantFirstJet U γ s dU dγ ds i a.succ)=
      dU a.succ/U := by
  fin_cases a <;>
    simp [normalCovariantFirstJet,lowerKoszul,foliationMetric,foliationMetricDerivative,
      foliationNormal,foliationNormalDerivative,metricBlock,Matrix.of_apply,
      Fin.sum_univ_three,Fin.sum_univ_two,
      hermitian_real_symmetry hγ 0 1,
      hermitian_real_symmetry (hdγ 0) 0 1,
      hermitian_real_symmetry (hdγ 1) 0 1,
      hermitian_real_symmetry (hdγ 2) 0 1]
  all_goals field_simp [hU]
  all_goals ring

end
end CKSAngularGeometry

end

end OAI
