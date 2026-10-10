import OAI.Analysis.BernoulliCone.FoliationDifferential

namespace OAI

universe uE

section
noncomputable section
open Set Filter
open scoped Topology ContDiff Laplacian
namespace Bernoulli.ScalarLaplacian
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
lemma laplacian_comp_smul {f:E→ℝ} {x:E} (a:ℝ) (hf:ContDiffAt ℝ 2 f (a • x)) :
    Δ (fun y=>f (a • y)) x=a^2*Δ f (a • x) := by
  have hg:ContDiffAt ℝ 2 (fun y:E=>f (a • y)) x:=
    hf.comp x (contDiffAt_const.smul contDiffAt_id)
  rw [laplacian_sum_line hg,laplacian_sum_line hf,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  let v:=stdOrthonormalBasis ℝ E i
  have he:(fun t:ℝ=>f (a • (x+t • v)))=(fun t:ℝ=>f (a • x+t • (a • v))) := by
    ext t
    rw [smul_add,smul_comm a t v]
  change deriv (deriv (fun t:ℝ=>f (a • (x+t • v)))) 0 = _
  rw [he,Axisymmetric.line_second_derivative hf,Axisymmetric.line_second_derivative hf]
  simp only [map_smul,smul_apply,smul_eq_mul]
  ring
end Bernoulli.ScalarLaplacian

end
end

end OAI
