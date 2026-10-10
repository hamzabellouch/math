import OAI.Analysis.BernoulliCone.StationarityDensity

namespace OAI

universe uE

section
noncomputable section
open Set Filter
namespace Bernoulli.Shape
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma rankOneMap_det (a : E →L[ℝ] ℝ) (e : E) (t : ℝ) :
    (rankOneMap a e t).det = 1+t*a e := by
  classical
  let b := Module.finBasis ℝ E
  let u := fun i => t * b.repr e i
  let v := fun j => a (b j)
  have hm : LinearMap.toMatrix b b (rankOneMap a e t).toLinearMap =
      1 + Matrix.replicateCol Unit u * Matrix.replicateRow Unit v := by
    ext i j
    simp only [LinearMap.toMatrix_apply]
    change b.repr (rankOneMap a e t (b j)) i = _
    rw [rankOneMap_apply]
    simp [u,v,Matrix.mul_apply,Matrix.one_apply,smul_eq_mul,Finsupp.single_apply]
    split_ifs <;> simp_all <;> ring
  rw [ContinuousLinearMap.det,← LinearMap.det_toMatrix b,hm,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  congr 1
  change (∑ i, a (b i) * (t * b.repr e i)) = t*a e
  calc
    _ = t * (∑ i, b.repr e i * a (b i)) := by rw [Finset.mul_sum]; congr 1; ext i; ring
    _ = t*a (∑ i, b.repr e i • b i) := by simp only [map_sum,map_smul,smul_eq_mul]
    _ = _ := by rw [b.sum_repr]
end Bernoulli.Shape

end
end

end OAI
