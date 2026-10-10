import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ComplexMatrix

namespace OAI


noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution MeasureTheory LineDeriv
open scoped SchwartzMap LineDeriv
variable {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
variable {ι : Type*} [Fintype ι] {n : ℕ}

lemma entries_lowerOrder (e : ι → D) (b : ι → Fin n → Fin n → 𝓢(D,ℂ))
    (c : Fin n → Fin n → 𝓢(D,ℂ)) (u : 𝓢'(D,C n)) :
    (∑ i, multiply (b i) (∂_{e i} u)) + multiply c u =
      matrixLowerOrder (fun q : ι × Fin n × Fin n => b q.1 q.2.1 q.2.2)
        (fun q => unit n n q.2.1 q.2.2) (fun q => e q.1)
        (fun q : Fin n × Fin n => c q.1 q.2) (fun q => unit n n q.1 q.2) u := by
  simp only [matrixLowerOrder,Fintype.sum_prod_type,multiply,_root_.sum_apply,
    ContinuousLinearMap.comp_apply]

end TamingCompatibility.ComplexMatrix

end

end OAI
