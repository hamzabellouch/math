import OAI.Analysis.Cotype.MainConstruction
import OAI.Analysis.Cotype.TypeUniformL1

namespace OAI

noncomputable section
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] [Nontrivial X]

theorem bConvex_of_AP_cotype_cotype (hAP : ApproximationProperty X)
    (hX : FiniteCotype X) (hXd : FiniteCotype (X →L[ℝ] ℝ)) : BConvex X :=
  bConvex_of_not_uniformL1 (not_uniformL1_of_no_cube
    (no_uniform_l1_of_AP_cotype_cotype hAP hX hXd))

theorem nontrivialType_of_AP_cotype_cotype (hAP : ApproximationProperty X)
    (hX : FiniteCotype X) (hXd : FiniteCotype (X →L[ℝ] ℝ)) : NontrivialType X :=
  nontrivialType_of_bConvex (bConvex_of_AP_cotype_cotype hAP hX hXd)

end Cotype

end

end OAI
