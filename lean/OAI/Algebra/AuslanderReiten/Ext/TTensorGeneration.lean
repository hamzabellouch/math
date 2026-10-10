import OAI.Algebra.AuslanderReiten.Ext.TTensorActions

namespace OAI

noncomputable section
namespace ArExplicit.Resolution
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
variable [HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
variable (hq : q ≠ 0) (hq1 : 1+q ≠ 0) (h : NoPositivePowerOne q)
local notation "T₀" => ArExplicit.T k q
local notation "S₀" => ModuleCat.of T₀ (Simple q)

include hq hq1 h in
theorem tTensor_generation (n : ℕ) (z : tTensorCoefficients q (3*(n+1))) :
    ∃ u v : tTensorCoefficients q (3*n),
      z = ExternalTensor.coefficientFirst k T₀ T₀ S₀ S₀ S₀ S₀ (tExplicitP q) (3*n) u +
        ExternalTensor.coefficientSecond k T₀ T₀ S₀ S₀ S₀ S₀ (tExplicitP q) (3*n) v := by
  obtain ⟨⟨u,v⟩, huv⟩ := BinaryKoszul.row_surjective k n
    (tTensorCoefficientEquiv q hq hq1 h (n+1) z)
  refine ⟨(tTensorCoefficientEquiv q hq hq1 h n).symm u,
    (tTensorCoefficientEquiv q hq hq1 h n).symm v, ?_⟩
  apply (tTensorCoefficientEquiv q hq hq1 h (n+1)).injective
  rw [map_add, tTensorCoefficient_first, tTensorCoefficient_second,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact huv.symm

end ArExplicit.Resolution

end

end OAI
