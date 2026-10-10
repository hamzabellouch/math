import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Data.Finsupp.SMul

namespace OAI

namespace InvariantProjection.ProductRotation

open scoped BigOperators

noncomputable def characterPhase {ι : Type*} (v : ι →₀ ℤ)
    (x : ι → UnitAddCircle) : UnitAddCircle :=
  v.sum (fun i n => n • x i)

noncomputable def productCharacter {ι : Type*} (v : ι →₀ ℤ) :
    C((ι → UnitAddCircle), ℂ) where
  toFun x := (AddCircle.toCircle (characterPhase v x) : ℂ)
  continuous_toFun := by
    apply continuous_subtype_val.comp
    apply AddCircle.continuous_toCircle.comp
    unfold characterPhase Finsupp.sum
    fun_prop

noncomputable def productFourierAlgebra (ι : Type*) :
    StarSubalgebra ℂ C((ι → UnitAddCircle), ℂ) :=
  StarAlgebra.adjoin ℂ (Set.range (productCharacter (ι := ι)))

end InvariantProjection.ProductRotation

end OAI
