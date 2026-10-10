import OAI.Algebra.Finitistic.Localization.SourceVerdier

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.SourceVerdier
universe u
variable {k : Type u} [Field k] {d t : ℕ} (P : QuadraticEncoding.Relations k d t)

open scoped ModuleCat.Algebra in
instance linearProj : Linear k (Proj P) := inferInstance
instance linearK : Linear k (K P) := inferInstance
instance linearQ : Linear k (Q P) := inferInstance
instance linearQuotient : (q P).Linear k := inferInstance

end LittleFinitistic.SourceVerdier

end

end OAI
