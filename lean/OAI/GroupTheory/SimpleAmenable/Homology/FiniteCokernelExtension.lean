import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.ReducedTensorTwo

namespace OAI

section
open CategoryTheory Limits HomologicalComplex
namespace ChainComplex
open scoped _root_.ChainComplex

variable {R:Type} [CommRing R] (K:ChainComplex (ModuleCat.{0} R) ℕ)
lemma finite_of_boundary_annihilation (hK:K.d 1 0=0) {S:ModuleCat.{0} R} (T:K.X 1⟶S) [Epi T]
    (N:Submodule R S) [Module.Finite R N] [Module.Finite R (K.homology 1)]
    (h:K.d 2 1 ≫ T ≫ ModuleCat.ofHom N.mkQ=0) : Module.Finite R S := by
  let c:=CokernelCofork.ofπ (T≫ModuleCat.ofHom N.mkQ) h
  let f:K.homology 1 ⟶ ModuleCat.of R (S⧸N):=(positiveIsCokernel K 0 hK).desc c
  have hf:positiveπ K 0 hK ≫ f=T≫ModuleCat.ofHom N.mkQ:=
    Cofork.IsColimit.π_desc (positiveIsCokernel K 0 hK) (t := c)
  have : Epi (ModuleCat.ofHom N.mkQ):=(ModuleCat.epi_iff_surjective _).mpr N.mkQ_surjective
  have : Epi (positiveπ K 0 hK ≫ f):=by rw [hf]; infer_instance
  have : Epi f:=epi_of_epi (positiveπ K 0 hK) _
  have : Module.Finite R (S⧸N):=Module.Finite.of_surjective f.hom ((ModuleCat.epi_iff_surjective f).mp inferInstance)
  exact Module.Finite.of_submodule_quotient N
end ChainComplex

end

end OAI
