import OAI.Analysis.BoundedHochschild.TypeIMatrixColumns

namespace OAI

/-! Conversion between the two existing abelian-corner formulations. -/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open FinitePathMain HochschildComparison

variable {M : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

omit [PartialOrder M] [StarOrderedRing M] in
lemma popa_abelian_of_finitePath {p : M} (hp : AbelianProjection p) :
    PopaTypeII.AbelianProjection hp.1 := by
  have hc (a : PopaCorner.algebra hp.1) : p * (a : M) * p = (a : M) := by
    rw [a.property.1, a.property.2]
  intro a b
  apply Subtype.ext
  change (a : M) * (b : M) = (b : M) * (a : M)
  simpa only [hc] using (hp.2 (a : M) (b : M)).eq

omit [PartialOrder M] [StarOrderedRing M] in
lemma abelian_partialIso (v : PartialIso M) (hp : AbelianProjection v.initial) :
    AbelianProjection v.final :=
  finitePath_abelian_of_popa v.final_proj
    (abelianProjection_partialIso v (popa_abelian_of_finitePath hp))

end KadisonRingrose
end BoundedHochschild

end

end OAI
