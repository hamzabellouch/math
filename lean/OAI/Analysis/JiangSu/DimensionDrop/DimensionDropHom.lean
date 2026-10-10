import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropGeneratedHom
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropRelations2

namespace OAI

section

noncomputable section
namespace NonunitalSI
open Pureness CurrentMain NonunitalGamma Filter Topology CompletelyPositiveOperations JiangSuConstruction
open scoped ComplexOrder ENNReal CStarAlgebra

variable {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (NormalizedTrace A)] [CompactSpace (NormalizedTrace A)] [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)]
local notation "Fω" => CentralSequenceAlgebra (A := A) U
local instance (p q : ℕ) : Semiring (DimensionDrop p q) :=
  (inferInstance : CStarAlgebra (DimensionDrop p q)).toSemiring

 theorem comparison_dimension_drop_hom
    (hnuc : NuclearUnitization.IsNuclear.{0,0} A) (hsimple : NonunitalGamma.TopologicallySimple A)
    (hstable : StablyProjectionless A)
    (hcone : AllDenselyFiniteTracesBounded A) (hcmp : NonunitalGamma.StrictComparison hcone)
    (n : ℕ) (hn : 0<n) :
    Nonempty (DimensionDrop (n+1) n →⋆ₐ[ℂ] Fω) := by
  obtain ⟨φ,s,hφn,hφrel,_hsn,hse,hsF,_hφ1⟩ := comparison_dimension_drop_relations U
    hnuc hsimple hstable hcone hcmp n hn
  let w : DimensionDropRelations.Witness (B := Fω) (⟨0,hn⟩ : Fin n) :=
    { φ := φ
      contractive := hφn
      orderZero := hφrel
      s := s
      small := hse
      support := hsF }
  exact ⟨w.dimensionDropHom⟩

end NonunitalSI

end
end

section

noncomputable section
namespace NonunitalSI
open Pureness CurrentMain NonunitalGamma Filter Topology JiangSuConstruction
open scoped ComplexOrder ENNReal CStarAlgebra

variable {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (NormalizedTrace A)] [CompactSpace (NormalizedTrace A)] [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)]
local instance (p q : ℕ) : Semiring (DimensionDrop p q) :=
  (inferInstance : CStarAlgebra (DimensionDrop p q)).toSemiring

 theorem comparison_prime_drop_hom
    (hnuc : NuclearUnitization.IsNuclear.{0,0} A) (hsimple : NonunitalGamma.TopologicallySimple A)
    (hstable : StablyProjectionless A)
    (hcone : AllDenselyFiniteTracesBounded A) (hcmp : NonunitalGamma.StrictComparison hcone)
    (p q : ℕ) (hp : 0<p) (hq : 0<q) (hco : p.Coprime q) :
    Nonempty (DimensionDrop p q →⋆ₐ[ℂ] CentralSequenceAlgebra (A := A) U) := by
  obtain ⟨n,hn,⟨ψ⟩⟩ := prime_drop_into_consecutive hp hq hco
  obtain ⟨φ⟩ := comparison_dimension_drop_hom U hnuc hsimple hstable hcone hcmp n hn
  exact ⟨φ.comp ψ⟩

end NonunitalSI

end
end

end OAI
