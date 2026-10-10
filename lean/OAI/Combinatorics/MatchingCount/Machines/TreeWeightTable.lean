import Mathlib
import OAI.Combinatorics.MatchingCount.Machines.TreePhantom

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

def sourceWeights (x : BagBuildInput×ℕ) : List Fraction :=
  (sourceTables x.1).1.map (fun key=>sourceBagWeight (x,key))
def rowsWith {A B C : Type} [Codec A] [Codec B] [Codec C]
    {f : A×B→C} {g : A→List B} (F : Realizer f) (G : Realizer g) :
    Realizer (fun x=>(g x).map (fun b=>f (x,b))) :=
  composition (pair identity G) (mapWith F)
lemma polynomial_rowsWith {A B C : Type} [Codec A] [Codec B] [Codec C]
    {f : A×B→C} {g : A→List B} {F : Realizer f} {G : Realizer g}
    (hF : PolynomialTime F) (hG : PolynomialTime G) : PolynomialTime (rowsWith F G) :=
  polynomial_composition (polynomial_pair polynomial_identity hG) (polynomial_mapWith hF)
def sourceWeightsRealizer : Realizer sourceWeights := rowsWith sourceBagWeightRealizer
  (composition (first (A:=BagBuildInput) (B:=ℕ)) sourceTablesRealizer).fst
lemma polynomial_sourceWeights : PolynomialTime sourceWeightsRealizer :=
  polynomial_rowsWith polynomial_sourceBagWeight
    (polynomial_fst (polynomial_composition polynomial_first polynomial_sourceTables))
lemma sourceWeights_source {n : ℕ} [Nontrivial (Fin n)] (hn : 2≤n)
    (w : Fin n→Fin n→ℚ) (hw : ∀ a b,0≤w a b) (K D : ℕ) :
    sourceWeights ((((matrixRep w,List.replicate (2*K+2) false),List.range n),List.replicate (2*K) false),D)=
      List.ofFn (fun i=>TreeFraction.repr (RationalSource.bagWeight w K D
        (UnitRefresh.orderedEnum (Transport.BagEdge (RationalSource.bags w K)) i))) := by
  unfold sourceWeights
  dsimp only
  rw [sourceTables_catalog hn w hw K]
  unfold sourceCatalog
  rw [List.map_ofFn]
  congr 1
  funext i
  exact sourceBagWeight_source hn w hw K D _

open TreePost Turing

theorem sourceWeights_post : ∃ p : Polynomial ℕ,∀ x : BagBuildInput×ℕ,∀ t : ℕ,
    p.eval (packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (machine sourceWeightsRealizer.program) (packed x) coins).state=none ∧
      (run (machine sourceWeightsRealizer.program) (packed x) coins).tape.right₀=
        ListBlank.mk (packed (sourceWeights x)) :=
  polynomial_compiles sourceWeightsRealizer polynomial_sourceWeights
end MatchingFPRAS.ExecutableSource

end OAI
