import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nuclearity.NuclearUnitization
import OAI.Analysis.JiangSu.CentralSequences.TracialMatrixModelSaturation
import OAI.Analysis.JiangSu.Comparison.FamilyProjectionComparison
import OAI.Analysis.JiangSu.Nonunital.ProjectionStrictComparison
import OAI.Analysis.JiangSu.Nonunital.UniformGamma

namespace OAI

section

noncomputable section
namespace NonunitalGamma
open Pureness CurrentMain DirectPacking Filter
open scoped ComplexOrder

variable {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (NormalizedTrace A)] [TopologicalSpace.SeparableSpace A]
variable [CompactSpace (NormalizedTrace A)] (U : Ultrafilter ℕ)
local notation "T" => (fun τ : NormalizedTrace A => NormalizedTrace.unitized τ)
local notation "D" => FamilyUltrapower T U
local notation "L" => familyLimitTrace T U
local notation "ι" => familyUltrapowerMap T U

 theorem comparison_central_matrix (hfree : (U : Filter ℕ)≤atTop)
    (hsimple : NonunitalGamma.TopologicallySimple A) (hstable : StablyProjectionless A)
    (hcone : AllDenselyFiniteTracesBounded A) (hcmp : NonunitalGamma.StrictComparison hcone)
    (hnuc : NuclearUnitization.IsNuclear A) (m : ℕ) (hm : 0 < m) :
    ∃ η : CStarMatrix (Fin m) (Fin m) ℂ →⋆ₐ[ℂ] D,
      ∀ M (a : A),Commute (η M) (ι (Unitization.inr a)) := by
  let : TopologicalSpace.SeparableSpace (Unitization ℂ A) :=
    (Unitization.uniformEquivProd (𝕜 := ℂ) (A := A)).symm.surjective.denseRange.separableSpace
      (Unitization.uniformEquivProd (𝕜 := ℂ) (A := A)).symm.continuous
  have hsupply : DirectComparison.SpectralProjectionSupply L :=
    projection_supply U hfree hsimple hstable.projectionless hcone hcmp
  have hnu := NuclearUnitization.nuclear_unitization hnuc
  have hstrict : ∀ {p q : D},IsStarProjection p → IsStarProjection q →
      ∀ {c : ℝ},0<c → (∀ s : ℕ → NormalizedTrace A,((L s).functional p).re+2*c≤((L s).functional q).re) →
        ∃ v : D,star v*v=p ∧ q*v=v :=
    fun {p q} hp hq {c} hc hgap => tracial_projection_strict_comparison U hfree hcone hcmp hp hq hc hgap
  obtain ⟨η,hη⟩ := central_matrix_of_tracial_models T U hfree m (by
    intro K ε hε
    obtain ⟨v⟩ := FamilyProjection.comparison_finite_matrix_models T U hfree hsupply hnu hstrict m hm K hε
    exact tracial_matrix_model_extract T U v)
  exact ⟨η,fun M a => hη M (Unitization.inr a)⟩

end NonunitalGamma

end
end

end OAI
