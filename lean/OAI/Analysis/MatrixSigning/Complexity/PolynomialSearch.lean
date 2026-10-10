import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialScalar
import OAI.Analysis.MatrixSigning.Realization.SearchRealization
import OAI.Analysis.MatrixSigning.Complexity.PolynomialCeiling
import OAI.Analysis.MatrixSigning.Complexity.PolynomialRoundedStep

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
instance poly_searchView : PolyTime searchView := by unfold searchView;apply poly_reindex
instance poly_searchPencil : PolyTime searchPencil := by unfold searchPencil;apply poly_then
instance poly_searchParameters : PolyTime searchParameters := by unfold searchParameters;apply poly_then
instance poly_searchY : PolyTime searchY := by unfold searchY;apply poly_then
instance poly_searchDim : PolyTime searchDim := by unfold searchDim;infer_instance
instance poly_searchStep : PolyTime searchStepRealizes := by unfold searchStepRealizes;apply poly_div
instance poly_searchMesh : PolyTime searchMeshRealizes := by unfold searchMeshRealizes;apply poly_div
instance poly_searchInit : PolyTime searchInit := by unfold searchInit;apply poly_changeOutput

variable {ι : Type*} {L : ι → ℕ}
lemma runsPoly_searchFuel (a : ι → SearchState)
    (ha : IsPoly L (fun i => (searchStateCode (a i)).length))
    (hn : IsPoly L (fun i => RationalSDP.searchFuel (a i).n (a i).r (a i).R)) :
    RunsPoly L searchFuelRealizes a := by
  unfold searchFuelRealizes
  apply RunsPoly.then_poly
  let expr := ((constant searchStateCode ratCode 4).mul
    ((searchParameters.then (second ratCode ratCode)).pow 2)).div (searchStepRealizes.pow 2)
  have hp := RunsPoly.of_poly expr a ha
  apply RunsPoly.then hp
  apply runsPoly_ratCeil
  · exact hp.output
  · apply hn.mono
    intro i
    change ⌈4*(a i).R^2/(RationalSDP.searchStep (a i).n (a i).r)^2⌉₊≤_
    exact Nat.le_succ _
lemma runsPoly_search (a : ι → SearchState)
    (ha : IsPoly L (fun i => (searchStateCode (a i)).length))
    (hn : IsPoly L (fun i => RationalSDP.searchFuel (a i).n (a i).r (a i).R)) :
    RunsPoly L search a := by
  unfold search
  apply RunsPoly.congr
  exact (((runsPoly_searchFuel a ha hn).both (RunsPoly.of_poly searchInit a ha)).then_poly
    pencilNext.iterate).then_poly stateY

def searchResource (s : SearchState) : ℕ := (searchStateCode s).length+RationalSDP.searchFuel s.n s.r s.R
lemma search_cost_bound : ∃p : NaturalPolynomial,∀s,search.cost s≤p.eval (searchResource s) := by
  have hw : IsPoly searchResource (fun s => (searchStateCode s).length) :=
    (isPoly_self searchResource).mono (fun _ => Nat.le_add_right _ _)
  have hn : IsPoly searchResource (fun s => RationalSDP.searchFuel s.n s.r s.R) :=
    (isPoly_self searchResource).mono (fun _ => Nat.le_add_left _ _)
  exact (runsPoly_search id hw hn).cost
end CurrentKS.Realization

end OAI
