import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.MatrixAlgebras.MatrixProjectionTests
import OAI.Analysis.JiangSu.MatrixAlgebras.TracialMatrixCorners

namespace OAI

section

noncomputable section
namespace DirectComparison
open Pureness CurrentMain DirectPacking Filter
open scoped ComplexOrder

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (TracialState A)] (U : Ultrafilter ℕ)
local notation "T" => (fun τ : TracialState A => τ)
local notation "D" => FamilyUltrapower T U
local notation "L" => familyLimitTrace T U
local notation "ι" => familyUltrapowerMap T U

 theorem comparison_finite_matrix_models (hfree : (U : Filter ℕ)≤atTop)
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hcmp : StrictComparison A) (hnuc : IsNuclear A)
    (m : ℕ) (hm : 0 < m) (K : Finset (unitary A)) {ε : ℝ} (hε : 0<ε) :
    Nonempty (TracialMatrixModel L ι m K ε) := by
  let := limitTraceFamily (A := A) U
  let := limitTraceFamily_nonempty (A := A) U
  obtain ⟨hs,hc,hi⟩ := source_tools U hfree hsimple hinf hcmp
  obtain ⟨M⟩ := matrix_models_from_packing hnuc ι hs hc hi hm
    (fun e he => tracial_matrix_corner U hfree hsimple hinf hcmp hnuc m hm he) K hε
  have h2 (a : D) : familyTwoNorm L a≤familyTwoNorm (fun τ : RestrictedTracialState D => (τ : TracialState D)) a := by
    apply ciSup_le
    intro s
    exact traceTwoNorm_le_family (fun τ : RestrictedTracialState D => (τ : TracialState D)) ⟨L s,⟨s,rfl⟩⟩ a
  exact ⟨{
    entry := M.entry
    norm_entry := M.norm_entry
    star_error := fun i j => (h2 _).trans_lt (M.star_error i j)
    mul_error := fun i j k l => (h2 _).trans_lt (M.mul_error i j k l)
    unit_error := (h2 _).trans_lt M.unit_error
    comm_error := fun i j u hu => (h2 _).trans_lt (M.comm_error i j u hu)}⟩

end DirectComparison

end
end

end OAI
