import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CentralSequences.CentralMatrix
import OAI.Analysis.JiangSu.CentralSequences.SigmaOrderZeroLift
import OAI.Analysis.JiangSu.MatrixAlgebras.MatrixDiagonalTrace
import OAI.Analysis.JiangSu.Nonunital.PropertySI

namespace OAI

section

noncomputable section
namespace NonunitalSI
open Pureness CurrentMain NonunitalGamma Filter Topology CompletelyPositiveOperations
open scoped ComplexOrder ENNReal CStarAlgebra

variable {A : Type} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [Nontrivial A] [Nonempty (NormalizedTrace A)] [CompactSpace (NormalizedTrace A)] [TopologicalSpace.SeparableSpace A]
variable (U : Ultrafilter ℕ) [Fact ((U : Filter ℕ) ≤ atTop)]
local notation "Fω" => CentralSequenceAlgebra (A := A) U
local notation "q" => centralSequenceToTracial (A := A) U
local notation "L" => familyLimitTrace (fun τ : NormalizedTrace A => NormalizedTrace.unitized τ) U

 theorem comparison_dimension_drop_relations
    (hnuc : NuclearUnitization.IsNuclear.{0,0} A) (hsimple : NonunitalGamma.TopologicallySimple A)
    (hstable : StablyProjectionless A)
    (hcone : AllDenselyFiniteTracesBounded A) (hcmp : NonunitalGamma.StrictComparison hcone)
    (n : ℕ) (hn : 0<n) :
    ∃ (φ : CStarMatrix (Fin n) (Fin n) ℂ →CP Fω) (s : Fω),
      (∀ M,‖φ M‖≤‖M‖) ∧ (∀ M P,φ M*φ P=φ (M*P)*φ 1) ∧
      ‖s‖≤1 ∧ star s*s=1-φ 1 ∧ φ (matrixUnit ⟨0,hn⟩ ⟨0,hn⟩)*s=s ∧ q (φ 1)=1 := by
  classical
  let p : Fin n := ⟨0,hn⟩
  let : Nonempty (Fin n) := ⟨p⟩
  obtain ⟨η,hη⟩ := NonunitalGamma.comparison_central_matrix U Fact.out hsimple hstable hcone hcmp hnuc n hn
  obtain ⟨φ,hφ,hφn,hφrel,_hφoz,hφ1⟩ := central_matrix_order_zero_lift U n hn η (fun M a => (hη M a).eq)
  let E : Fω := 1-φ 1
  let F : Fω := φ (matrixUnit p p)
  have h1p : 0≤φ 1 := map_nonneg φ zero_le_one
  have h1n : ‖φ 1‖≤1 := by simpa only [norm_one] using hφn 1
  have h1le : φ 1≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ h1p).mp h1n
  have hEp : 0≤E := sub_nonneg.mpr h1le
  have hEn : ‖E‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hEp).mpr (sub_le_self _ h1p)
  have hEq : q E=0 := by simp only [E,map_sub,map_one,hφ1,sub_self]
  have hFp : 0≤F := map_nonneg φ (matrixUnit_projection p).nonneg
  have hFn : ‖F‖≤1 := (hφn _).trans (matrixUnit_projection p).norm_le
  have hFq : IsStarProjection (q F) := by
    rw [show q F=η (matrixUnit p p) from hφ _]
    exact (matrixUnit_projection p).map η
  have htr (v : ℕ → NormalizedTrace A) : ((L v).functional (q F)).re=(n:ℝ)⁻¹ := by
    rw [show q F=η (matrixUnit p p) from hφ _,trace_matrix_corner η (L v) p,Fintype.card_fin]
    simp
  have hnr : 0<(n:ℝ) := by exact_mod_cast hn
  let t : ℝ := (n:ℝ)⁻¹/4
  have ht : 0<t := by dsimp [t]; positivity
  have hlarge (v : ℕ → NormalizedTrace A) : 2*t≤((L v).functional (q F)).re := by
    rw [htr]; dsimp [t]; nlinarith [inv_pos.mpr hnr]
  obtain ⟨s,hsn,hse,hsF⟩ := central_sequence_property_SI_projection_large U hnuc hsimple
    hstable.projectionless hcone hcmp E F hEp hEn hEq hFp hFn hFq ht hlarge
  exact ⟨φ,s,hφn,hφrel,hsn,hse,hsF,hφ1⟩

end NonunitalSI

end
end

end OAI
