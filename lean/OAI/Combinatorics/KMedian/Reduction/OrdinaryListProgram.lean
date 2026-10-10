import Mathlib
import OAI.Combinatorics.KMedian.Programs.BranchProgram
import OAI.Combinatorics.KMedian.Programs.FinalSelectionProgram
import OAI.Combinatorics.KMedian.Binary.InstanceParserProgram

namespace OAI


                                           
section
namespace MetricKMedian.Reduction.Program
open Finset Preparation Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row Table setView)
open InstanceProgram (Raw view)
variable (r : ℕ) (hr : 0<r) {η τ : ℝ} (p : RationalAllParameters η τ) (c a b : ℕ) (δ : ℚ)
def ordinarySet (I : Instance) : Finset (Fin I.n) :=
  if I.zeroTest then I.zeroOutput else selectList I (allList r hr p c a b δ I)
noncomputable def selectedProgram : PolyProgram InstanceProgram.encode (enc : Row → List Bool)
    (fun I => setView (selectList I (allList r hr p c a b δ I))) :=
  ((((identity enc).recode view (fun _ => rfl) (fun _ => rfl)).fanout (allListProgram r hr p c a b δ)).comp
    selectData_poly.program).congr _ (fun I => selectData_view I _)
noncomputable def ordinaryProgram : PolyProgram InstanceProgram.encode (enc : Row → List Bool)
    (fun I => setView (ordinarySet r hr p c a b δ I)) :=
  (PolyProgram.ite InstanceProgram.zeroTestProgram (selectedProgram r hr p c a b δ)
    InstanceProgram.zeroOutputProgram).congr _ (by
      intro I
      unfold ordinarySet
      by_cases h : I.zeroTest <;> simp [h])
def algorithm (I : Instance) : List Bool := setView (ordinarySet r hr p c a b δ I)
noncomputable def program : PolyProgram encodeInstance id (algorithm r hr p c a b δ) :=
  ((InputParser.instanceProgram.comp (ordinaryProgram r hr p c a b δ)).comp BooleanLists.unpackProgram).congr _ (fun _ => rfl)
 theorem ordinarySet_spec (α ξ : ℝ) (hc : 0<c) (hδ : 0<(δ:ℝ)) (hsmall : (δ:ℝ)≤1/6) (hξ : 0<ξ)
    (hfactor : 1+12*(δ:ℝ)≤α+ξ) (ha : (3/2:ℝ)≤a*((δ:ℝ)*ξ/(2*c))) (hb : 6*(α+ξ)*c/((δ:ℝ)*ξ)≤(b:ℝ))
    (hpseudo : ∀ I : Instance, I.computedPseudo r hr p c⊆I.facilities ∧ (I.computedPseudo r hr p c).Nonempty ∧
      (I.computedPseudo r hr p c).card≤I.k+c ∧ cost I (I.computedPseudo r hr p c)≤α*optimum I)
    (I : Instance) : ordinarySet r hr p c a b δ I⊆I.facilities ∧ (ordinarySet r hr p c a b δ I).Nonempty ∧
      (ordinarySet r hr p c a b δ I).card≤I.k ∧ cost I (ordinarySet r hr p c a b δ I)≤(α+ξ)*optimum I := by
  unfold ordinarySet
  split_ifs with hzero
  · obtain ⟨hsub,hne,hk,hcost⟩ := I.zeroOutput_spec hzero
    refine ⟨hsub,hne,hk,?_⟩
    rw [hcost,I.zeroTest_iff.mp hzero,mul_zero]
  · have hz : optimum I≠0 := fun he => hzero (I.zeroTest_iff.mpr he)
    obtain ⟨S,hS,hSF,hSne,hSk,hSc⟩ := reductionOutputs_success (fun J => J.computedPseudo r hr p c)
      α ξ δ c a b hc hδ hsmall hξ hfactor ha hb hpseudo I (lt_of_le_of_ne I.optimum_nonneg (Ne.symm hz))
    have hm : S∈allList r hr p c a b δ I := by apply List.mem_toFinset.mp; rwa [allList_toFinset]
    obtain ⟨hsub,hne,hk,hcost⟩ := selectList_spec I _ S hm hSF hSne hSk
    exact ⟨hsub,hne,hk,hcost.trans hSc⟩
end MetricKMedian.Reduction.Program
end

end OAI
