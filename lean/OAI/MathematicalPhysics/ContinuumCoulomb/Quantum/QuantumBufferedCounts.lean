import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedCongestion

namespace OAI

/-! The assembled simple paths have linearly many candidate crossing points. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical
namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

def bufferedSites (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) : Finset (ℕ × ℕ) :=
  (M.bufferedPath hd e).val.support.toFinset

def bufferedAllSites (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) : Finset (ℕ × ℕ) :=
  Finset.univ.biUnion (M.bufferedSites hd)

theorem bufferedSites_card (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    (M.bufferedSites hd e).card ≤ 2*(16*(9*B+6)+2)+8*(9*B+9)*(3*A+2)+1 := by
  unfold bufferedSites
  rw [List.toFinset_card_of_nodup (M.bufferedPath hd e).nodup_support,
    SimpleGraph.Walk.length_support]
  exact Nat.add_le_add_right (M.bufferedPath_length hd e) 1

theorem bufferedAllSites_card (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) :
    (M.bufferedAllSites hd).card ≤
      Fintype.card M.Term * (2*(16*(9*B+6)+2)+8*(9*B+9)*(3*A+2)+1) := by
  calc
    _ ≤ ∑ e : M.Term, (M.bufferedSites hd e).card := Finset.card_biUnion_le
    _ ≤ ∑ _e : M.Term, (2*(16*(9*B+6)+2)+8*(9*B+9)*(3*A+2)+1) :=
      Finset.sum_le_sum (fun e _ => M.bufferedSites_card hd e)
    _ = _ := by simp

theorem bufferedSites_third_eq (hA : 0 < A) (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    {e f g : M.Term} (hef : e ≠ f) {z : ℕ × ℕ} (hv : ∀ v, z ≠ M.placedVertex v)
    (he : z ∈ M.bufferedSites hd e) (hf : z ∈ M.bufferedSites hd f)
    (hg : z ∈ M.bufferedSites hd g) : g = e ∨ g = f := by
  exact M.bufferedPath_third_eq hA hd hef hv
    (List.mem_toFinset.mp he) (List.mem_toFinset.mp hf) (List.mem_toFinset.mp hg)

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
