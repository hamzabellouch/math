import OAI.Analysis.CircleDomains.Modulus.RecursiveTestBudget
import OAI.Analysis.CircleDomains.Topology.SavedSeparatingFamily

namespace OAI

/-! Iterate the constructed finite appending theorem, choosing each error
below every saved tolerance in the finite history. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

structure SavedAppendingStep {G : Set Sphere} (a : ℝ) (T : FiniteCompactTests G) (δ η : ℝ) where
  data : AppendingPairData G T.test T.witness a δ η
  saved : SavedSeparatingFamily G a η data.p data.q data.p_witness data.q_witness

structure AppendingConstructionState (G : Set Sphere) where
  family : FiniteCompactTests G
  tolerances : List ℝ
  positive : ∀ t ∈ tolerances, 0 < t

namespace AppendingConstructionState
variable {G : Set Sphere} {a ε : ℝ}

 def chooseStep (hsupply : FiniteAppendingSupply G a)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
    (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
    (s : AppendingConstructionState G) (n : ℕ) :
    SavedAppendingStep a s.family (recursiveTestBudget ε n s.tolerances) (1/((n:ℝ)+1)) := by
  let D := Classical.choice (hsupply s.family (recursiveTestBudget ε n s.tolerances)
    (1/((n:ℝ)+1)) (recursiveTestBudget_pos hε n s.positive) (by positivity))
  exact ⟨D,Classical.choice (D.exists_saved_family hsard hsch hG hinf hTD ha hBa)⟩

 def next (hsupply : FiniteAppendingSupply G a)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
    (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
    (s : AppendingConstructionState G) (n : ℕ) : AppendingConstructionState G :=
  let step := s.chooseStep hsupply hsard hsch hG hinf hTD ha hBa hε n
  { family := step.data.toTestFamily
    tolerances := step.saved.tolerance :: s.tolerances
    positive := fun t ht => by
      rcases List.mem_cons.mp ht with rfl | ht
      · exact step.saved.tolerance_pos
      · exact s.positive t ht }

end AppendingConstructionState

 def appendingStates {G : Set Sphere} {a ε : ℝ}
    (hsupply : FiniteAppendingSupply G a)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
    (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
    (T : FiniteCompactTests G) : ℕ → AppendingConstructionState G
  | 0 => ⟨T,[],fun _ ht => by simp at ht⟩
  | n+1 => (appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T n).next
      hsupply hsard hsch hG hinf hTD ha hBa hε n

 theorem appendingStates_history_length {G : Set Sphere} {a ε : ℝ}
    (hsupply : FiniteAppendingSupply G a)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
    (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
    (T : FiniteCompactTests G) (n : ℕ) :
    (appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T n).tolerances.length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [appendingStates, AppendingConstructionState.next, List.length_cons] using congrArg Nat.succ ih

 theorem appendingStates_family_count {G : Set Sphere} {a ε : ℝ}
    (hsupply : FiniteAppendingSupply G a)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
    (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
    (T : FiniteCompactTests G) (n : ℕ) :
    (appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T n).family.count = T.count+2*n := by
  induction n with
  | zero => simp only [appendingStates, Nat.mul_zero, Nat.add_zero]
  | succ n ih =>
    change (appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T n).family.count+2 = _
    rw [ih]
    omega

end CircleDomainRigidity

end

end OAI
