import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumEntryParity

namespace OAI

/-! Every real three-local Pauli word splits into one real factor and two
single-site factors of the same entry parity. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem qmaPauliRestrict_restrict (L S : Finset ι) (w : ι → Fin 4) (hL : L ⊆ S) :
    qmaPauliRestrict L (qmaPauliRestrict S w) = qmaPauliRestrict L w := by
  funext i
  by_cases hi : i ∈ L
  · simp [qmaPauliRestrict,hi,hL hi]
  · simp [qmaPauliRestrict,hi]

omit [DecidableEq ι] in
theorem qmaPauliYCount_zero (w : ι → Fin 4) (h : ∀ i, w i ≠ 2) : qmaPauliYCount w = 0 := by
  simp [qmaPauliYCount,h]

theorem qmaThreeSupport_split (w : ι → Fin 4) (hw : (qmaPauliSupport w).card ≤ 3)
    (he : Even (qmaPauliYCount w)) :
    ∃ P C : Finset ι, P.card ≤ 2 ∧ C.card ≤ 1 ∧ Disjoint P C ∧
      P ∪ C = qmaPauliSupport w ∧ ∀ i ∈ C, w i ≠ 2 := by
  let S := qmaPauliSupport w
  by_cases hS : S.card ≤ 2
  · exact ⟨S,∅,hS,by simp,by simp,by simp [S],by simp⟩
  · have hcard : S.card = 3 := by change S.card ≤ 3 at hw; omega
    have hreal : ∃ i ∈ S, w i ≠ 2 := by
      by_contra hn
      have hall : ∀ i ∈ S, w i = 2 := by simpa using hn
      have hf : Finset.univ.filter (fun i => w i = 2) = S := by
        ext i
        constructor
        · intro hi
          have hi2 := (Finset.mem_filter.mp hi).2
          simp [S,qmaPauliSupport,hi2]
        · intro hi
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hall i hi⟩
      have hc : qmaPauliYCount w = 3 := by rw [qmaPauliYCount,hf,hcard]
      rw [hc] at he
      norm_num at he
    obtain ⟨i,hi,hi2⟩ := hreal
    refine ⟨S \ {i},{i},?_,by simp,?_,?_,?_⟩
    · rw [Finset.card_sdiff_of_subset (by simpa using hi),Finset.card_singleton,hcard]
    · exact Finset.disjoint_left.mpr (fun j hj hc => (Finset.mem_sdiff.mp hj).2 hc)
    · exact Finset.sdiff_union_of_subset (by simpa using hi)
    · intro j hj
      simpa only [Finset.mem_singleton.mp hj] using hi2

theorem qmaPauliWord_triple_factor (w : ι → Fin 4) (hw : (qmaPauliSupport w).card ≤ 3)
    (he : Even (qmaPauliYCount w)) :
    ∃ a b c : ι → Fin 4,
      (qmaPauliSupport a).card ≤ 1 ∧ (qmaPauliSupport b).card ≤ 1 ∧ (qmaPauliSupport c).card ≤ 1 ∧
      qmaPauliWord a*qmaPauliWord b*qmaPauliWord c = qmaPauliWord w ∧
      qmaPauliWord a*qmaPauliWord b = qmaPauliWord b*qmaPauliWord a ∧
      qmaPauliWord a*qmaPauliWord c = qmaPauliWord c*qmaPauliWord a ∧
      qmaPauliWord b*qmaPauliWord c = qmaPauliWord c*qmaPauliWord b ∧
      decide (Odd (qmaPauliYCount a)) = decide (Odd (qmaPauliYCount b)) ∧
      Even (qmaPauliYCount c) := by
  obtain ⟨P,C,hP,hC,hPC,hcover,hnoY⟩ := qmaThreeSupport_split w hw he
  obtain ⟨L,T,hL,hT,hLT,hunion⟩ := qmaBalancedSupport P 1 (by omega)
  have hLP : L ⊆ P := by rw [← hunion]; exact Finset.subset_union_left
  have hTP : T ⊆ P := by rw [← hunion]; exact Finset.subset_union_right
  let a := qmaPauliRestrict L w
  let b := qmaPauliRestrict T w
  let c := qmaPauliRestrict C w
  let v := qmaPauliRestrict P w
  have hc : qmaPauliYCount c = 0 := by
    apply qmaPauliYCount_zero
    intro i
    by_cases hi : i ∈ C
    · simpa only [c,qmaPauliRestrict,hi,ite_true] using hnoY i hi
    · simp [c,qmaPauliRestrict,hi]
  have hvcover : qmaPauliSupport v ⊆ L ∪ T := by
    rw [hunion]
    exact qmaPauliRestrict_support P w
  have hv : Even (qmaPauliYCount v) := by
    have hs := qmaPauliYCount_split P C w hPC (by rw [hcover])
    change qmaPauliYCount v+qmaPauliYCount c = qmaPauliYCount w at hs
    rw [hc,add_zero] at hs
    rwa [hs]
  have hab : qmaPauliWord a*qmaPauliWord b = qmaPauliWord v := by
    have h := qmaPauliRestrict_factor L T v hLT hvcover
    simpa only [v,qmaPauliRestrict_restrict L P w hLP,qmaPauliRestrict_restrict T P w hTP] using h
  refine ⟨a,b,c,(Finset.card_le_card (qmaPauliRestrict_support L w)).trans hL,
    (Finset.card_le_card (qmaPauliRestrict_support T w)).trans hT,
    (Finset.card_le_card (qmaPauliRestrict_support C w)).trans hC,?_,
    qmaPauliRestrict_commute L T w hLT,
    qmaPauliRestrict_commute L C w (hPC.mono_left hLP),
    qmaPauliRestrict_commute T C w (hPC.mono_left hTP),?_,?_⟩
  · rw [hab]
    exact qmaPauliRestrict_factor P C w hPC (by rw [hcover])
  · have h := qmaPauliRestrict_same_parity L T v hLT hvcover hv
    simpa only [v,qmaPauliRestrict_restrict L P w hLP,qmaPauliRestrict_restrict T P w hTP] using h
  · rw [hc]
    norm_num

end ContinuumCoulomb

end

end OAI
