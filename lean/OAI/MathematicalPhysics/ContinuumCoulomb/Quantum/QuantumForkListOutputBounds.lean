import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListInitialWeights

namespace OAI

/-! A single explicit coefficient envelope for every edge in the actual
output, including the retained active-star edges, and for its scalar offset. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open MediatorListProgram

theorem CoefficientBound.full (s : State) {L : ℝ} (h : CoefficientBound s L)
    (b : Bond) (hb : b ∈ s.2.1++activeBonds s.2.2.2) : |(b.2.2:ℝ)| ≤ L := by
  rcases List.mem_append.mp hb with hold | hnew
  · exact h.ordinary b hold
  obtain ⟨bs,hbs,hb⟩ := List.mem_flatten.mp hnew
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hbs
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hb
  exact h.active _ (groupAt_mem _ _ (List.mem_range.mp hi)) _ hp

def outputCoefficient (m D : ℕ) (L T : ℝ) : ℝ :=
  let M : ℝ := ((8*D+3)*m:ℕ)
  coefficientEnvelope M (forkCoefficient M L T) T D

theorem initial_iterate_coefficientBound (n : ℕ) (bs : List Bond)
    (hb : SourceBondLists.bounded n bs) (c N : ℚ) (hN : 0 ≤ N)
    {L T : ℝ} (hL : 1 ≤ L) (hT : |(N:ℝ)| ≤ T)
    (hc : |(c:ℝ)| ≤ L) (hw : ∀ b ∈ bs, |(b.2.2:ℝ)| ≤ L) (D : ℕ) :
    CoefficientBound (iterate N D (initial n bs c N)) (outputCoefficient bs.length D L T) := by
  let M : ℝ := ((8*D+3)*bs.length:ℕ)
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  have hm : (bs.length:ℝ) ≤ M := by
    have hn : bs.length ≤ (8*D+3)*bs.length := by
      simpa only [one_mul] using
        (Nat.mul_le_mul_right bs.length (by omega : 1 ≤ 8*D+3))
    dsimp only [M]
    exact_mod_cast hn
  have hi := initial_coefficientBound n bs c N hN hm hL hT hc hw
  have hv := initial_background_valid n bs c N
  have hmass : ((((initial n bs c N).2.1.length+
      (4*D+1)*portMass (initial n bs c N).2.2.2):ℕ):ℝ) ≤ M := by
    rw [initial_portMass n bs hb c N]
    have hlen : (initial n bs c N).2.1.length=bs.length := by
      simp only [initial,List.length_map,List.length_range]
    rw [hlen]
    dsimp only [M]
    exact_mod_cast (show bs.length+(4*D+1)*(2*bs.length) ≤ (8*D+3)*bs.length from
      le_of_eq (by ring))
  exact iterate_coefficientBound _ (initial_validPorts n bs c N) hv.1 hv.2 N hN
    (forkCoefficient_one_le hM0 hL) hT hi D hmass

theorem initial_iterate_full_weight (n : ℕ) (bs : List Bond)
    (hb : SourceBondLists.bounded n bs) (c N : ℚ) (hN : 0 ≤ N)
    {L T : ℝ} (hL : 1 ≤ L) (hT : |(N:ℝ)| ≤ T)
    (hc : |(c:ℝ)| ≤ L) (hw : ∀ b ∈ bs, |(b.2.2:ℝ)| ≤ L) (D : ℕ)
    (b : Bond) (hmem : b ∈ (iterate N D (initial n bs c N)).2.1++
      activeBonds (iterate N D (initial n bs c N)).2.2.2) :
    |(b.2.2:ℝ)| ≤ outputCoefficient bs.length D L T :=
  (initial_iterate_coefficientBound n bs hb c N hN hL hT hc hw D).full _ b hmem

end ContinuumCoulomb.QuantumForkList

end

end OAI
