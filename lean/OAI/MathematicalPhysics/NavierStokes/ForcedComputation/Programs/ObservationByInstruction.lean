import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.IntermediateObservation

namespace OAI

namespace ShearFlows
open Set

theorem materialFlow_first_ge_of_mem {d : Input} (hd : ValidInput d)
    {Φ : ℝ → Space → Space} (hΦ : IsMaterialFlow d.period d.realizingVelocity Φ)
    {b : Instruction} (hb : b ∈ d.instructions) {x : Plane} (hx : x ∈ b.source.carrier)
    {a t : ℝ} (hs : a ≤ b.source.center 0) (htarget : a ≤ b.target.center 0)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    a - 2 * (d.h : ℝ) ≤ Φ t (atHeight x d.codingHeight) 0 := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hb
  let k : Fin d.instructions.length := ⟨i, hi⟩
  have hsource : d.sources k = b.source := by change d.instructions[i].source = b.source; rw [he]
  have htarget' : d.targets k = b.target := by change d.instructions[i].target = b.target; rw [he]
  apply materialFlow_first_ge hd hΦ k
  · rwa [hsource]
  · change a ≤ (d.sources k).center 0
    rwa [hsource]
  · change a ≤ (d.targets k).center 0
    rwa [htarget']
  · exact ht

theorem materialFlow_first_le_of_mem {d : Input} (hd : ValidInput d)
    {Φ : ℝ → Space → Space} (hΦ : IsMaterialFlow d.period d.realizingVelocity Φ)
    {b : Instruction} (hb : b ∈ d.instructions) {x : Plane} (hx : x ∈ b.source.carrier)
    {a t : ℝ} (hs : b.source.center 0 ≤ a) (htarget : b.target.center 0 ≤ a)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    Φ t (atHeight x d.codingHeight) 0 ≤ a + 2 * (d.h : ℝ) := by
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hb
  let k : Fin d.instructions.length := ⟨i, hi⟩
  have hsource : d.sources k = b.source := by change d.instructions[i].source = b.source; rw [he]
  have htarget' : d.targets k = b.target := by change d.instructions[i].target = b.target; rw [he]
  apply materialFlow_first_le hd hΦ k
  · rwa [hsource]
  · change (d.sources k).center 0 ≤ a
    rwa [hsource]
  · change (d.targets k).center 0 ≤ a
    rwa [htarget']
  · exact ht

end ShearFlows

end OAI
