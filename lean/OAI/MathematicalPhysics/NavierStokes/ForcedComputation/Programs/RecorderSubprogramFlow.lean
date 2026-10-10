import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.RecorderObservation

namespace OAI

/-! Recorder transitions inside a larger geometric program. This version
allows the fresh-state loader and the used recorder rows to share one period. -/

noncomputable section
namespace ForcedComputation.Recorder
open ShearFlows Radix Set

theorem Step.flow_one_in {M : Alternating.Machine} {hM : M.WellFormed}
    {C D : Configuration (State M) (Alphabet M)}
    (h : Step (finiteMachine M hM) C D) {d : Input} (hd : ValidInput d)
    (hm : ∀ b : Branch (finiteMachine M hM), b.source = C.control →
      b.read = C.tape C.head → b.left = C.tape (C.head - 1) →
      geometricInstruction M hM b ∈ d.instructions)
    {Φ : ℝ → Space → Space} (hΦ : IsMaterialFlow d.period d.realizingVelocity Φ) :
    Φ 1 (atHeight (codedPoint M C) d.codingHeight) =
      atHeight (codedPoint M D) d.codingHeight := by
  obtain ⟨q, a, k, hl, rfl⟩ := h
  let b : Branch (finiteMachine M hM) :=
    ⟨C.control, C.tape C.head, q, a, k, C.tape (C.head - 1), hl⟩
  have hb := hm b rfl rfl rfl
  have hB := radixBase_gt_one M
  have hdigits : ∀ a, 0 ≤ radixDigit M a ∧ radixDigit M a ≤ radixBase M - 1 := by
    intro a
    exact ⟨(radixDigit_bounds_rat M a).1, by linarith [(radixDigit_bounds_rat M a).2]⟩
  have hc : codedPoint M C ∈ (geometricInstruction M hM b).source.carrier :=
    branchInstruction_contains hB hdigits (bandScale_pos M).le (stateOffset M) b C rfl rfl rfl
  have he := realizingVelocity_periodMap hd hΦ hb
    (sourceTube_contains (geometricInstruction M hM b) d.codingHeight
      (by exact_mod_cast tubeRadius_pos hd)
      (Set.mem_image_of_mem (fun X => atHeight X d.codingHeight) hc))
  simp only [atHeight_horizontal] at he
  change Φ 1 (atHeight (codedPoint M C) d.codingHeight) =
    atHeight ((geometricInstruction M hM b).affine (codedPoint M C)) d.codingHeight at he
  have ha : (geometricInstruction M hM b).affine (codedPoint M C) =
      codedPoint M ⟨q, C.head + k, Function.update C.tape C.head a⟩ :=
    branchInstruction_step hB hdigits (bandScale M) (stateOffset M) b C rfl rfl rfl
  simpa only [ha] using he

theorem Step.flow_safe_in {M : Alternating.Machine} {hM : M.WellFormed}
    {C D : Configuration (State M) (Alphabet M)}
    (h : Step (finiteMachine M hM) C D)
    (hc : recorderHalting M C.control = false) (ht : recorderHalting M D.control = false)
    {d : Input} (hd : ValidInput d) (hsmall : (d.h : ℝ) ≤ (bandScale M : ℝ) / 2)
    (hm : ∀ b : Branch (finiteMachine M hM), b.source = C.control →
      b.read = C.tape C.head → b.left = C.tape (C.head - 1) →
      geometricInstruction M hM b ∈ d.instructions)
    {Φ : ℝ → Space → Space} (hΦ : IsMaterialFlow d.period d.realizingVelocity Φ)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    0 < Φ s (atHeight (codedPoint M C) d.codingHeight) 0 ∧
      Φ s (atHeight (codedPoint M C) d.codingHeight) 0 < 1 / 2 := by
  obtain ⟨q, a, k, hl, rfl⟩ := h
  let b : Branch (finiteMachine M hM) :=
    ⟨C.control, C.tape C.head, q, a, k, C.tape (C.head - 1), hl⟩
  have hb := hm b rfl rfl rfl
  have hdigits : ∀ a, 0 ≤ radixDigit M a ∧ radixDigit M a ≤ radixBase M - 1 := by
    intro a
    exact ⟨(radixDigit_bounds_rat M a).1, by linarith [(radixDigit_bounds_rat M a).2]⟩
  have hx : codedPoint M C ∈ (geometricInstruction M hM b).source.carrier :=
    branchInstruction_contains (radixBase_gt_one M) hdigits (bandScale_pos M).le
      (stateOffset M) b C rfl rfl rfl
  have hsource := stateBox_nonterminal_x M b.source hc (geometricInstruction_source_unit M hM b)
    (center_mem (geometricInstruction_source_positive M hM b))
  have htarget := stateBox_nonterminal_x M b.target ht (geometricInstruction_target_unit M hM b)
    (center_mem (geometricInstruction_target_positive M hM b))
  have hlo := materialFlow_first_ge_of_mem hd hΦ hb hx hsource.1 htarget.1 hs
  have hhi := materialFlow_first_le_of_mem hd hΦ hb hx hsource.2 htarget.2 hs
  have hk : (bandScale M : ℝ) ≤ 1 / 64 := by
    have he := (Rat.cast_le (K := ℝ)).mpr (bandScale_le M)
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using he
  constructor <;> linarith

theorem Steps.flow_nat_in {M : Alternating.Machine} {hM : M.WellFormed}
    {C D : Configuration (State M) (Alphabet M)} {n : ℕ}
    (h : Steps (finiteMachine M hM) n C D) {d : Input} (hd : ValidInput d)
    (hm : ∀ m E, Steps (finiteMachine M hM) m C E →
      ∀ b : Branch (finiteMachine M hM), b.source = E.control →
      b.read = E.tape E.head → b.left = E.tape (E.head - 1) →
      geometricInstruction M hM b ∈ d.instructions)
    {Φ : ℝ → Space → Space} (hΦ : IsMaterialFlow d.period d.realizingVelocity Φ) :
    Φ n (atHeight (codedPoint M C) d.codingHeight) =
      atHeight (codedPoint M D) d.codingHeight := by
  induction h with
  | zero C => simpa only [Nat.cast_zero] using hΦ.initial (atHeight (codedPoint M C) d.codingHeight)
  | @next n C D E hc hs ih =>
    rw [Nat.cast_add, Nat.cast_one, add_comm,
      hΦ.nat_shift (realizingVelocity_time_periodic _) n 1, ih hm]
    exact hs.flow_one_in hd (hm n D hc) hΦ

end ForcedComputation.Recorder

end

end OAI
