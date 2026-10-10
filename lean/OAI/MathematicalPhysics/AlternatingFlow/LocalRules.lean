import OAI.MathematicalPhysics.AlternatingFlow.Detector
import OAI.MathematicalPhysics.AlternatingFlow.MachineProfiles

namespace OAI

open scoped BigOperators ENNReal NNReal Topology ContDiff
open MeasureTheory
namespace AlternatingNS
namespace LocalRule

noncomputable def readC (M : Machine) (N n : ℕ) (D : ℝ) : ℝ :=
  Profiles.decoder M.base ((M.base : ℝ) ^ Scales.s N n * D)
noncomputable def readB (M : Machine) (N n : ℕ) (D : ℝ) : ℝ :=
  Profiles.decoder M.base ((M.base : ℝ) ^ (Scales.s N n + 1 + Scales.K N n) * D)
noncomputable def readA (M : Machine) (N n : ℕ) (D : ℝ) : ℝ :=
  Profiles.decoder M.base ((M.base : ℝ) ^ (Scales.s N n + 1) * D) -
    ((M.base : ℝ) ^ Scales.K N n)⁻¹ * readB M N n D

noncomputable def updateLeft (b _a l : ℕ) (r : Rule) (A _B : ℝ) : ℝ :=
  letI := neZeroThree
  letI := twoAtLeastTwo
  if r.2.2 = 0 then (b : ℝ) * A - 2 * l
  else if r.2.2 = 1 then A else ((2 * r.2.1 : ℕ) + A) / b

noncomputable def updateRight (b a l : ℕ) (r : Rule) (_A B : ℝ) : ℝ :=
  letI := neZeroThree
  letI := twoAtLeastTwo
  let R := (b : ℝ) * B - 2 * a
  if r.2.2 = 0 then ((2 * l : ℕ) + ((2 * r.2.1 : ℕ) + R) / b) / b
  else if r.2.2 = 1 then ((2 * r.2.1 : ℕ) + R) / b else R

noncomputable def branchNumerator (b K a l : ℕ) (r : Rule) (A B : ℝ) : ℝ :=
  (2 * r.1 : ℕ) + updateLeft b a l r A B +
    ((b : ℝ) ^ K)⁻¹ * updateRight b a l r A B

noncomputable def branch (M : Machine) (N n q a : ℕ) (A B : ℝ) : ℝ :=
  letI := neZeroThree
  let r := M.command q a
  if r.2.2 = 0 then ∑ l ∈ Finset.range M.alphabet,
    Profiles.selector M.base l A * branchNumerator M.base (Scales.K N (n + 1)) a l r A B
  else branchNumerator M.base (Scales.K N (n + 1)) a 0 r A B

noncomputable def write (M : Machine) (N n : ℕ) (D : ℝ) : ℝ :=
  Scales.ε M.base N (n + 1) / M.base *
    ∑ q ∈ Finset.range (M.states + 1), ∑ a ∈ Finset.range M.alphabet,
      Profiles.selector M.base q (readC M N n D) *
        Profiles.selector M.base a (readB M N n D) *
          branch M N n q a (readA M N n D) (readB M N n D)

noncomputable def haltWeight (M : Machine) (N n : ℕ) (D : ℝ) : ℝ :=
  ∑ q ∈ Finset.range (M.states + 1),
    if q = M.states ∨ q ∈ M.haltingStates then Profiles.selector M.base q (readC M N n D) else 0

noncomputable def signal (M : Machine) (N n : ℕ) (D : ℝ) : ℝ :=
  letI := twoAtLeastTwo
  Scales.ε M.base N n - Scales.ε M.base N (n + 1) +
    2 * Scales.ε M.base N (n + 1) * haltWeight M N n D

lemma readC_smooth (M : Machine) (N n : ℕ) : ContDiff ℝ ∞ (readC M N n) := by
  exact (Profiles.decoder_smooth M.base (by have := M.base_ge_four; omega)).comp
    (contDiff_const.mul contDiff_id)

lemma readB_smooth (M : Machine) (N n : ℕ) : ContDiff ℝ ∞ (readB M N n) := by
  exact (Profiles.decoder_smooth M.base (by have := M.base_ge_four; omega)).comp
    (contDiff_const.mul contDiff_id)

lemma readA_smooth (M : Machine) (N n : ℕ) : ContDiff ℝ ∞ (readA M N n) := by
  exact ((Profiles.decoder_smooth M.base (by have := M.base_ge_four; omega)).comp
    (contDiff_const.mul contDiff_id)).sub (contDiff_const.mul (readB_smooth M N n))

lemma branchNumerator_smooth (b K a l : ℕ) (r : Rule) (A B : ℝ → ℝ)
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (fun D => branchNumerator b K a l r (A D) (B D)) := by
  unfold branchNumerator updateLeft updateRight
  split_ifs <;> fun_prop

lemma branch_smooth (M : Machine) (N n q a : ℕ) (A B : ℝ → ℝ)
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (fun D => branch M N n q a (A D) (B D)) := by
  unfold branch
  dsimp only
  split_ifs
  · apply ContDiff.sum
    intro l _
    exact ((Profiles.selector_smooth M.base l).comp hA).mul
      (branchNumerator_smooth _ _ _ _ _ _ _ hA hB)
  · exact branchNumerator_smooth _ _ _ _ _ _ _ hA hB

lemma write_smooth (M : Machine) (N n : ℕ) : ContDiff ℝ ∞ (write M N n) := by
  unfold write
  apply ContDiff.mul contDiff_const
  apply ContDiff.sum
  intro q _
  apply ContDiff.sum
  intro a _
  exact (((Profiles.selector_smooth M.base q).comp (readC_smooth M N n)).mul
    ((Profiles.selector_smooth M.base a).comp (readB_smooth M N n))).mul
    (branch_smooth M N n q a _ _ (readA_smooth M N n) (readB_smooth M N n))

lemma haltWeight_smooth (M : Machine) (N n : ℕ) : ContDiff ℝ ∞ (haltWeight M N n) := by
  unfold haltWeight
  apply ContDiff.sum
  intro q _
  split_ifs
  · exact (Profiles.selector_smooth M.base q).comp (readC_smooth M N n)
  · exact contDiff_const

lemma signal_smooth (M : Machine) (N n : ℕ) : ContDiff ℝ ∞ (signal M N n) := by
  exact contDiff_const.add (contDiff_const.mul (haltWeight_smooth M N n))

lemma readC_run (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w) (n : ℕ) :
    readC M w.length n (Encoding.donor M.base w.length (M.recordedBlock w) n) =
      M.recordedBlock w n := (M.read_run hM w hw n).1

lemma readB_run (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w) (n : ℕ) :
    readB M w.length n (Encoding.donor M.base w.length (M.recordedBlock w) n) =
      Machine.rightCode M.base w.length n (M.run w n) := (M.read_run hM w hw n).2.1

lemma readA_run (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w) (n : ℕ) :
    readA M w.length n (Encoding.donor M.base w.length (M.recordedBlock w) n) =
      Machine.leftCode M.base w.length n (M.run w n) := (M.read_run hM w hw n).2.2

end LocalRule
end AlternatingNS

namespace AlternatingNS
namespace LocalRule

lemma branchNumerator_execute (b N n : ℕ) (hb : 0 < b) (c : Machine.Configuration)
    (hc : Machine.Window N n c) (r : Rule) :
    branchNumerator b (Scales.K N (n + 1)) (c.tape c.head) (c.tape (c.head - 1)) r
      (Machine.leftCode b N n c) (Machine.rightCode b N n c) =
    (2 * r.1 : ℕ) + Machine.leftCode b N (n + 1) (Machine.execute c r) +
      ((b : ℝ) ^ Scales.K N (n + 1))⁻¹ * Machine.rightCode b N (n + 1) (Machine.execute c r) := by
  by_cases h₀ : r.2.2 = 0
  · obtain ⟨hL, hR⟩ := Machine.code_execute_left b N n hb c hc r h₀
    rw [hL, hR]
    simp [branchNumerator, updateLeft, updateRight, h₀, Machine.leftDigits, Machine.rightDigits]
  · by_cases h₁ : r.2.2 = 1
    · obtain ⟨hL, hR⟩ := Machine.code_execute_stay b N n hb c hc r h₁
      rw [hL, hR]
      simp [branchNumerator, updateLeft, updateRight, h₁, Machine.rightDigits]
    · have h₂ : r.2.2 = 2 := by omega
      obtain ⟨hL, hR⟩ := Machine.code_execute_right b N n hb c hc r h₂
      rw [hL, hR]
      simp [branchNumerator, updateLeft, updateRight, h₀, h₁, Machine.rightDigits]

lemma branch_on_configuration (M : Machine) (N n : ℕ) (c : Machine.Configuration)
    (ha : M.Admissible c) (hw : Machine.Window N n c) :
    branch M N n c.state (c.tape c.head)
      (Machine.leftCode M.base N n c) (Machine.rightCode M.base N n c) =
    (2 * (M.step c).state : ℕ) + Machine.leftCode M.base N (n + 1) (M.step c) +
      ((M.base : ℝ) ^ Scales.K N (n + 1))⁻¹ * Machine.rightCode M.base N (n + 1) (M.step c) := by
  have hb : 0 < M.base := by have := M.base_ge_four; omega
  have hnum := branchNumerator_execute M.base N n hb c hw (M.command c.state (c.tape c.head))
  rw [Machine.step_execute]
  unfold branch
  dsimp only
  split_ifs with h₀
  · rw [Finset.sum_eq_single_of_mem (c.tape (c.head - 1)) (Finset.mem_range.2 (ha.2 _))]
    · rw [Machine.selector_leftCode M c ha N n, ite_eq_left rfl, one_mul]
      exact hnum
    · intro l _ hl
      simp [Machine.selector_leftCode M c ha N n l, hl]
  · simpa only [branchNumerator, updateLeft, updateRight, h₀, ite_false, Machine.execute] using hnum

lemma write_run (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w) (n : ℕ) :
    write M w.length n (Encoding.donor M.base w.length (M.recordedBlock w) n) =
      Scales.ε M.base w.length (n + 1) * M.recordedBlock w (n + 1) := by
  have hc := M.run_admissible hM w hw n
  have hq : (M.run w n).state ∈ Finset.range (M.states + 1) :=
    Finset.mem_range.2 (Nat.lt_succ_of_le hc.1)
  have ha : (M.run w n).tape (M.run w n).head ∈ Finset.range M.alphabet :=
    Finset.mem_range.2 (hc.2 _)
  unfold write
  rw [readC_run M hM w hw n, readB_run M hM w hw n, readA_run M hM w hw n]
  simp only [Machine.selector_recordedBlock M hM w hw n,
    Machine.selector_rightCode M (M.run w n) hc w.length n,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', ite_eq_left hq, ite_eq_left ha]
  rw [branch_on_configuration M w.length n (M.run w n) hc (M.run_window w n)]
  rw [Machine.recordedBlock_formula, Machine.run_succ]
  ring

lemma haltWeight_run (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w) (n : ℕ) :
    haltWeight M w.length n (Encoding.donor M.base w.length (M.recordedBlock w) n) =
      if M.isHalting (M.run w n) then 1 else 0 := by
  have hc := (M.run_admissible hM w hw n).1
  unfold haltWeight
  rw [readC_run M hM w hw n,
    Finset.sum_eq_single_of_mem (M.run w n).state (Finset.mem_range.2 (by omega))]
  · simp [Machine.selector_recordedBlock M hM w hw n, Machine.isHalting]
  · intro q _ hq
    simp [Machine.selector_recordedBlock M hM w hw n q, hq]

lemma signal_run (M : Machine) (hM : M.WellFormed) (w : List ℕ) (hw : M.ValidInput w) (n : ℕ) :
    signal M w.length n (Encoding.donor M.base w.length (M.recordedBlock w) n) =
      Detector.increment M.base w.length (fun j => M.isHalting (M.run w j)) n := by
  rw [signal, haltWeight_run M hM w hw n]
  simp only [Detector.increment, mul_ite, mul_one, mul_zero]

end LocalRule
end AlternatingNS

end OAI
