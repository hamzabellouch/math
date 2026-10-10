import OAI.MathematicalPhysics.NavierStokes.Material.MachineEncoding
import OAI.MathematicalPhysics.NavierStokes.Material.Selectors

namespace OAI

namespace Alternating.Memory
open scoped BigOperators

theorem selector_sum {b d k : ℕ} {x : ℝ} (hd : d < k)
    (hx : (b : ℝ) * x ∈ Set.Icc (2 * (d : ℝ)) (2 * d + 1)) (v : ℕ → ℝ) :
    ∑ e ∈ Finset.range k, digitSelector b e x * v e = v d := by
  simp_rw [digitSelector_selects hx, ite_mul, one_mul, zero_mul]
  simp [hd]

theorem Block.code_state_cylinder {b K d : ℕ} (hb : 2 ≤ b) (c : Block b K)
    (hd : c.stateDigit = 2 * d) :
    (b : ℝ) * c.code ∈ Set.Icc (2 * (d : ℝ)) (2 * d + 1) := by
  have hb0 : (b : ℝ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  have htail := c.tail_mem hb
  have hm1 := tailBound_lt_one hb
  rw [c.code_formula (by omega)]
  have he : (b : ℝ) *
      (((c.stateDigit : ℝ) + c.leftCode + (b : ℝ)⁻¹ ^ K * c.rightCode) / b) =
      (c.stateDigit : ℝ) + (c.leftCode + (b : ℝ)⁻¹ ^ K * c.rightCode) := by
    field_simp
    ring
  rw [he, hd]
  push_cast
  exact ⟨by linarith [htail.1], by linarith [htail.2]⟩

noncomputable def readState (b N n : ℕ) (D : ℝ) : ℝ :=
  safeDecoder b ((b : ℝ) ^ scale N n * D)

noncomputable def readRight (b N n : ℕ) (D : ℝ) : ℝ :=
  safeDecoder b ((b : ℝ) ^ (scale N n + 1 + width N n) * D)

noncomputable def readLeft (b N n : ℕ) (D : ℝ) : ℝ :=
  safeDecoder b ((b : ℝ) ^ (scale N n + 1) * D) -
    (b : ℝ)⁻¹ ^ width N n * readRight b N n D

theorem readState_smooth {b : ℕ} (hb : 2 ≤ b) (N n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (readState b N n) :=
  (safeDecoder_smooth hb).comp (contDiff_const.mul contDiff_id)

theorem readRight_smooth {b : ℕ} (hb : 2 ≤ b) (N n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (readRight b N n) :=
  (safeDecoder_smooth hb).comp (contDiff_const.mul contDiff_id)

theorem readLeft_smooth {b : ℕ} (hb : 2 ≤ b) (N n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (readLeft b N n) := by
  exact ((safeDecoder_smooth hb).comp (contDiff_const.mul contDiff_id)).sub
    (contDiff_const.mul (readRight_smooth hb N n))

noncomputable def haltingSelector (M : Machine) (C : ℝ) : ℝ :=
  ∑ q ∈ Finset.range (M.stateCount + 1),
    digitSelector (alphabetBase M) q C * (if M.isHalting q then 1 else 0)

theorem haltingSelector_smooth (M : Machine) :
    ContDiff ℝ (⊤ : ℕ∞) (haltingSelector M) := by
  unfold haltingSelector
  apply ContDiff.sum
  intro q _
  exact (digitSelector_smooth _ _).mul contDiff_const

theorem haltingSelector_exact {M : Machine} {q : ℕ} (hq : q ≤ M.stateCount)
    {C : ℝ} (hC : (alphabetBase M : ℝ) * C ∈ Set.Icc (2 * (q : ℝ)) (2 * q + 1)) :
    haltingSelector M C = if M.isHalting q then 1 else 0 :=
  selector_sum (by omega) hC _

noncomputable def localSignal (M : Machine) (N n : ℕ) (D : ℝ) : ℝ :=
  epsilon (alphabetBase M) N n - epsilon (alphabetBase M) N (n + 1) +
    2 * epsilon (alphabetBase M) N (n + 1) *
      haltingSelector M (readState (alphabetBase M) N n D)

theorem localSignal_smooth (M : Machine) (N n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (localSignal M N n) := by
  apply contDiff_const.add
  apply contDiff_const.mul
  exact (haltingSelector_smooth M).comp
    (readState_smooth (by have := alphabetBase_ge_four M; omega) N n)

theorem localSignal_exact (I : MachineInput) (hI : ValidInput I) (n : ℕ) :
    localSignal I.1 I.2.length n
      (donor (alphabetBase I.1) I.2.length (actualBlock I hI) n) =
    signalIncrement (alphabetBase I.1) I.2.length
      (fun j => I.1.isHalting (configurationAt I j).state) n := by
  have hb : 2 ≤ alphabetBase I.1 := by have := alphabetBase_ge_four I.1; omega
  have hr := (actualBlock_read I hI n).1
  change readState (alphabetBase I.1) I.2.length n
    (donor (alphabetBase I.1) I.2.length (actualBlock I hI) n) = (actualBlock I hI n).code at hr
  have hq := (configurationAt_valid hI n).1
  have hc := (actualBlock I hI n).code_state_cylinder hb rfl
  unfold localSignal signalIncrement
  rw [hr, haltingSelector_exact hq hc]
  split_ifs <;> ring

end Alternating.Memory

end OAI
