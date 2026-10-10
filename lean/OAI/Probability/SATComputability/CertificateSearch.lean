import OAI.MathematicalPhysics.RapidForcing.RatOperations
import Mathlib.Computability.PartrecCode

namespace OAI

namespace FixedClauseThreshold.Computability

open Filter
open scoped Topology
open RapidForcing.EffectiveArithmetic

def tolerance (r : ℕ) : ℚ := (2 ^ r : ℚ)⁻¹

@[fun_prop]
theorem tolerance_computable : Computable tolerance := by
  unfold tolerance
  fun_prop

theorem tolerance_pos (r : ℕ) : 0 < tolerance r := by
  unfold tolerance
  positivity

def certificateTest (lower upper : ℕ → ℚ) (valid : ℕ → Bool)
    (r n : ℕ) : Option ℚ :=
  let i := n.unpair.1
  let j := n.unpair.2
  if valid j = true ∧ upper j - lower i ≤ 2 * tolerance r then
    some ((lower i + upper j) / 2)
  else none

theorem certificateTest_computable {lower upper : ℕ → ℚ} {valid : ℕ → Bool}
    (hl : Computable lower) (hu : Computable upper) (hv : Computable valid) :
    Computable₂ (certificateTest lower upper valid) := by
  unfold Computable₂ certificateTest
  fun_prop

def certificateProgram (lower upper : ℕ → ℚ) (valid : ℕ → Bool)
    (r : ℕ) : Part ℚ :=
  Nat.rfindOpt (certificateTest lower upper valid r)

theorem certificateProgram_partrec {lower upper : ℕ → ℚ} {valid : ℕ → Bool}
    (hl : Computable lower) (hu : Computable upper) (hv : Computable valid) :
    Partrec (certificateProgram lower upper valid) :=
  Partrec.rfindOpt (certificateTest_computable hl hu hv)

theorem certificateTest_sound {α : ℝ} {lower upper : ℕ → ℚ} {valid : ℕ → Bool}
    (hl : ∀ i, (lower i : ℝ) ≤ α)
    (hu : ∀ j, valid j = true → α ≤ (upper j : ℝ))
    {r n : ℕ} {q : ℚ} (hq : q ∈ certificateTest lower upper valid r n) :
    |(q : ℝ) - α| ≤ (tolerance r : ℝ) := by
  dsimp only [certificateTest] at hq
  split_ifs at hq with h
  · obtain rfl := Option.mem_some_iff.mp hq
    have hlo := hl n.unpair.1
    have hup := hu n.unpair.2 h.1
    have hwidth : (upper n.unpair.2 : ℝ) - lower n.unpair.1 ≤
        2 * (tolerance r : ℝ) := by exact_mod_cast h.2
    push_cast
    apply abs_le.mpr
    constructor <;> linarith
  · contradiction

theorem certificateProgram_total {α : ℝ} {lower upper : ℕ → ℚ} {valid : ℕ → Bool}
    (hl : ∀ ε : ℝ, 0 < ε → ∃ i, α - ε < (lower i : ℝ))
    (hu : ∀ ε : ℝ, 0 < ε → ∃ j, valid j = true ∧ (upper j : ℝ) < α + ε)
    (r : ℕ) : (certificateProgram lower upper valid r).Dom := by
  have hε : (0 : ℝ) < tolerance r := by exact_mod_cast tolerance_pos r
  obtain ⟨i, hi⟩ := hl (tolerance r) hε
  obtain ⟨j, hj, hj'⟩ := hu (tolerance r) hε
  apply Nat.rfindOpt_dom.mpr
  refine ⟨Nat.pair i j, (lower i + upper j) / 2, ?_⟩
  have hwidth : upper j - lower i ≤ 2 * tolerance r := by
    have : (upper j : ℝ) - lower i ≤ 2 * (tolerance r : ℝ) := by linarith
    exact_mod_cast this
  simp [certificateTest, hj, hwidth]

theorem finite_certificate_search {α : ℝ}
    {lower upper : ℕ → ℚ} {valid : ℕ → Bool}
    (hlc : Computable lower) (huc : Computable upper) (hvc : Computable valid)
    (hls : ∀ i, (lower i : ℝ) ≤ α)
    (hus : ∀ j, valid j = true → α ≤ (upper j : ℝ))
    (hld : ∀ ε : ℝ, 0 < ε → ∃ i, α - ε < (lower i : ℝ))
    (hud : ∀ ε : ℝ, 0 < ε → ∃ j, valid j = true ∧ (upper j : ℝ) < α + ε) :
    ∃ q : ℕ → ℚ, Computable q ∧
      (∀ r, q r ∈ certificateProgram lower upper valid r) ∧
      ∀ r, |(q r : ℝ) - α| ≤ (2 ^ r : ℝ)⁻¹ := by
  let total := certificateProgram_total hld hud
  let q := fun r => (certificateProgram lower upper valid r).get (total r)
  have hq (r : ℕ) : q r ∈ certificateProgram lower upper valid r := Part.get_mem _
  refine ⟨q, (certificateProgram_partrec hlc huc hvc).of_eq_tot hq, hq, ?_⟩
  intro r
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec (hq r)
  simpa only [tolerance, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat] using
    certificateTest_sound hls hus hn

theorem rational_sequence_code {q : ℕ → ℚ} (hq : Computable q) :
    ∃ c : Nat.Partrec.Code, ∀ r,
      Nat.Partrec.Code.eval c r = Part.some (Encodable.encode (q r)) := by
  have hencode := Computable.encode.comp hq
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hencode)
  exact ⟨c, fun r => congrFun hc r⟩

end FixedClauseThreshold.Computability

end OAI
