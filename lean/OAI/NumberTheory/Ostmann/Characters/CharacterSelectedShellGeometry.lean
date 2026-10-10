import OAI.NumberTheory.Ostmann.Characters.CharacterBandGeometry
import OAI.NumberTheory.Ostmann.Characters.CharacterConstructedRanges
import OAI.NumberTheory.Ostmann.Characters.CharacterRoundedEndpoint

namespace OAI

/-! # The chosen small shell and upper rich shell satisfy the actual cutoffs -/
namespace Ostmann
open Filter

@[simp] theorem characterBandPoint_succ (α β : ℝ) (q i : ℕ) :
    characterBandPoint α β q (i + 1) = characterBandPoint α β q i + (β - α) / q := by
  unfold characterBandPoint
  push_cast
  ring

theorem eventual_character_selected_shell_geometry (α β z : ℝ) (hα : 0 < α)
    (hαβ : α < β) (hz : 0 ≤ z) (q n : ℕ) (hq : 0 < q) (hn : 20000 ≤ n)
    (i j k : Fin q) (hij : i.val + 1 < j.val) (hjk : j.val + 1 < k.val) :
    let γs := characterBandPoint α β q (i.val + 1)
    let γw := characterBandPoint α β q (j.val + 1)
    let νa := characterBandPoint α β q k.val
    ∀ᶠ L : ℝ in atTop, ∀ us Ulate v : ℝ,
      characterBandPoint α β q i.val * L ≤ us → us + 1 ≤ γs * L →
      νa * L ≤ Ulate →
      Ulate + 5 * n ≤ characterBandPoint α β q (k.val + 1) * L →
      Ulate + (n : ℝ) / 10000 ≤ v → v + 1 ≤ Ulate + 2 * (n : ℝ) / 10000 →
      2 ≤ v ∧ us + 2 ≤ v ∧
      α * L ≤ us ∧ α * L ≤ v ∧ us ≤ β * L ∧ v ≤ β * L ∧
      α * L ≤ Ulate ∧ Ulate ≤ β * L ∧
      Ulate ≤ Real.log (characterRoundedTau n v) ∧
      Real.log (characterRoundedTau n v) ≤ Ulate + 2 * (n : ℝ) / 10000 ∧
      3 * Real.exp us + 3 * Real.exp v ≤ 4 * characterRoundedTau n v ∧
      ∀ m : ℕ, (m : ℝ) ≤ z * L → m * Real.exp (γw * L) ≤ characterRoundedTau n v := by
  intro γs γw νa
  have hmono := characterBandPoint_strictMono α β q hαβ hq
  have hgap : γs < νa := hmono (by omega)
  have hwgap : γw < νa := hmono hjk
  have hνapos : 0 < νa := hα.trans_le
    (characterBandPoint_bounds α β q k.val hαβ hq (by omega)).1
  have hUβ := (characterBandPoint_bounds α β q (k.val + 1) hαβ hq (by omega)).2
  have husα := (characterBandPoint_bounds α β q i.val hαβ hq (by omega)).1
  have hγsβ := (characterBandPoint_bounds α β q (i.val + 1) hαβ hq (by omega)).2
  have hνaα := (characterBandPoint_bounds α β q k.val hαβ hq (by omega)).1
  have hnR : (20000 : ℝ) ≤ n := by exact_mod_cast hn
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    (tendsto_id.const_mul_atTop hνapos).eventually (eventually_ge_atTop 2),
    (tendsto_id.const_mul_atTop (sub_pos.mpr hgap)).eventually (eventually_ge_atTop 2),
    eventual_character_top_dominates_bulk z γw νa hz hwgap] with L hL hvlarge hsep hbulk
  intro us Ulate v huslo hushi hUlo hUhi hvlo hvhi
  simp only [id_eq] at hvlarge hsep
  have hv2 : 2 ≤ v := by linarith only [hvlarge, hUlo, hvlo, hnR]
  have hUs : us + 2 ≤ v := by nlinarith only [hushi, hUlo, hvlo, hsep, hnR]
  have hUv : Ulate + 1 ≤ v := by linarith only [hvlo, hnR]
  have hdata := character_rounded_endpoint_bounds n v Ulate hv2 hUv
  have hUupper : Ulate ≤ β * L := by
    have hh := mul_le_mul_of_nonneg_right hUβ hL
    nlinarith only [hh, hUhi, hnR]
  have hvupper : v ≤ β * L := by
    have hh := mul_le_mul_of_nonneg_right hUβ hL
    nlinarith only [hh, hUhi, hvhi, hnR]
  have huslower : α * L ≤ us := (mul_le_mul_of_nonneg_right husα hL).trans huslo
  have hUlower : α * L ≤ Ulate := (mul_le_mul_of_nonneg_right hνaα hL).trans hUlo
  have hvlower : α * L ≤ v := by linarith only [hUlower, hvlo, hnR]
  have husupper : us ≤ β * L := by
    have hh := mul_le_mul_of_nonneg_right hγsβ hL
    linarith only [hh, hushi]
  have hτlo := hdata.2.2.2.2.2.1
  have hτhi := hdata.2.2.2.2.2.2.1
  refine ⟨hv2, hUs, huslower, hvlower, husupper, hvupper, hUlower, hUupper,
    hτlo, hτhi.trans (by linarith only [hvhi]),
    character_rounded_anchor_pair n v Ulate us hv2 hUv hUs, ?_⟩
  intro m hm
  have hτpos : 0 < characterRoundedTau n v := by linarith only [hdata.2.2.1]
  have hh := hbulk m (Real.log (characterRoundedTau n v)) hm (hUlo.trans hτlo)
  rwa [Real.exp_log hτpos] at hh

end Ostmann

end OAI
