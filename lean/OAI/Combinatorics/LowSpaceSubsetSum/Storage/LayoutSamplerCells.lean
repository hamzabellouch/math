import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PermutationSamplerCells
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.MeasuredFilterCells
import OAI.Combinatorics.LowSpaceSubsetSum.Representation.RepresentationLayoutExecution

namespace OAI

/-! # Live stored arrays for the actual permutation and sign draw -/

noncomputable section
namespace LowSpaceSubsetSum.LayoutSamplerCells

variable {n : ℕ}

private theorem mask_ext {a b : IndexedMask n} (h : a.indices = b.indices) : a = b := by
  cases a
  cases b
  cases h
  rfl

def signs (n : ℕ) (bits : Fin n → Bool) : (IndexedMask n × ℕ) × ℕ :=
  let r := MeasuredFilterCells.run (fun i => ((bits i, 0), 2)) (List.finRange n)
  ((⟨r.1.1, (MeasuredFilterCells.run_length _ _).trans (by simp only [List.length_finRange]; omega)⟩,
    4*n+2), r.2+2*n+8)

theorem signs_value (n : ℕ) (bits : Fin n → Bool) :
    (signs n bits).1 = SignMaskExecution.run n bits := by
  apply Prod.ext
  · apply mask_ext
    simp only [signs, SignMaskExecution.run, MeasuredFilterCells.run_value,
      MeasuredFilter.runAcc_value, List.reverse_nil, List.nil_append]
  · rfl

theorem signs_cells (n : ℕ) (bits : Fin n → Bool) : (signs n bits).2 ≤ 4*n+14 := by
  have h := MeasuredFilterCells.run_cells
    (fun i : Fin n => ((bits i, 0), 2)) 2 (fun _ => le_rfl) (List.finRange n)
  simp only [List.length_finRange] at h
  change _+2*n+8 ≤ _
  omega

def run (R : RepresentationSetup n) (s : R.layoutCoupling.Seed) :
    (Option (Vector (Fin n) n × IndexedMask n) × ℕ) × ℕ :=
  let digits := PermutationSamplerCells.run n n s.1
  match digits.1.value with
  | none => ((none, digits.1.reads+digits.1.tests+1), digits.2+n+16)
  | some d =>
    let v := PermutationArray.build n d
    let mask := signs n s.2
    ((some (v.1, mask.1.1), digits.1.reads+digits.1.tests+v.2+mask.1.2+3),
      digits.2+PermutationArray.peakCells n+mask.2+3*n+32)

theorem run_value (R : RepresentationSetup n) (s : R.layoutCoupling.Seed) :
    (run R s).1 = RepresentationLayoutExecution.run R s := by
  have h := signs_value n s.2
  have h₁ := congrArg Prod.fst h
  have h₂ := congrArg Prod.snd h
  simp only [run, RepresentationLayoutExecution.run, PermutationSamplerCells.run_value, h₁, h₂]
  split <;> simp_all only

theorem run_cells (R : RepresentationSetup n) (s : R.layoutCoupling.Seed) :
    (run R s).2 ≤ (n+1)*(3*n^3+128)+32*(n+1)^2 := by
  have hd := PermutationSamplerCells.run_cells n n s.1
  have hp := PermutationArray.peakCells_bound n
  have hs := signs_cells n s.2
  simp only [run]
  split <;> dsimp only <;> nlinarith only [hd, hp, hs, Nat.zero_le (n^2), Nat.zero_le (n^3)]

theorem run_cells_scale (R : RepresentationSetup n) (hn : 10000 ≤ n)
    (s : R.layoutCoupling.Seed) : (run R s).2 ≤ inputScale R.input^6 := by
  have hu : n+1 ≤ inputScale R.input := by unfold inputScale; omega
  have hn' : n ≤ inputScale R.input := by omega
  have hu0 : 10000 ≤ inputScale R.input := by omega
  have hp3 := Nat.pow_le_pow_left hn' 3
  have hp2 := Nat.pow_le_pow_left hu 2
  have hu3 : inputScale R.input ≤ inputScale R.input^3 := by
    simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ inputScale R.input)
      (by decide : 1 ≤ 3)
  have ht : 3*n^3+128 ≤ 4*inputScale R.input^3 := by nlinarith only [hp3, hu3, hu0]
  have hm := Nat.mul_le_mul hu ht
  have hm' : (n+1)*(3*n^3+128) ≤ 4*inputScale R.input^4 := by
    convert hm using 1; ring
  have h24 : inputScale R.input^2 ≤ inputScale R.input^4 :=
    pow_le_pow_right' (by omega) (by decide)
  have h46 : 36*inputScale R.input^4 ≤ inputScale R.input^6 := by
    have hcoef : 36 ≤ inputScale R.input^2 := by nlinarith only [hu0]
    calc
      _ ≤ inputScale R.input^2*inputScale R.input^4 := Nat.mul_le_mul_right _ hcoef
      _ = _ := by rw [← pow_add]
  have h := run_cells R s
  nlinarith only [h, hm', hp2, h24, h46]

end LowSpaceSubsetSum.LayoutSamplerCells

end

end OAI
