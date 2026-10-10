import OAI.Combinatorics.EditApproximation.Binary.BitQueryOn
import OAI.Combinatorics.EditApproximation.Binary.BinaryCachedContinuation
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Executed cache normalization charges the actual Boolean rescaling.
Its exact-value premise is checked on the reachable local result. -/

namespace EditApproximation.BitQuery



theorem normalize_value {ι : Type*} (program : BitQuery ι BinaryFraction)
    (base : List Bool) (hbase : 0 < bitWordValue base) (remaining : ℕ)
    (oracle : ι → BinaryFraction)
    (hden : (program.value oracle).value.den ∣ bitWordValue base ^ remaining) :
    (normalize program base hbase remaining).value oracle =
      (BinaryFraction.finishCachedWithWork (program.value oracle, 0) base hbase remaining).1 ∧
    ((normalize program base hbase remaining).value oracle).value = (program.value oracle).value := by
  refine ⟨by simp only [normalize, value_bind, compute, value], ?_⟩
  simp only [normalize, value_bind, compute, value]
  exact BinaryFraction.finishCachedWithWork_value _ base hbase remaining hden

theorem normalize_keys {ι : Type*} (program : BitQuery ι BinaryFraction)
    (base : List Bool) (hbase : 0 < bitWordValue base) (remaining : ℕ)
    (oracle : ι → BinaryFraction) :
    (normalize program base hbase remaining).keys oracle = program.keys oracle := by
  simp only [normalize, keys_bind, compute, keys, List.append_nil]

theorem normalize_work {ι : Type*} (program : BitQuery ι BinaryFraction)
    (base : List Bool) (hbase : 0 < bitWordValue base) (remaining : ℕ)
    (oracle : ι → BinaryFraction) (readWork : ι → ℕ) :
    (normalize program base hbase remaining).work oracle readWork =
      program.work oracle readWork +
        (BinaryFraction.finishCachedWithWork (program.value oracle, 0) base hbase remaining).2 := by
  simp only [normalize, work_bind, compute, work, Nat.add_zero]

theorem RefinesOn.normalize {ι : Type*} {oracle : ι → BinaryFraction}
    {program : BitQuery ι BinaryFraction} {expected : FiniteQuery ι}
    (h : RefinesOn oracle (fun word value => word.value = value) program expected)
    (base : List Bool) (hbase : 0 < bitWordValue base) (remaining : ℕ)
    (hden : (program.value oracle).value.den ∣ bitWordValue base ^ remaining) :
    RefinesOn oracle (fun word value => word.value = value)
      (normalize program base hbase remaining) expected := by
  apply h.finish
  exact BinaryFraction.finishCachedWithWork_value _ base hbase remaining hden

end EditApproximation.BitQuery

end OAI
