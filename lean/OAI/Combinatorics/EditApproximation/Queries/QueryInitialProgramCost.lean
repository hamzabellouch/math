import OAI.Combinatorics.EditApproximation.Queries.QueryInitialConeProgram
import OAI.Combinatorics.EditApproximation.Queries.QueryInitialCenterCost

namespace OAI

namespace EditApproximation.BinaryFraction

def queryInitialSeedReadBudget (count B : ℕ) : ℕ :=
  16 * B + 7 + count * (16 * B + 6) + 500 * (B + 1) ^ 2

theorem queryInitialSeedReadWithWork_bounds {n : ℕ} (value : BinaryFraction) (q : TargetInterval n)
    (keys : List (TargetInterval n)) (words : List BinaryFraction) (r : TargetInterval n)
    (B : ℕ) (hB : 2 ≤ B) (hn : Nat.size n ≤ B) (hv : value.width ≤ B)
    (hw : ∀ w ∈ words, w.width ≤ B) :
    Nat.size (bitWordValue (queryInitialSeedReadWithWork value q keys words r).1) ≤ B + 2 ∧
      (queryInitialSeedReadWithWork value q keys words r).2 ≤ queryInitialSeedReadBudget keys.length B := by
  have htest := queryIntervalEqualWithWork_cost r q B hn
  have hread := queryParentReadWithWork_cost keys words r
  have hwidth : (queryParentReadWithWork keys words r).1.width ≤ B :=
    gatheredWordLookupWithWork_width _ keys words r B hB hw
  have hsize (v : BinaryFraction) (h : v.width ≤ B) :
      Nat.size (bitWordValue (naturalCeilingWithWork v).1) ≤ B + 2 :=
    (Nat.size_le.mpr (bitWordValue_lt_pow_length _)).trans ((naturalCeilingWithWork_length v).trans (by omega))
  have hcost (v : BinaryFraction) (h : v.width ≤ B) :
      (naturalCeilingWithWork v).2 ≤ 500 * (B + 1) ^ 2 :=
    (naturalCeilingWithWork_cost v).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  unfold queryInitialSeedReadWithWork queryInitialSeedReadBudget
  dsimp only
  split_ifs
  · exact ⟨hsize value hv, by have := hcost value hv; omega⟩
  · exact ⟨hsize _ hwidth, by
      have := hcost _ hwidth
      have hread' : (queryParentReadWithWork keys words r).2 ≤ 1 + keys.length * (16 * B + 6) :=
        hread.trans (by gcongr)
      omega⟩

def queryInitialProgramBitBudget (P Amax B C : ℕ) : ℕ :=
  let count := (B + 1) * (64 * Amax ^ 2 * P + 2) ^ 2
  C + queryInitialCentersBitBudget P Amax B + count * (C + 3) +
    cachedInitialProgramBitBudget P Amax (B + 2) * (queryInitialSeedReadBudget count B + 2)

end EditApproximation.BinaryFraction

namespace EditApproximation

private theorem initial_program_sum_bound {κ : Type*} (keys : List κ) (f : κ → ℕ) (C : ℕ)
    (hf : ∀ key ∈ keys, f key ≤ C) : (keys.map f).sum ≤ keys.length * C := by
  induction keys with
  | nil => simp
  | cons key keys ih =>
    have hh := hf key List.mem_cons_self
    have ht := ih (fun k hk => hf k (List.mem_cons_of_mem key hk))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

open BinaryFraction

theorem queryInitialConeProgramAt_work {ι : Type*} {n : ℕ}
    (sourceLength N P F : ℕ) (A a : BinaryFraction)
    (reader : TargetInterval n → BitQuery ι BinaryFraction) (q : TargetInterval n)
    (oracle : ι → BinaryFraction) (readWork : ι → ℕ) :
    let value := (reader q).value oracle
    let keys := queryInitialConeCentersWithWork N P A value q
    let words := keys.1.map fun r => (reader r).value oracle
    (queryInitialConeProgramAt sourceLength N P F A a reader q).work oracle readWork =
      (reader q).work oracle readWork + keys.2 +
        (keys.1.map fun r => (reader r).work oracle readWork + 3).sum +
        (cachedInitialProgramReadWithWork sourceLength N P F A a
          (queryInitialSeedReadWithWork value q keys.1 words) q).2 := by
  simp only [queryInitialConeProgramAt, BitQuery.work_bind, BitQuery.work_collect,
    BitQuery.compute, BitQuery.work, BitQuery.value, Nat.add_zero, Nat.add_assoc]

theorem queryInitialConeProgramAt_width {ι : Type*} {n : ℕ}
    (sourceLength N P F : ℕ) (A a : BinaryFraction)
    (reader : TargetInterval n → BitQuery ι BinaryFraction) (q : TargetInterval n)
    (oracle : ι → BinaryFraction) (hP : 0 < P) :
    ((queryInitialConeProgramAt sourceLength N P F A a reader q).value oracle).width ≤
      Nat.size ((32 * F + 1) * N) + 3 := by
  classical
  let value := (reader q).value oracle
  let keys := queryInitialConeCentersWithWork N P A value q
  let words := keys.1.map fun r => (reader r).value oracle
  let seed := queryInitialSeedReadWithWork value q keys.1 words
  let R := Finset.univ.sup (fun r => (seed r).2)
  have hR (r : TargetInterval n) : (seed r).2 ≤ R :=
    Finset.le_sup (f := fun r => (seed r).2) (Finset.mem_univ r)
  have heq := (cachedInitialProgramReadWithWork_eq_cost sourceLength N P F A a seed q R hR).1
  have hw0 := fun (U : TargetInterval (List.replicate n ()).length → ℕ) r =>
    (cachedInitialProgramWithWork_value_width (List.replicate sourceLength ())
      (List.replicate n ()) N P F A a U r hP).2
  generalize hy : (List.replicate n ()).length = ny at hw0
  simp only [List.length_replicate] at hy
  subst ny
  have hw := hw0 (fun r => bitWordValue (seed r).1) q
  simp only [List.length_replicate] at hw
  simp only [queryInitialConeProgramAt, BitQuery.value_bind, BitQuery.value_collect,
    BitQuery.compute, BitQuery.value]
  change (cachedInitialProgramReadWithWork sourceLength N P F A a seed q).1.width ≤ _
  rw [heq]
  exact hw

theorem queryInitialConeProgramAt_work_bound {ι : Type*} {n : ℕ}
    (sourceLength N P F Amax B C : ℕ) (hP : 0 < P) (A a : BinaryFraction)
    (reader : TargetInterval n → BitQuery ι BinaryFraction) (q : TargetInterval n)
    (oracle : ι → BinaryFraction) (readWork : ι → ℕ)
    (hB : 8 ≤ B) (hN : Nat.size N ≤ B) (hPb : Nat.size P ≤ B) (hF : Nat.size F ≤ B)
    (hnx : Nat.size sourceLength ≤ B) (hny : Nat.size n ≤ B)
    (hA : A.width ≤ B) (ha : a.width ≤ B) (hAone : 1 ≤ A.value) (hAmax : A.value ≤ Amax)
    (hw : ∀ r, ((reader r).value oracle).width ≤ B)
    (hc : ∀ r, (reader r).work oracle readWork ≤ C) :
    (queryInitialConeProgramAt sourceLength N P F A a reader q).work oracle readWork ≤
      queryInitialProgramBitBudget P Amax B C := by
  let value := (reader q).value oracle
  let keys := queryInitialConeCentersWithWork N P A value q
  let words := keys.1.map fun r => (reader r).value oracle
  let seed := queryInitialSeedReadWithWork value q keys.1 words
  have hk := queryInitialConeCentersWithWork_bounds N P Amax B A value q hB hP hN hPb hny hA (hw q) hAone hAmax
  have hs (r : TargetInterval n) := queryInitialSeedReadWithWork_bounds value q keys.1 words r B
    (by omega) hny (hw q) (by
      intro w hmem
      obtain ⟨key, _, rfl⟩ := List.mem_map.mp hmem
      exact hw key)
  have hseed : ∀ r, (seed r).2 ≤ queryInitialSeedReadBudget ((B + 1) * (64 * Amax ^ 2 * P + 2) ^ 2) B := by
    intro r
    apply (hs r).2.trans
    unfold queryInitialSeedReadBudget
    exact Nat.add_le_add_right (Nat.add_le_add_left
      (Nat.mul_le_mul_right (16 * B + 6) hk.1) _) _
  have hkernel := (cachedInitialProgramReadWithWork_eq_cost sourceLength N P F A a seed q _ hseed).2
  have hplain := cachedInitialProgramWithWork_cost sourceLength N P F Amax (B + 2) A a
    (fun r => bitWordValue (seed r).1) q (by omega) hP (by omega) (by omega) (by omega)
    (by omega) (by omega) (fun r => (hs r).1) (by omega) (by omega) hAone hAmax
  have hkernel' := hkernel.trans (Nat.mul_le_mul_right _ hplain)
  have hsum := (initial_program_sum_bound keys.1 (fun r => (reader r).work oracle readWork + 3) (C + 3)
    (fun r _ => Nat.add_le_add_right (hc r) 3)).trans (Nat.mul_le_mul_right _ hk.1)
  rw [queryInitialConeProgramAt_work]
  change (reader q).work oracle readWork + keys.2 +
    (keys.1.map fun r => (reader r).work oracle readWork + 3).sum +
    (cachedInitialProgramReadWithWork sourceLength N P F A a seed q).2 ≤ _
  have hcq := hc q
  have hkc : keys.2 ≤ queryInitialCentersBitBudget P Amax B := hk.2
  unfold queryInitialProgramBitBudget
  dsimp only
  omega

end EditApproximation

end OAI
