import OAI.Combinatorics.LowSpaceSubsetSum.Storage.PermutationDigitsExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Storage.SignMaskExecution

namespace OAI

/-! # Materializing the bounded layout draw

An accepted permutation is stored as an indexed array, and the independent
sign bits are scanned into a bounded mask. Failed permutation draws halt
without using the coupling's ideal backup.
-/

noncomputable section
namespace LowSpaceSubsetSum.RepresentationLayoutExecution

variable {n : ℕ}

def run (R : RepresentationSetup n) (s : R.layoutCoupling.Seed) :
    Option (Vector (Fin n) n × IndexedMask n) × ℕ :=
  let digits := PermutationDigitsExecution.run n n s.1
  match digits.value with
  | none => (none, digits.reads + digits.tests + 1)
  | some d =>
    let v := PermutationArray.build n d
    let signs := SignMaskExecution.run n s.2
    (some (v.1, signs.1), digits.reads + digits.tests + v.2 + signs.2 + 3)

theorem value (R : RepresentationSetup n) (s : R.layoutCoupling.Seed)
    (v : Vector (Fin n) n) (F : IndexedMask n) (h : (run R s).1 = some (v, F)) :
    ∃ e, R.layoutCoupling.bounded s = some (e, F.semantic) ∧
      ∀ i : Fin n, v[i.val] = e i := by
  rcases s with ⟨first, second⟩
  simp only [run] at h
  cases hd : (PermutationDigitsExecution.run n n first).value with
  | none => simp only [hd, reduceCtorEq] at h
  | some d =>
    simp only [hd, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    refine ⟨PermutationArray.semantic n d, ?_, PermutationArray.build_value n d⟩
    have hp := PermutationDigitsExecution.value n n first
    rw [hd] at hp
    have hp' : (permutationCoupling n n).bounded first = some (PermutationArray.semantic n d) := by
      rw [← (SamplerExecution.permutation n n).value_eq]
      exact hp.symm
    have hi := (SamplerExecution.permutation n n).ideal_eq_of_some first
      (PermutationArray.semantic n d) hp.symm
    simp only [RepresentationSetup.layoutCoupling, SamplerCoupling.prod,
      SamplerCoupling.map, SamplerCoupling.bind, hp', reduceCtorEq, ↓reduceIte,
      signCoupling, bitArrayCoupling, Option.map_some]
    rw [hi]
    exact congrArg (fun mask => some (PermutationArray.semantic n d, mask))
      (SignMaskExecution.value n second).symm

theorem complete (R : RepresentationSetup n) (s : R.layoutCoupling.Seed)
    (e : Equiv.Perm (Fin n)) (F : Finset (Fin n))
    (h : R.layoutCoupling.bounded s = some (e, F)) :
    ∃ v mask, (run R s).1 = some (v, mask) ∧ mask.semantic = F ∧
      ∀ i : Fin n, v[i.val] = e i := by
  rcases s with ⟨first, second⟩
  have hp := PermutationDigitsExecution.value n n first
  cases hd : (PermutationDigitsExecution.run n n first).value with
  | none =>
    rw [hd] at hp
    have hp' : (permutationCoupling n n).bounded first = none := by
      rw [← (SamplerExecution.permutation n n).value_eq]
      exact hp.symm
    simp only [RepresentationSetup.layoutCoupling, SamplerCoupling.prod,
      SamplerCoupling.map, SamplerCoupling.bind, hp', ↓reduceIte, Option.map_none,
      reduceCtorEq] at h
  | some d =>
    rw [hd] at hp
    have hp' : (permutationCoupling n n).bounded first = some (PermutationArray.semantic n d) := by
      rw [← (SamplerExecution.permutation n n).value_eq]
      exact hp.symm
    have hi := (SamplerExecution.permutation n n).ideal_eq_of_some first
      (PermutationArray.semantic n d) hp.symm
    simp only [RepresentationSetup.layoutCoupling, SamplerCoupling.prod,
      SamplerCoupling.map, SamplerCoupling.bind, hp', reduceCtorEq, ↓reduceIte,
      signCoupling, bitArrayCoupling, Option.map_some] at h
    have he : PermutationArray.semantic n d = e := hi.symm.trans (congrArg Prod.fst (Option.some.inj h))
    have hF : bitsSubsetEquiv n second = F := congrArg Prod.snd (Option.some.inj h)
    refine ⟨(PermutationArray.build n d).1, (SignMaskExecution.run n second).1, ?_, ?_, ?_⟩
    · simp only [run, hd]
    · exact (SignMaskExecution.value n second).trans hF
    · rw [← he]
      exact PermutationArray.build_value n d

theorem work (R : RepresentationSetup n) (s : R.layoutCoupling.Seed) :
    (run R s).2 ≤ n * n ^ 3 + 10 * (n + 1) ^ 2 + 4 * n + 5 := by
  have hd := PermutationDigitsExecution.counts n n s.1
  simp only [run]
  split
  · dsimp only
    omega
  next d _ =>
    have hv := PermutationArray.build_work n d
    change _ + _ + _ + (4 * n + 2) + 3 ≤ _
    omega

end LowSpaceSubsetSum.RepresentationLayoutExecution

end

end OAI
