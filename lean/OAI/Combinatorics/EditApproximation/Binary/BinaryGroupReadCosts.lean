import OAI.Combinatorics.EditApproximation.Binary.BinaryBandReadCosts
import OAI.Combinatorics.EditApproximation.Binary.BinaryGroupActionReads

namespace OAI

/-! Exact group score scans charge the finite-buffer readers through the
same loops as their arithmetic-only counterparts. -/

namespace EditApproximation
namespace BinaryFraction

theorem scoredArgmaxWithWork_factor {α : Type*} (read plain : α → BinaryFraction × ℕ)
    (xs : List α) (K : ℕ) (hK : 1 ≤ K)
    (hv : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hc : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 * K) :
    (scoredArgmaxWithWork read xs).1 = (scoredArgmaxWithWork plain xs).1 ∧
    (scoredArgmaxWithWork read xs).2 ≤ (scoredArgmaxWithWork plain xs).2 * K := by
  induction xs with
  | nil => exact ⟨rfl, by simp only [scoredArgmaxWithWork, Nat.zero_mul, le_refl]⟩
  | cons x xs ih =>
    have hx := hv x List.mem_cons_self
    have hcx := hc x List.mem_cons_self
    have ht := ih (fun y hy => hv y (List.mem_cons_of_mem _ hy))
      (fun y hy => hc y (List.mem_cons_of_mem _ hy))
    have h := Nat.add_le_add ht.2 hcx
    rw [← Nat.add_mul] at h
    simp only [scoredArgmaxWithWork, ht.1, hx]
    cases (scoredArgmaxWithWork plain xs).1 with
    | none =>
      refine ⟨rfl, ?_⟩
      dsimp only
      apply cost_replace_factor _ _ _ _ _ h hK <;> omega
    | some best =>
      refine ⟨rfl, ?_⟩
      dsimp only
      apply cost_replace_factor _ _ _ _ _ h hK <;> omega

theorem selectGroupWithWork_factor {α : Type*} (read plain : α → BinaryFraction × ℕ)
    (xs : List α) (hne : xs ≠ []) (K : ℕ) (hK : 1 ≤ K)
    (hv : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hc : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 * K) :
    (selectGroupWithWork xs hne read).1 = (selectGroupWithWork xs hne plain).1 ∧
    (selectGroupWithWork xs hne read).2 ≤ (selectGroupWithWork xs hne plain).2 * K := by
  have h := scoredArgmaxWithWork_factor
    (fun x => ((read x).1.neg, (read x).2 + 1))
    (fun x => ((plain x).1.neg, (plain x).2 + 1)) xs K hK
    (fun x hx => by rw [hv x hx]) (fun x hx => by
      apply cost_replace_factor _ _ _ _ _ (hc x hx) hK <;> omega)
  unfold selectGroupWithWork
  dsimp only
  rw [h.1]
  refine ⟨rfl, ?_⟩
  apply cost_replace_factor _ _ _ _ _ h.2 hK <;> omega

section Group
variable {α : Type*} (source target : List α) {M T : ℕ}
  (parent : TargetInterval source.length) (b P exponent Q : ℕ)
  (tau F : BinaryFraction)
  (child : Fin M → TargetInterval target.length → BinaryFraction)
  (initial current : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (scales : Fin T → BinaryFraction)
  (draw : ∀ t, Fin (groupSampleCount M Q b (scales t).value) → Fin M)

local notation "Member" => UnskippedBand source target parent b P exponent
  (BinaryFraction.value tau) (BinaryFraction.value F)
  (fun i q => BinaryFraction.value (child i q))
  (fun i q => BinaryFraction.value (Prod.fst (initial i q)))

theorem unskippedEstimateReadWithWork_factor (member : Member) (R : ℕ)
    (hi : ∀ i q, (initial i q).2 ≤ R) (hr : ∀ i q, (current i q).2 ≤ R) :
    (unskippedEstimateReadWithWork source target parent b P exponent Q tau F child initial current
      scales draw member).2 ≤
      (unskippedEstimateWithWork source target parent b P exponent Q tau F child
        (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw member).2 *
        tableReadFactor R := by
  have hm := envelopeVectorReadWithWork_factor b member.actions initial R hi
  have hmq := (envelopeVectorReadWithWork_eq_cost b member.actions initial R hi).1
  have hp := roundedBandReadWithWork_factor exponent b member.actions member.nonempty initial R hi
  have hpq := (roundedBandReadWithWork_eq_cost exponent b member.actions member.nonempty initial R hi).1
  have hv := vectorMapWithWork_factor M
    (fun i => current i ((roundedBandWithWork exponent b member.actions member.nonempty
      (fun j q => (initial j q).1)).1.get i))
    (fun i => ((current i ((roundedBandWithWork exponent b member.actions member.nonempty
      (fun j q => (initial j q).1)).1.get i)).1, 1))
    (tableReadFactor R) (tableReadFactor_pos R) (fun _ => rfl)
    (fun i => by
      change (current i _).2 ≤ 1 * tableReadFactor R
      have hR : R ≤ tableReadFactor R := by unfold tableReadFactor; omega
      simpa only [Nat.one_mul] using (hr i _).trans hR)
  have h := Nat.add_le_add (Nat.add_le_add hm hp) hv.2
  simp only [← Nat.add_mul] at h
  unfold unskippedEstimateReadWithWork unskippedEstimateWithWork
  dsimp only
  rw [hmq, hpq, hv.1]
  apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R) <;> omega

theorem chooseUnskippedReadWithWork_factor (members : List Member) (hne : members ≠ []) (R : ℕ)
    (hi : ∀ i q, (initial i q).2 ≤ R) (hr : ∀ i q, (current i q).2 ≤ R) :
    (chooseUnskippedReadWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).2 ≤
      (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child
        (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).2 *
        tableReadFactor R := by
  exact (selectGroupWithWork_factor _ _ members hne (tableReadFactor R) (tableReadFactor_pos R)
    (fun member _ => (unskippedEstimateReadWithWork_eq_cost source target parent b P exponent Q
      tau F child initial current scales draw member R R hi hr).1)
    (fun member _ => unskippedEstimateReadWithWork_factor source target parent b P exponent Q
      tau F child initial current scales draw member R hi hr)).2

theorem sampledGroupActionReadWithWork_factor (members : List Member) (hne : members ≠ []) (R : ℕ)
    (hi : ∀ i q, (initial i q).2 ≤ R) (hr : ∀ i q, (current i q).2 ≤ R) :
    (sampledGroupActionReadWithWork source target parent b P exponent Q tau F child initial current
      scales draw members hne).2 ≤
      (sampledGroupActionWithWork source target parent b P exponent Q tau F child
        (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).2 *
        tableReadFactor R := by
  have hc := chooseUnskippedReadWithWork_factor source target parent b P exponent Q tau F
    child initial current scales draw members hne R hi hr
  have hcq := (chooseUnskippedReadWithWork_eq_cost source target parent b P exponent Q tau F
    child initial current scales draw members hne R R hi hr).1
  have hp := roundedBandReadWithWork_factor exponent b
    (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child
      (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).1.actions
    (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child
      (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).1.nonempty initial R hi
  have hpq := (roundedBandReadWithWork_eq_cost exponent b
    (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child
      (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).1.actions
    (chooseBinaryUnskippedWithWork source target parent b P exponent Q tau F child
      (fun i q => (initial i q).1) (fun i q => (current i q).1) scales draw members hne).1.nonempty initial R hi).1
  have h := Nat.add_le_add hc hp
  rw [← Nat.add_mul] at h
  unfold sampledGroupActionReadWithWork sampledGroupActionWithWork
  dsimp only
  simp only [hcq, hpq]
  apply cost_replace_factor _ _ _ _ _ h (tableReadFactor_pos R) <;> omega

end Group
end BinaryFraction
end EditApproximation

end OAI
