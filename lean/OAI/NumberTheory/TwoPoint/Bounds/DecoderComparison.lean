import OAI.NumberTheory.TwoPoint.Bounds.EncodedCoefficients
import OAI.NumberTheory.TwoPoint.Circuits.CircuitEncoding

namespace OAI

/-! Uniform decoding-error estimates for the finite jitter construction. -/

namespace TwoPointCorrelations

open Finset

lemma uniformAverage_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (h : ∀ x, f x ≤ g x) : uniformAverage f ≤ uniformAverage g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => h x)) (Nat.cast_nonneg _)

lemma uniformAverage_sum {α ι : Type*} [Fintype α] [Fintype ι] (f : ι → α → ℝ) :
    uniformAverage (fun x => ∑ i, f i x) = ∑ i, uniformAverage (f i) := by
  unfold uniformAverage
  rw [Finset.sum_comm, Finset.sum_div]

lemma abs_uniformAverage_sub_le {α : Type*} [Fintype α] (f g h : α → ℝ)
    (hfg : ∀ x, |f x - g x| ≤ h x) :
    |uniformAverage f - uniformAverage g| ≤ uniformAverage h := by
  unfold uniformAverage
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div,
    show |(Fintype.card α : ℝ)| = (Fintype.card α : ℝ) from abs_of_nonneg (Nat.cast_nonneg _)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun x _ => hfg x))

lemma uniformAverage_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : ι → Type*) [∀ i, Fintype (β i)] [∀ i, Nonempty (β i)] (i : ι)
    (f : β i → ℝ) :
    uniformAverage (fun x : ∀ j, β j => f (x i)) = uniformAverage f := by
  let e := Equiv.piSplitAt i β
  calc
    _ = uniformAverage (fun x : β i × (∀ j : {j // j ≠ i}, β j) => f x.1) :=
      uniformAverage_equiv e (fun x => f x.1)
    _ = _ := by
      rw [uniformAverage_prod (fun (x : β i) (_y : ∀ j : {j // j ≠ i}, β j) => f x)]
      simp only [uniformAverage_const]

noncomputable def decodedResidues {m : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (B : ℕ) (x : Fin m → BooleanCube B) : ∀ i, ZMod (s i) :=
  fun i => ZMod.finEquiv (s i) (decodeBits (NeZero.pos (s i)) (x i))

lemma decodedResidues_jitter {m B : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (r : ∀ i, ZMod (s i)) (j : Fin m → Fin (2 ^ B)) (i : Fin m) :
    decodedResidues s B (crtJitterBits s B r j) i =
      ZMod.finEquiv (s i) (jitterDecode (NeZero.pos (s i)) (by positivity)
        (jitterCode ((ZMod.finEquiv (s i)).symm (r i)) (j i))) := by
  change ZMod.finEquiv (s i) (decodeBits (NeZero.pos (s i))
    (jitterBits ((ZMod.finEquiv (s i)).symm (r i)) (j i))) = _
  rw [decode_jitterBits]

lemma decoded_coordinate_error {m B : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (r : ∀ i, ZMod (s i)) (i : Fin m) :
    uniformAverage (fun j : Fin m → Fin (2 ^ B) =>
      if decodedResidues s B (crtJitterBits s B r j) i ≠ r i then (1 : ℝ) else 0) ≤
        (s i : ℝ) / (2 ^ B : ℕ) := by
  let : Nonempty (Fin (2 ^ B)) := ⟨⟨0, by positivity⟩⟩
  simp_rw [decodedResidues_jitter]
  rw [uniformAverage_coordinate (fun _ : Fin m => Fin (2 ^ B)) i
    (fun j => if ZMod.finEquiv (s i) (jitterDecode (NeZero.pos (s i)) (by positivity)
      (jitterCode ((ZMod.finEquiv (s i)).symm (r i)) j)) ≠ r i then (1 : ℝ) else 0)]
  have heq (j : Fin (2 ^ B)) :
      (ZMod.finEquiv (s i) (jitterDecode (NeZero.pos (s i)) (by positivity)
        (jitterCode ((ZMod.finEquiv (s i)).symm (r i)) j)) ≠ r i) ↔
      jitterDecode (NeZero.pos (s i)) (by positivity)
        (jitterCode ((ZMod.finEquiv (s i)).symm (r i)) j) ≠
          (ZMod.finEquiv (s i)).symm (r i) := by
    exact not_congr (ZMod.finEquiv (s i)).toEquiv.eq_symm_apply.symm
  simp_rw [heq]
  simpa only [uniformAverage, Fintype.card_fin] using
    jitterDecode_error (NeZero.pos (s i)) (by positivity) ((ZMod.finEquiv (s i)).symm (r i))

noncomputable def eventIndicator {α : Type*} (E : α → Bool) (x : α) : ℝ := if E x then 1 else 0

lemma eventIndicator_difference_le_coordinate_errors {m : ℕ} (s : Fin m → ℕ)
    (E : (∀ i, ZMod (s i)) → Bool) (r d : ∀ i, ZMod (s i)) :
    |eventIndicator E r - eventIndicator E d| ≤
      ∑ i : Fin m, if d i ≠ r i then (1 : ℝ) else 0 := by
  by_cases heq : d = r
  · subst d
    simp
  · have hex : ∃ i, d i ≠ r i := by
      by_contra h
      push Not at h
      exact heq (funext h)
    obtain ⟨i, hi⟩ := hex
    have hsum : (1 : ℝ) ≤ ∑ j : Fin m, if d j ≠ r j then (1 : ℝ) else 0 := by
      have h := Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin m))) (a := i)
        (f := fun j => if d j ≠ r j then (1 : ℝ) else 0)
        (by intro j _; split_ifs <;> norm_num) (Finset.mem_univ i)
      change (if d i ≠ r i then (1 : ℝ) else 0) ≤ _ at h
      rw [ite_eq_left hi] at h
      exact h
    have hdiff : |eventIndicator E r - eventIndicator E d| ≤ 1 := by
      cases hr : E r <;> cases hd : E d <;> norm_num [eventIndicator, hr, hd]
    exact hdiff.trans hsum

/-- Every event has decoding error at most the sum of the coordinate errors.
This statement imposes no circuit assumption; circuits enter only in the
comparison of the encoded distributions. -/
theorem decoder_event_error {m B : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (E : (∀ i, ZMod (s i)) → Bool) (r : ∀ i, ZMod (s i)) :
    |eventIndicator E r - uniformAverage (fun j : Fin m → Fin (2 ^ B) =>
      eventIndicator E (decodedResidues s B (crtJitterBits s B r j)))| ≤
        ∑ i : Fin m, (s i : ℝ) / (2 ^ B : ℕ) := by
  let : Nonempty (Fin (2 ^ B)) := ⟨⟨0, by positivity⟩⟩
  have h := abs_uniformAverage_sub_le
    (fun _j : Fin m → Fin (2 ^ B) => eventIndicator E r)
    (fun j => eventIndicator E (decodedResidues s B (crtJitterBits s B r j)))
    (fun j => ∑ i : Fin m,
      if decodedResidues s B (crtJitterBits s B r j) i ≠ r i then (1 : ℝ) else 0)
    (fun _ => eventIndicator_difference_le_coordinate_errors s E r _)
  rw [uniformAverage_const, uniformAverage_sum] at h
  exact h.trans (Finset.sum_le_sum (fun i _ => decoded_coordinate_error s r i))

/-- The same decoder bound holds after averaging over an arbitrary finite
law of origins represented as a uniformly sampled finite map. -/
theorem decoder_event_error_averaged {α : Type*} [Fintype α] [Nonempty α]
    {m B : ℕ} (s : Fin m → ℕ) [∀ i, NeZero (s i)]
    (E : (∀ i, ZMod (s i)) → Bool) (r : α → ∀ i, ZMod (s i)) :
    |uniformAverage (fun x => eventIndicator E (r x)) -
      uniformAverage (fun x => uniformAverage (fun j : Fin m → Fin (2 ^ B) =>
        eventIndicator E (decodedResidues s B (crtJitterBits s B (r x) j))))| ≤
      ∑ i : Fin m, (s i : ℝ) / (2 ^ B : ℕ) := by
  have h := abs_uniformAverage_sub_le
    (fun x => eventIndicator E (r x))
    (fun x => uniformAverage (fun j : Fin m → Fin (2 ^ B) =>
      eventIndicator E (decodedResidues s B (crtJitterBits s B (r x) j))))
    (fun _x : α => ∑ i : Fin m, (s i : ℝ) / (2 ^ B : ℕ))
    (fun x => decoder_event_error s E (r x))
  simpa only [uniformAverage_const] using h

end TwoPointCorrelations

end OAI
