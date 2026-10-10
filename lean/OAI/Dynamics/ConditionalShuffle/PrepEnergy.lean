import OAI.Dynamics.ConditionalShuffle.UniformEnergy

namespace OAI

noncomputable section
open scoped Classical
namespace Thorp.Conditional

lemma rawEnergy_nonneg {d : ℕ} (v : RawState d) : 0 ≤ rawEnergy v :=
  Finset.sum_nonneg (fun x _ => sq_nonneg (v.weight x))

lemma rawIterate_energy_le (d : ℕ) (v : RawState (d+1)) (t : ℕ) (ω : SweepHistory d t) :
    rawEnergy (rawIterate d v t ω) ≤ rawEnergy v := by
  induction t with
  | zero => exact le_rfl
  | succ t ih => exact (physicalFlow_energy_le d _ _ _).trans (ih (Fin.init ω))

lemma rawPermute_eq_of_free {d : ℕ} (v : RawState d)
    (hw : ∀ x, v.free x = false → v.weight x = 0) (g h : State d)
    (he : ∀ x, v.free x = true → g x = h x) : rawPermute v g = rawPermute v h := by
  have hm (y : Position d) (hy : v.free (g.symm y) = true) : h.symm y = g.symm y := by
    apply h.injective
    rw [Equiv.apply_symm_apply, ← he _ hy, Equiv.apply_symm_apply]
  have hn (y : Position d) (hy : v.free (g.symm y) = false) : v.free (h.symm y) = false := by
    by_contra hn
    have hh : v.free (h.symm y) = true := by cases hx : v.free (h.symm y) <;> simp_all
    have hg : g (h.symm y) = y := (he _ hh).trans (h.apply_symm_apply y)
    have hi : h.symm y = g.symm y := by simpa using congrArg g.symm hg
    rw [hi, hy] at hh
    contradiction
  apply RawState.ext
  · funext y
    cases hy : v.free (g.symm y)
    · exact hy.trans (hn y hy).symm
    · change v.free (g.symm y) = v.free (h.symm y)
      rw [hm y hy]
  · funext y
    change v.weight (g.symm y) = v.weight (h.symm y)
    cases hy : v.free (g.symm y)
    · rw [hw _ hy, hw _ (hn y hy)]
    · rw [hm y hy]

def extendTuple {α β : Type*} [Finite α] [Finite β] (e : α → β) (he : Function.Injective e)
    (z : α → β) : Equiv.Perm β :=
  if hz : Function.Injective z then (Equiv.Perm.exists_extending_pair e z he hz).choose else 1

lemma extendTuple_extends {α β : Type*} [Finite α] [Finite β] (e : α → β) (he : Function.Injective e)
    (z : α → β) (hz : Function.Injective z) (a : α) : extendTuple e he z (e a) = z a := by
  simp only [extendTuple, dite_eq_left hz]
  exact (Equiv.Perm.exists_extending_pair e z he hz).choose_spec a

lemma rawPermute_extend_free {d : ℕ} (v : RawState d)
    (hw : ∀ x, v.free x = false → v.weight x = 0)
    (g : State d) :
    rawPermute v (extendTuple
      (fun i : Fin (Fintype.card {x // v.free x = true}) =>
        ((Fintype.equivFin {x // v.free x = true}).symm i).val)
      (Subtype.val_injective.comp (Fintype.equivFin _).symm.injective)
      (fun i => g ((Fintype.equivFin {x // v.free x = true}).symm i).val)) = rawPermute v g := by
  apply rawPermute_eq_of_free v hw
  intro x hx
  let a : {x // v.free x = true} := ⟨x,hx⟩
  have hh := extendTuple_extends
    (fun i : Fin (Fintype.card {x // v.free x = true}) =>
      ((Fintype.equivFin {x // v.free x = true}).symm i).val)
    (Subtype.val_injective.comp (Fintype.equivFin _).symm.injective)
    (fun i => g ((Fintype.equivFin {x // v.free x = true}).symm i).val)
    (g.injective.comp (Subtype.val_injective.comp (Fintype.equivFin _).symm.injective))
    ((Fintype.equivFin _) a)
  simpa only [Equiv.symm_apply_apply] using hh

lemma prep_score_bound (d m : ℕ) (v : RawState (d+2))
    (hw : ∀ x, v.free x = false → v.weight x = 0)
    (hm : Fintype.card (Position (d+2)) ≤ 8*m)
    (hk : freeCount v.free + m ≤ Fintype.card (Position (d+2)))
    (F : RawState (d+2) → ℝ) (hF : ∀ g : State (d+2), 0 ≤ F (rawPermute v g))
    (hFC : ∀ g : State (d+2), F (rawPermute v g) ≤ rawEnergy v) :
    mean (fun ω : History (d+2) (200*(d+2)) => F (rawPermute v (run (d+2) (200*(d+2)) ω))) ≤
      mean (fun g : State (d+2) => F (rawPermute v g)) + rawEnergy v *
        (freeCount v.free : ℝ) * Real.sqrt ((Fintype.card (Position (d+2)) : ℝ) *
          ((1/2 : ℝ)^(8*(d+2)) + 32*(9/10 : ℝ)^m)) := by
  let A := {x // v.free x = true}
  let k := Fintype.card A
  have hc : k = freeCount v.free := Fintype.card_subtype _
  let e (i : Fin k) : Position (d+2) := ((Fintype.equivFin A).symm i).val
  have he : Function.Injective e := Subtype.val_injective.comp (Fintype.equivFin A).symm.injective
  let C := rawEnergy v
  have hC : 0 ≤ C := rawEnergy_nonneg v
  by_cases hzero : C = 0
  · have hg (g : State (d+2)) : F (rawPermute v g) = 0 := le_antisymm
      (by simpa only [← show C = rawEnergy v from rfl, hzero] using hFC g) (hF g)
    simp only [hg, mean_zero, ← show C = rawEnergy v from rfl, hzero, zero_mul, add_zero, le_refl]
  have hpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hzero)
  let f (z : Fin k → Position (d+2)) := F (rawPermute v (extendTuple e he z)) / C
  have hf (z) : |f z| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg (hF _) hC)]
    exact (div_le_one hpos).mpr (hFC _)
  have hspec (g : State (d+2)) : f (g ∘ e) = F (rawPermute v g) / C := by
    dsimp only [f]
    exact congrArg (fun u => F u / C) (rawPermute_extend_free v hw g)
  have hh := prefix_test_bound d m hm k (by simpa only [hc] using hk) e he f hf
  simp_rw [hspec] at hh
  rw [mean_div_const, mean_div_const, ← sub_div] at hh
  have hle := (le_abs_self _).trans hh
  have hmul := (div_le_iff₀ hpos).mp hle
  rw [hc] at hmul
  change _ ≤ _ + C * _ * _
  nlinarith

lemma prep_sweep_energy (d m t : ℕ) (ht : t ≤ d+2) (v : RawState (d+2))
    (hw : ∀ x, v.free x = false → v.weight x = 0) (hz : ∑ x, v.weight x = 0)
    (hm : Fintype.card (Position (d+2)) ≤ 8*m)
    (hk : freeCount v.free + m ≤ Fintype.card (Position (d+2)))
    (hf : Fintype.card (Position (d+2)) ≤ 64 * freeCount v.free)
    (hs : 256 * (t+1) ≤ Fintype.card (Position (d+2))) :
    mean (fun ω : History (d+2) (200*(d+2)) => mean (fun η : SweepHistory (d+1) t =>
      rawEnergy (rawIterate (d+1) (rawPermute v (run (d+2) (200*(d+2)) ω)) t η))) ≤
      rawEnergy v * ((255/256 : ℝ)^t + (freeCount v.free : ℝ) *
        Real.sqrt ((Fintype.card (Position (d+2)) : ℝ) *
          ((1/2 : ℝ)^(8*(d+2)) + 32*(9/10 : ℝ)^m))) := by
  have hh := prep_score_bound d m v hw hm hk
    (fun u => mean (fun η : SweepHistory (d+1) t => rawEnergy (rawIterate (d+1) u t η)))
    (fun g => mean_nonneg (fun η => rawEnergy_nonneg _))
    (fun g => mean_le_const (fun η => (rawIterate_energy_le (d+1) _ t η).trans_eq (rawPermute_energy v g)))
  have hu := raw_uniform_sweep (d+1) t ht v hw hz hf hs
  nlinarith

end Thorp.Conditional

end

end OAI
