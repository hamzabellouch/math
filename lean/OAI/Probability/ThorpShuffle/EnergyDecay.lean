import OAI.Probability.ThorpShuffle.NoiseEnergy

namespace OAI

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

theorem mean_rawFree_sweep (d : ℕ) (v : RawState (d + 1)) (x : Position (d + 1)) :
    mean (fun ω : History (d + 1) (d + 1) =>
      if (rawIterate d v (d + 1) ω).free x then (1 : ℝ) else 0) =
        (freeCount v.free : ℝ) / Fintype.card (Position (d + 1)) := by
  simp only [rawIterate_free]
  exact mean_free_after_sweep d v.free x

theorem rawIterate_half_weight (d : ℕ) (v : RawState (d + 2)) (h : Bool)
    (ω : History (d + 2) (d + 1)) (x : Position (d + 1)) :
    (rawIterate (d + 1) v (d + 1) ω).weight (Fin.cons h x) =
      (rawIterate d (halfRaw (d + 1) (Fin.last (d + 1)) h v) (d + 1)
        (halfHistory d (d + 1) h ω)).weight x := by
  have hz := congrArg (fun u : RawState (d + 1) => u.weight x)
    (rawIterate_half d (d + 1) le_rfl h v ω)
  simpa only [halfMarker_end, halfRaw, insertBit_zero] using hz

theorem rawIterate_half_free (d : ℕ) (v : RawState (d + 2)) (h : Bool)
    (ω : History (d + 2) (d + 1)) (x : Position (d + 1)) :
    (rawIterate (d + 1) v (d + 1) ω).free (Fin.cons h x) =
      (rawIterate d (halfRaw (d + 1) (Fin.last (d + 1)) h v) (d + 1)
        (halfHistory d (d + 1) h ω)).free x := by
  have hz := congrArg (fun u : RawState (d + 1) => u.free x)
    (rawIterate_half d (d + 1) le_rfl h v ω)
  simpa only [halfMarker_end, halfRaw, insertBit_zero] using hz

theorem mean_half_single (d t : ℕ) (h : Bool) (f : History (d + 1) t → ℝ) :
    mean (fun ω : History (d + 2) t => f (halfHistory d t h ω)) = mean f := by
  simpa only [mean_const, mul_one] using
    mean_opposite_half_product d t h f (fun _ => (1 : ℝ))

theorem mean_half_factorization (d : ℕ) (v : RawState (d + 2)) (h : Bool)
    (x : Position (d + 1)) :
    mean (fun ω : History (d + 2) (d + 1) =>
      (rawIterate (d + 1) v (d + 1) ω).weight (Fin.cons h x) ^ 2 *
        (if (rawIterate (d + 1) v (d + 1) ω).free (Fin.cons (!h) x) then (1 : ℝ) else 0)) =
      ((freeCount (halfRaw (d + 1) (Fin.last (d + 1)) (!h) v).free : ℝ) /
        Fintype.card (Position (d + 1))) *
      mean (fun ω : History (d + 2) (d + 1) =>
        (rawIterate (d + 1) v (d + 1) ω).weight (Fin.cons h x) ^ 2) := by
  simp_rw [rawIterate_half_weight, rawIterate_half_free]
  rw [mean_opposite_half_product d (d + 1) h
    (fun ω => (rawIterate d (halfRaw (d + 1) (Fin.last (d + 1)) h v) (d + 1) ω).weight x ^ 2)
    (fun ω => if (rawIterate d (halfRaw (d + 1) (Fin.last (d + 1)) (!h) v)
      (d + 1) ω).free x then (1 : ℝ) else 0)]
  rw [mean_rawFree_sweep, mean_half_single d (d + 1) h
    (fun ω => (rawIterate d (halfRaw (d + 1) (Fin.last (d + 1)) h v) (d + 1) ω).weight x ^ 2),
    mul_comm]

 def rawEnergy {d : ℕ} (v : RawState d) : ℝ := ∑ x, v.weight x ^ 2
 def halfEnergy (d : ℕ) (v : RawState (d + 1)) (h : Bool) : ℝ :=
   ∑ x : Position d, v.weight (Fin.cons h x) ^ 2
 def partnerEnergy (d : ℕ) (v : RawState (d + 1)) (h : Bool) : ℝ :=
   ∑ x : Position d, v.weight (Fin.cons h x) ^ 2 *
     (if v.free (Fin.cons (!h) x) then 1 else 0)
 def startHalfDensity (d : ℕ) (v : RawState (d + 1)) (h : Bool) : ℝ :=
   (freeCount (halfRaw d (Fin.last d) h v).free : ℝ) / Fintype.card (Position d)

 theorem halfEnergy_nonneg (d : ℕ) (v : RawState (d + 1)) (h : Bool) :
    0 ≤ halfEnergy d v h := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

 theorem rawEnergy_halves (d : ℕ) (v : RawState (d + 1)) :
    rawEnergy v = halfEnergy d v false + halfEnergy d v true := by
  unfold rawEnergy halfEnergy
  have he := Equiv.sum_comp (splitPosition d).symm (fun x => v.weight x ^ 2)
  rw [← he, Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
  rfl

 theorem oneFreeEnergy_partner (d : ℕ) (v : RawState (d + 1)) :
    oneFreeEnergy d v.free v.weight + partnerEnergy d v false + partnerEnergy d v true =
      rawEnergy v := by
  rw [rawEnergy_halves]
  unfold oneFreeEnergy partnerEnergy halfEnergy
  simp only [Bool.not_false, Bool.not_true, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  cases v.free (Fin.cons false x) <;> cases v.free (Fin.cons true x) <;> simp [add_comm]

 theorem mean_half_energy_factorization (d : ℕ) (v : RawState (d + 2)) (h : Bool) :
    mean (fun ω : History (d + 2) (d + 1) =>
      partnerEnergy (d + 1) (rawIterate (d + 1) v (d + 1) ω) h) =
      startHalfDensity (d + 1) v (!h) *
        mean (fun ω : History (d + 2) (d + 1) =>
          halfEnergy (d + 1) (rawIterate (d + 1) v (d + 1) ω) h) := by
  unfold partnerEnergy halfEnergy startHalfDensity
  rw [mean_sum, mean_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  exact mean_half_factorization d v h x

theorem noise_bound_balanced_halves (d : ℕ) (v : RawState (d + 2))
    (β : ℝ) (hb : ∀ h, β ≤ startHalfDensity (d + 1) v h) :
    mean (fun ω : History (d + 2) (d + 1) =>
      oneFreeEnergy (d + 1) (rawIterate (d + 1) v (d + 1) ω).free
        (rawIterate (d + 1) v (d + 1) ω).weight) ≤
      (1 - β) * mean (fun ω : History (d + 2) (d + 1) =>
        rawEnergy (rawIterate (d + 1) v (d + 1) ω)) := by
  have hid := mean_congr (fun ω : History (d + 2) (d + 1) =>
    oneFreeEnergy_partner (d + 1) (rawIterate (d + 1) v (d + 1) ω))
  rw [mean_add, mean_add, mean_half_energy_factorization,
    mean_half_energy_factorization] at hid
  have he := mean_congr (fun ω : History (d + 2) (d + 1) =>
    rawEnergy_halves (d + 1) (rawIterate (d + 1) v (d + 1) ω))
  rw [mean_add] at he
  have hfalse := mul_le_mul_of_nonneg_right (hb true)
    (mean_nonneg (fun ω : History (d + 2) (d + 1) =>
      halfEnergy_nonneg (d + 1) (rawIterate (d + 1) v (d + 1) ω) false))
  have htrue := mul_le_mul_of_nonneg_right (hb false)
    (mean_nonneg (fun ω : History (d + 2) (d + 1) =>
      halfEnergy_nonneg (d + 1) (rawIterate (d + 1) v (d + 1) ω) true))
  simp only [Bool.not_false, Bool.not_true] at hid
  rw [he] at hid ⊢
  nlinarith

end Conditional

namespace Conditional

def splitHistory (d s t : ℕ) : History d (s + t) ≃ History d s × History d t where
  toFun ω := (fun i => ω (Fin.castAdd t i), fun i => ω (Fin.natAdd s i))
  invFun p := Fin.append p.1 p.2
  left_inv ω := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · exact Fin.append_left _ _ _
    · exact Fin.append_right _ _ _
  right_inv p := by
    apply Prod.ext <;> funext i
    · exact Fin.append_left _ _ _
    · exact Fin.append_right _ _ _

theorem mean_history_add (d s t : ℕ) (f : History d (s + t) → ℝ) :
    mean f = mean (fun a : History d s =>
      mean (fun b : History d t => f (Fin.append a b))) := by
  have he := mean_equiv (splitHistory d s t).symm f
  rw [mean_prod] at he
  exact he.symm

@[simp] theorem rawIterate_snoc (d t : ℕ) (v : RawState (d + 1))
    (ω : History (d + 1) t) (c : Coins (d + 1)) :
    rawIterate d v (t + 1) (Fin.snoc ω c) = rawNext d (rawIterate d v t ω) c := by
  simp [rawIterate]

@[simp] theorem iterateState_snoc (d t : ℕ) (v : CenteredState (d + 1))
    (ω : History (d + 1) t) (c : Coins (d + 1)) :
    iterateState d v (t + 1) (Fin.snoc ω c) = nextState d (iterateState d v t ω) c := by
  simp [iterateState]

theorem rawIterate_append (d s t : ℕ) (v : RawState (d + 1))
    (a : History (d + 1) s) (b : History (d + 1) t) :
    rawIterate d v (s + t) (Fin.append a b) = rawIterate d (rawIterate d v s a) t b := by
  induction t with
  | zero =>
    have hz : Fin.append a b = a := by funext i; exact Fin.append_left a b i
    rw [hz]; rfl
  | succ t ih =>
    obtain ⟨⟨c, b⟩, rfl⟩ := (Fin.snocEquiv (fun _ : Fin (t + 1) => Coins (d + 1))).surjective b
    erw [Fin.append_snoc, rawIterate_snoc, rawIterate_snoc, ih]

theorem iterateState_append (d s t : ℕ) (v : CenteredState (d + 1))
    (a : History (d + 1) s) (b : History (d + 1) t) :
    iterateState d v (s + t) (Fin.append a b) = iterateState d (iterateState d v s a) t b := by
  induction t with
  | zero =>
    have hz : Fin.append a b = a := by funext i; exact Fin.append_left a b i
    rw [hz]; rfl
  | succ t ih =>
    obtain ⟨⟨c, b⟩, rfl⟩ := (Fin.snocEquiv (fun _ : Fin (t + 1) => Coins (d + 1))).surjective b
    erw [Fin.append_snoc, iterateState_snoc, iterateState_snoc, ih]

theorem expectedEnergy_add (d s t : ℕ) (v : CenteredState (d + 1)) :
    expectedEnergy d v (s + t) = mean (fun a : History (d + 1) s =>
      expectedEnergy d (iterateState d v s a) t) := by
  unfold expectedEnergy
  rw [mean_history_add]
  simp_rw [iterateState_append]

theorem expectedNoise_add (d s t : ℕ) (v : CenteredState (d + 1)) :
    expectedNoise d v (s + t) = mean (fun a : History (d + 1) s =>
      expectedNoise d (iterateState d v s a) t) := by
  unfold expectedNoise
  rw [mean_history_add]
  simp_rw [iterateState_append]

end Conditional

end Thorp

end

end OAI
