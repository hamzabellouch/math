import OAI.Probability.ThorpShuffle.FiniteExpectation

namespace OAI

universe uΩ

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

theorem scatterPosition_eq_snoc (d : ℕ) (b : Bool) (x : Position d) :
    scatterPosition d (b, x) = Fin.snoc x b := by
  rw [Fin.snoc_eq_cons_rotate]
  ext i
  simp only [scatterPosition, splitPosition, Equiv.trans_apply, Equiv.symm_symm,
    Fin.consEquiv_apply, rotate, Equiv.piCongrLeft_apply]
  simp

theorem character_snoc (d : ℕ) (h b : Bool) (a x : Position d) :
    character (Fin.snoc a h) (Fin.snoc x b) =
      character a x * (if h then sign b else 1) := by
  simp [character, Fin.prod_univ_castSucc]

theorem coefficient_physicalFlow_even (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (c : Coins (d + 1)) (a : Position d) :
    coefficient (physicalFlow d B w c) (Fin.snoc a false) =
      coefficient w (Fin.cons false a) := by
  unfold coefficient
  rw [← Equiv.sum_comp (scatterPosition d)
    (fun x => physicalFlow d B w c x * character (Fin.snoc a false) x)]
  rw [← Equiv.sum_comp (splitPosition d).symm
    (fun x => w x * character (Fin.cons false a) x)]
  simp only [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  simp only [physicalFlow_scatter]
  simp only [scatterPosition_eq_snoc, character_snoc,
    Bool.false_eq_true, ↓reduceIte, mul_one]
  change flow _ _ c (true, x) * character a x +
    flow _ _ c (false, x) * character a x =
    w (Fin.cons true x) * character (Fin.cons false a) (Fin.cons true x) +
    w (Fin.cons false x) * character (Fin.cons false a) (Fin.cons false x)
  rw [character_cons, character_cons]
  simp only [Bool.false_eq_true, ↓reduceIte, one_mul]
  rw [← add_mul, ← add_mul]
  congr 1
  simpa only [flow, Bool.false_eq_true, ↓reduceIte, add_comm, Function.comp_apply,
    splitPosition, Equiv.symm_symm, Fin.consEquiv, Equiv.coe_fn_mk] using
    pairUpdate_sum (B (Fin.cons false x)) (B (Fin.cons true x))
      (w (Fin.cons false x)) (w (Fin.cons true x)) (c x)

theorem coefficient_physicalFlow_odd (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) (c : Coins (d + 1)) (a : Position d) :
    coefficient (physicalFlow d B w c) (Fin.snoc a true) =
      oddCoefficient (character a) (flow (B ∘ (splitPosition d).symm)
        (w ∘ (splitPosition d).symm) c) := by
  unfold coefficient
  rw [← Equiv.sum_comp (scatterPosition d)
    (fun x => physicalFlow d B w c x * character (Fin.snoc a true) x)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  rw [← Finset.sum_add_distrib]
  unfold oddCoefficient
  apply Finset.sum_congr rfl
  intro x _
  simp only [physicalFlow_scatter]
  simp only [scatterPosition_eq_snoc, character_snoc,
    ↓reduceIte, sign, Bool.false_eq_true]
  ring

def oneFreeEnergy (d : ℕ) (B : Position (d + 1) → Bool)
    (w : Position (d + 1) → ℝ) : ℝ :=
  ∑ x : Position d,
    ((if B (Fin.cons true x) then 0 else w (Fin.cons false x) ^ 2) +
      (if B (Fin.cons false x) then 0 else w (Fin.cons true x) ^ 2))

theorem mean_coefficient_physicalFlow_odd_sq (d : ℕ)
    (B : Position (d + 1) → Bool) (w : Position (d + 1) → ℝ)
    (hw : ∀ x, B x = false → w x = 0) (a : Position d) :
    mean (fun c : Coins (d + 1) =>
      coefficient (physicalFlow d B w c) (Fin.snoc a true) ^ 2) =
        oneFreeEnergy d B w := by
  simp_rw [coefficient_physicalFlow_odd]
  exact mean_oddCoefficient_sq _ _ _ (fun p => hw ((splitPosition d).symm p))
    (character_sq a)

end Conditional

namespace Conditional

def prefixZero {d : ℕ} (j : ℕ) (a : Position d) : Prop :=
  ∀ i : Fin d, i.val < j → a i = false

instance prefixZeroDecidable {d : ℕ} (j : ℕ) (a : Position d) :
    Decidable (prefixZero j a) := by
  unfold prefixZero
  infer_instance

@[simp] theorem prefixZero_zero {d : ℕ} (a : Position d) : prefixZero 0 a := by
  intro i hi
  omega

theorem prefixZero_full {d : ℕ} (a : Position d) :
    prefixZero d a ↔ a = fun _ => false := by
  constructor
  · intro h
    funext i
    exact h i i.isLt
  · intro h
    subst a
    intro i _
    rfl

theorem prefixZero_cons (j d : ℕ) (h : Bool) (a : Position d) :
    prefixZero (j + 1) (Fin.cons h a) ↔ h = false ∧ prefixZero j a := by
  constructor
  · intro hp
    refine ⟨?_, ?_⟩
    · simpa using hp 0 (by simp)
    · intro i hi
      simpa using hp i.succ (by simpa using hi)
  · rintro ⟨rfl, hp⟩ i
    refine Fin.cases ?_ (fun k => ?_) i
    · intro _; rfl
    · intro hi
      exact hp k (by simpa using hi)

theorem prefixZero_snoc (j d : ℕ) (hj : j ≤ d) (h : Bool) (a : Position d) :
    prefixZero j (Fin.snoc a h) ↔ prefixZero j a := by
  constructor
  · intro hp i hi
    simpa using hp i.castSucc hi
  · intro hp i hi
    have hid : i.val < d := lt_of_lt_of_le hi hj
    rw [Fin.snoc, dite_eq_left hid]
    exact hp _ hi

theorem prefixZero_count (j d : ℕ) (hj : j ≤ d) :
    (∑ a : Position d, if prefixZero j a then (1 : ℝ) else 0) = 2 ^ (d - j) := by
  classical
  induction d generalizing j with
  | zero =>
    have : j = 0 := by omega
    subst j
    simp
  | succ d ih =>
    cases j with
    | zero => simp [Fintype.card_pi, Fintype.card_bool]
    | succ j =>
      rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (d + 1) => Bool))
        (fun a => if prefixZero (j + 1) a then (1 : ℝ) else 0)]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type, Fintype.sum_bool,
        prefixZero_cons]
      simpa using ih j (by omega)

def bandEnergy (d : ℕ) (w : Position d → ℝ) (j : ℕ) : ℝ := by
  classical
  exact ∑ a : Position d, if prefixZero j a then coefficient w a ^ 2 else 0

@[simp] theorem bandEnergy_zero (d : ℕ) (w : Position d → ℝ) :
    bandEnergy d w 0 = (Fintype.card (Position d) : ℝ) * ∑ x, w x ^ 2 := by
  have hp := parseval w
  unfold mean at hp
  have hc : (Fintype.card (Position d) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum : (∑ a, coefficient w a ^ 2) =
      (Fintype.card (Position d) : ℝ) * ∑ x, w x ^ 2 := by
    rw [div_eq_iff hc] at hp
    linarith
  simpa [bandEnergy] using hsum

@[simp] theorem bandEnergy_full (d : ℕ) (w : Position d → ℝ) :
    bandEnergy d w d = (∑ x, w x) ^ 2 := by
  classical
  simp [bandEnergy, prefixZero_full]

theorem bandEnergy_cons (d j : ℕ) (w : Position (d + 1) → ℝ) :
    bandEnergy (d + 1) w (j + 1) =
      ∑ a : Position d, if prefixZero j a then coefficient w (Fin.cons false a) ^ 2 else 0 := by
  classical
  unfold bandEnergy
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (d + 1) => Bool))
    (fun a => if prefixZero (j + 1) a then coefficient w a ^ 2 else 0)]
  simp [Fintype.sum_prod_type, prefixZero_cons, Fin.consEquiv]

theorem mean_indicator {Ω : Type uΩ} [Fintype Ω] (p : Prop) [Decidable p] (f : Ω → ℝ) :
    mean (fun ω => if p then f ω else 0) = if p then mean f else 0 := by
  by_cases hp : p <;> simp [hp, mean_zero]

theorem mean_bandEnergy_physicalFlow (d j : ℕ) (hj : j ≤ d)
    (B : Position (d + 1) → Bool) (w : Position (d + 1) → ℝ)
    (hw : ∀ x, B x = false → w x = 0) :
    mean (fun c : Coins (d + 1) => bandEnergy (d + 1) (physicalFlow d B w c) j) =
      bandEnergy (d + 1) w (j + 1) + 2 ^ (d - j) * oneFreeEnergy d B w := by
  classical
  have hs (c : Coins (d + 1)) :
      bandEnergy (d + 1) (physicalFlow d B w c) j =
        (∑ a : Position d, if prefixZero j a then
          coefficient (physicalFlow d B w c) (Fin.snoc a true) ^ 2 else 0) +
        (∑ a : Position d, if prefixZero j a then
          coefficient w (Fin.cons false a) ^ 2 else 0) := by
    unfold bandEnergy
    rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (d + 1) => Bool))
      (fun a => if prefixZero j a then coefficient (physicalFlow d B w c) a ^ 2 else 0)]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Fin.snocEquiv, Equiv.coe_fn_mk,
      prefixZero_snoc j d hj, coefficient_physicalFlow_even]
  simp_rw [hs]
  rw [mean_add, mean_sum, mean_const, bandEnergy_cons]
  simp_rw [mean_indicator, mean_coefficient_physicalFlow_odd_sq d B w hw]
  have hcount :
      (∑ a : Position d, if prefixZero j a then oneFreeEnergy d B w else 0) =
        2 ^ (d - j) * oneFreeEnergy d B w := by
    rw [← prefixZero_count j d hj, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  rw [hcount, add_comm]

end Conditional

end Thorp

end

end OAI
