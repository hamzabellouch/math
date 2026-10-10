import OAI.NumberTheory.JointDickman.Arithmetic.PrimeSiteLocalLaw

namespace OAI

/-! # The actual logarithmic and residue cells, with partial output -/

namespace JointDickman

open Finset

open Classical in
noncomputable def logResidueCell {D : Type*} (B q : ℕ) (lower upper : D → ℝ)
    (n : ℕ) : Option (D × (ZMod q)ˣ) :=
  if hn : n.Coprime q then
    if hi : ∃ d, Real.log n / B ∈ Set.Ioc (lower d) (upper d) then
      some (hi.choose, ZMod.unitOfCoprime n hn)
    else none
  else none

open Classical in
theorem logResidueCell_eq_some {D : Type*} (B q : ℕ) (lower upper : D → ℝ)
    (hdisjoint : ∀ d e s, s ∈ Set.Ioc (lower d) (upper d) →
      s ∈ Set.Ioc (lower e) (upper e) → d = e)
    (n : ℕ) (d : D) (r : (ZMod q)ˣ) :
    logResidueCell B q lower upper n = some (d, r) ↔
      Real.log n / B ∈ Set.Ioc (lower d) (upper d) ∧ (n : ZMod q) = r := by
  unfold logResidueCell
  by_cases hn : n.Coprime q
  · rw [dite_eq_left hn]
    by_cases hi : ∃ e, Real.log n / B ∈ Set.Ioc (lower e) (upper e)
    · rw [dite_eq_left hi, Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨hd, hr⟩
        subst d
        exact ⟨hi.choose_spec, by rw [← hr]; rfl⟩
      · rintro ⟨hd, hr⟩
        exact ⟨hdisjoint hi.choose d _ hi.choose_spec hd, Units.ext hr⟩
    · rw [dite_eq_right hi]
      simp only [reduceCtorEq, false_iff, not_and]
      exact fun hd => False.elim (hi ⟨d, hd⟩)
  · rw [dite_eq_right hn]
    simp only [reduceCtorEq, false_iff, not_and]
    intro _ hr
    have hu : IsUnit (n : ZMod q) := hr ▸ r.isUnit
    exact hn ((ZMod.isUnit_iff_coprime n q).mp hu)

/-- Multiplication by the common product translates the log cell and
permutes the unit residue. The high-exclusive cutoff changes only the
lower endpoint. -/
theorem high_product_cell_iff {B c n q : ℕ} (hc : 0 < c) (hn : 0 < n)
    (u r : (ZMod q)ˣ) (hu : (c : ZMod q) = u) (a b θ : ℝ) :
    (θ < Real.log n / B ∧
      Real.log (c * n : ℕ) / B ∈ Set.Ioc a b ∧ ((c * n : ℕ) : ZMod q) = (r : ZMod q)) ↔
    (Real.log n / B ∈ Set.Ioc (max θ (a - Real.log c / B)) (b - Real.log c / B) ∧
      (n : ZMod q) = (u⁻¹ * r : (ZMod q)ˣ)) := by
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : Real.log (c * n : ℕ) / B = Real.log c / B + Real.log n / B := by
    rw [Nat.cast_mul, Real.log_mul hc0.ne' hn0.ne', add_div]
  have hmod : ((c * n : ℕ) : ZMod q) = r ↔ (n : ZMod q) = (u⁻¹ * r : (ZMod q)ˣ) := by
    rw [Nat.cast_mul, hu]
    constructor
    · intro h
      have h' := congrArg (fun t : ZMod q => (u⁻¹ : (ZMod q)ˣ) * t) h
      simpa [mul_assoc] using h'
    · intro h
      rw [h]
      simp [← Units.val_mul]
  rw [hlog, hmod]
  simp only [Set.mem_Ioc, max_lt_iff]
  constructor
  · rintro ⟨hθ, hab, hr⟩
    exact ⟨⟨⟨hθ, by linarith [hab.1]⟩, by linarith [hab.2]⟩, hr⟩
  · rintro ⟨⟨⟨hθ, ha⟩, hb⟩, hr⟩
    exact ⟨hθ, ⟨by linarith, by linarith⟩, hr⟩

/-- The uncut product cell is a translated log interval with a permuted residue. -/
theorem product_cell_iff {B c n q : ℕ} (hc : 0 < c) (hn : 0 < n)
    (u r : (ZMod q)ˣ) (hu : (c : ZMod q) = u) (a b : ℝ) :
    (Real.log (c * n : ℕ) / B ∈ Set.Ioc a b ∧ ((c * n : ℕ) : ZMod q) = (r : ZMod q)) ↔
    (Real.log n / B ∈ Set.Ioc (a - Real.log c / B) (b - Real.log c / B) ∧
      (n : ZMod q) = (u⁻¹ * r : (ZMod q)ˣ)) := by
  let θ := min (a - Real.log c / B) 0 - 1
  have hθ : θ < Real.log n / B := by
    have ht : 0 ≤ Real.log n / (B : ℝ) :=
      div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg B)
    dsimp [θ]
    linarith [min_le_right (a - Real.log c / B) 0]
  have hm : max θ (a - Real.log c / B) = a - Real.log c / B := by
    apply max_eq_right
    dsimp [θ]
    linarith [min_le_left (a - Real.log c / B) 0]
  have h := high_product_cell_iff (B := B) hc hn u r hu a b θ
  simpa only [hθ, true_and, hm] using h

end JointDickman

end OAI
