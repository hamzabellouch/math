import OAI.Probability.InvariantIsing.Spectral.SpectralPaths

namespace OAI

/-! Algebraic reconstruction of spectral-group symbols and roots, as used
in manuscript Proposition `rot:paths`, from the Ward equations. -/

noncomputable section

open scoped BigOperators

namespace InvariantIsing

variable {ι : Type*} [Fintype ι]

/-- The nonnegative solution of the finite spectral Ward equations is the
projected inverse resolvent. -/
theorem spectral_symbol_reconstruction (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (α : ι → ℝ) (hα : ∀ a, 0 ≤ α a)
    (hward : ∀ a b, ρ b * α a - ρ a * α b =
      (eig a - eig b) * α a * α b) (a : ι) :
    α a = projectedResolvent ρ eig hρ hρsum a (∑ b, α b) := by
  let x := ∑ b, α b
  have hx : 0 ≤ x := Finset.sum_nonneg fun b _ => hα b
  by_cases hxpos : 0 < x
  · have hex : ∃ b, 0 < α b := by
      by_contra! h
      have hz : x = 0 := Finset.sum_eq_zero fun b _ => le_antisymm (h b) (hα b)
      linarith
    obtain ⟨a₀, ha₀⟩ := hex
    have hapos : ∀ b, 0 < α b := by
      intro b
      by_contra! h
      have hz : α b = 0 := le_antisymm h (hα b)
      have hw := hward b a₀
      rw [hz] at hw
      nlinarith [mul_pos (hρ b) ha₀]
    let b := ρ a₀ / α a₀ + eig a₀
    have hcommon : ∀ c, b - eig c = ρ c / α c := by
      intro c
      have hw := hward c a₀
      dsimp [b]
      apply (eq_div_iff (hapos c).ne').mpr
      field_simp [ha₀.ne']
      nlinarith [hw]
    have habove : ∀ c, eig c < b := by
      intro c
      have hp : 0 < b - eig c := by rw [hcommon c]; exact div_pos (hρ c) (hapos c)
      exact sub_pos.mp hp
    have hres : finiteResolvent ρ eig b = x := by
      unfold finiteResolvent
      dsimp [x]
      apply Finset.sum_congr rfl
      intro c _
      rw [hcommon c]
      field_simp [(hρ c).ne', (hapos c).ne']
    have hs := finiteInverse_spec ρ eig hρ hρsum hxpos
    have hb : b = finiteInverse ρ eig hρ hρsum x :=
      finiteResolvent_solution_unique (fun c => (hρ c).le) hρsum habove hs.1 hres hs.2
    change α a = projectedResolvent ρ eig hρ hρsum a x
    simp only [projectedResolvent, ite_eq_left hxpos]
    rw [← hb, hcommon a]
    field_simp [(hρ a).ne', (hapos a).ne']
  · have hxzero : x = 0 := le_antisymm (le_of_not_gt hxpos) hx
    have ha : α a = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hα b)).mp hxzero a (Finset.mem_univ a)
    rw [ha]
    simp only [projectedResolvent, show ¬ 0 < ∑ b, α b from hxpos, ite_false]

 /-- The root Ward equations determine the normalized derivative weights.
 This also includes the zero-symbol endpoint and tied eigenvalues. -/
 theorem spectral_root_reconstruction (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a)
     (hρsum : ∑ a, ρ a = 1) {x : ℝ} (hx : 0 ≤ x) (r : ι → ℝ)
     (hward : ∀ a b, ρ b * r a - ρ a * r b =
       (eig a - eig b) *
         (projectedResolvent ρ eig hρ hρsum a x * r b +
          r a * projectedResolvent ρ eig hρ hρsum b x)) (a : ι) :
     r a = (∑ b, r b) * projectedResolventDerivative ρ eig hρ hρsum a x := by
   by_cases hxpos : 0 < x
   · let B := finiteInverse ρ eig hρ hρsum x
     have hs := finiteInverse_spec ρ eig hρ hρsum hxpos
     have hgap : ∀ b, B - eig b ≠ 0 := fun b => (sub_pos.mpr (hs.1 b)).ne'
     have hM := finiteSecondResolvent_pos (fun b => (hρ b).le) hρsum hs.1
     have hpair : ∀ b, r a * (B - eig a) ^ 2 * (ρ b / (B - eig b) ^ 2) =
         ρ a * r b := by
       intro b
       have hw := hward a b
       simp only [projectedResolvent, ite_eq_left hxpos] at hw
       change ρ b * r a - ρ a * r b =
         (eig a - eig b) * (ρ a / (B - eig a) * r b +
           r a * (ρ b / (B - eig b))) at hw
       field_simp [hgap a, hgap b] at hw ⊢
       nlinarith [hw]
     have hsum := congrArg (fun f : ι → ℝ => ∑ b, f b) (funext hpair)
     simp only [← Finset.mul_sum] at hsum
     change r a * (B - eig a) ^ 2 * finiteSecondResolvent ρ eig B =
       ρ a * ∑ b, r b at hsum
     simp only [projectedResolventDerivative, ite_eq_left hxpos]
     change r a = (∑ b, r b) * (ρ a /
       (finiteSecondResolvent ρ eig B * (B - eig a) ^ 2))
     rw [← mul_div_assoc]
     apply (eq_div_iff (mul_ne_zero hM.ne' (pow_ne_zero 2 (hgap a)))).mpr
     nlinarith [hsum]
   · have hxzero : x = 0 := le_antisymm (le_of_not_gt hxpos) hx
     subst x
     have hpair : ∀ b, ρ b * r a = ρ a * r b := by
       intro b
       have hw := hward a b
       simp only [projectedResolvent, lt_self_iff_false, ite_false, zero_mul,
         mul_zero, add_zero] at hw
       linarith
     have hsum := congrArg (fun f : ι → ℝ => ∑ b, f b) (funext hpair)
     simp only [← Finset.sum_mul, ← Finset.mul_sum, hρsum, one_mul] at hsum
     simpa only [projectedResolventDerivative, lt_self_iff_false, ite_false, mul_comm] using hsum

end InvariantIsing

end

end OAI
