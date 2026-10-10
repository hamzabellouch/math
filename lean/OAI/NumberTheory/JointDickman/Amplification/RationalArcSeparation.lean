import OAI.NumberTheory.JointDickman.Amplification.MinorArcApproximation

namespace OAI

/-! # Separation and uniqueness of the rational major arcs -/

namespace JointDickman
open Filter
open scoped Topology

theorem rational_separation {r s : ℚ} (hrs : r ≠ s) :
    1/((r.den : ℝ)*s.den) ≤ |(r : ℝ)-s| := by
  have hr : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hs : (0 : ℝ) < s.den := by exact_mod_cast s.pos
  have hd : (0 : ℝ) < (r.den : ℝ)*s.den := mul_pos hr hs
  have hrs' : (r : ℝ) ≠ s := by exact_mod_cast hrs
  let z : ℤ := r.num*s.den-s.num*r.den
  have he : (z : ℝ) = ((r : ℝ)-s)*((r.den : ℝ)*s.den) := by
    dsimp [z]
    push_cast
    rw [Rat.cast_def,Rat.cast_def]
    field_simp
  have hz : z ≠ 0 := by
    intro h
    have : ((r : ℝ)-s)*((r.den : ℝ)*s.den) = 0 := by rw [← he,h]; simp
    exact (mul_ne_zero (sub_ne_zero.mpr hrs') hd.ne') this
  have h1 : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast (Int.one_le_abs hz)
  apply (div_le_iff₀ hd).mpr
  calc
    1 ≤ |(z : ℝ)| := h1
    _ = |(r : ℝ)-s| *((r.den : ℝ)*s.den) := by rw [he,abs_mul,abs_of_pos hd]

theorem rationalArc_unique {θ Q δ : ℝ} (_hQ : 0 < Q) (hδ : 2*δ < 1/Q^2)
    {r s : ℚ} (hr : (r.den : ℝ) ≤ Q) (hs : (s.den : ℝ) ≤ Q)
    (hθr : |θ-(r : ℝ)| ≤ δ) (hθs : |θ-(s : ℝ)| ≤ δ) : r = s := by
  by_contra hne
  have hr0 : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hs0 : (0 : ℝ) < s.den := by exact_mod_cast s.pos
  have hprod : (r.den : ℝ)*s.den ≤ Q^2 := by nlinarith
  have hlow : 1/Q^2 ≤ |(r : ℝ)-s| :=
    (one_div_le_one_div_of_le (mul_pos hr0 hs0) hprod).trans (rational_separation hne)
  have hupp : |(r : ℝ)-s| ≤ 2*δ := by
    calc
      _ ≤ |(r : ℝ)-θ|+|θ-(s : ℝ)| := abs_sub_le _ _ _
      _ ≤ δ+δ := add_le_add (by simpa only [abs_sub_comm] using hθr) hθs
      _ = _ := by ring
  linarith

theorem majorArc_width_separation :
    ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X → (9/10 : ℝ)*B ≤ Real.log X →
      2*((B : ℝ)^13/X) < 1/((B : ℝ)^12)^2 := by
  have hl := (isLittleO_pow_exp_pos_mul_atTop 37
    (by norm_num : (0 : ℝ) < 9/10)).def (by norm_num : (0 : ℝ) < 1/3)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hl,eventually_ge_atTop 1]
    with B hsmall hB
  intro X hX hlog
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hexp : Real.exp ((9/10 : ℝ)*B) ≤ X := by
    simpa only [Real.exp_log hX] using Real.exp_le_exp.mpr hlog
  have hsmall' : (B : ℝ)^37 ≤ (1/3 : ℝ)*Real.exp ((9/10 : ℝ)*B) := by
    simpa only [Real.norm_eq_abs,abs_of_pos (pow_pos hB0 _),
      abs_of_pos (Real.exp_pos _)] using hsmall
  have hlarge : 2*(B : ℝ)^37 < X := by
    have he := Real.exp_pos ((9/10 : ℝ)*B)
    linarith
  rw [← mul_div_assoc]
  apply (div_lt_div_iff₀ hX (sq_pos_of_pos (pow_pos hB0 12))).mpr
  convert hlarge using 1 <;> ring

/-- At the manuscript's exponential scale a point belongs to at most one
reduced rational arc, before passing to the lifted endpoint coordinate. -/
theorem majorArc_rational_unique :
    ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X → (9/10 : ℝ)*B ≤ Real.log X →
      ∀ (θ : ℝ) (r s : ℚ), (r.den : ℝ) ≤ (B : ℝ)^12 →
      (s.den : ℝ) ≤ (B : ℝ)^12 → |θ-(r : ℝ)| ≤ (B : ℝ)^13/X →
      |θ-(s : ℝ)| ≤ (B : ℝ)^13/X → r = s := by
  filter_upwards [majorArc_width_separation,eventually_ge_atTop 1] with B hsep hB
  intro X hX hlog θ r s hr hs hθr hθs
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  exact rationalArc_unique (pow_pos hB0 12) (hsep X hX hlog) hr hs hθr hθs

end JointDickman

end OAI
