import OAI.NumberTheory.CubicMoment.Transform.MetaplecticTransformBounds

namespace OAI

/-! Exact far-left metaplectic Gamma growth from the finite recurrence.
Choosing Re s = 1/2-m gives the sharp height exponent 4m = 2+4A,
A=m-1/2. No additional Stirling or completed-height input is needed. -/
noncomputable section
namespace CubicFirstMoment

private lemma metaplectic_ascPochhammer_norm (n : ℕ) (z : ℂ) :
    ‖(ascPochhammer ℂ n).eval z‖ ≤ (‖z‖+(n:ℝ))^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval,norm_mul]
    have hn : ‖z+(n:ℂ)‖ ≤ ‖z‖+(n:ℝ) := by simpa using norm_add_le z (n:ℂ)
    calc
      _ ≤ (‖z‖+(n:ℝ))^n*(‖z‖+(n:ℝ)) :=
        mul_le_mul ih hn (_root_.norm_nonneg _) (by positivity)
      _ = (‖z‖+(n:ℝ))^(n+1) := (pow_succ _ _).symm
      _ ≤ (‖z‖+((n+1:ℕ):ℝ))^(n+1) := by
        apply pow_le_pow_left₀ (by positivity)
        push_cast
        linarith

/-- A symmetric Gamma ratio for any fixed real shift, retaining the
zero values at the totalized Gamma poles. -/
lemma metaplectic_symmetric_gamma_ratio (k : ℝ) (m : ℕ) (t : ℝ) :
    ‖Complex.Gamma ((1/2:ℂ)+(m:ℂ)+(k:ℂ)-(t:ℂ)*Complex.I) /
      Complex.Gamma ((1/2:ℂ)-(m:ℂ)+(k:ℂ)+(t:ℂ)*Complex.I)‖ ≤
      (|k|+3*(m:ℝ)+1)^(2*m)*(1+|t|)^(2*m) := by
  let z : ℂ := (1/2:ℂ)-(m:ℂ)+(k:ℂ)+(t:ℂ)*Complex.I
  by_cases hG : Complex.Gamma z = 0
  · change ‖_ / Complex.Gamma z‖ ≤ _
    rw [hG,div_zero,norm_zero]
    positivity
  have hreg : ∀ n : ℕ, z ≠ -(n:ℂ) := by
    intro n hn
    apply hG
    rw [hn,Complex.Gamma_neg_nat_eq_zero]
  have he : ((1/2:ℂ)+(m:ℂ)+(k:ℂ)-(t:ℂ)*Complex.I) =
      starRingEnd ℂ (z+(2*m:ℕ)) := by
    dsimp [z]
    simp only [map_add,map_sub,map_mul,Complex.conj_ofReal,Complex.conj_I,
      map_natCast,map_div₀,map_one,map_ofNat]
    push_cast
    ring
  have hq := Complex.Gamma_add_nat_div_Gamma_eq (n := 2*m) z hreg
  have hn : ‖z‖ ≤ |k|+(m:ℝ)+1+|t| := by
    calc
      _ ≤ ‖(1/2:ℂ)-(m:ℂ)+(k:ℂ)‖+‖(t:ℂ)*Complex.I‖ := norm_add_le _ _
      _ ≤ ‖(1/2:ℂ)-(m:ℂ)‖+‖(k:ℂ)‖+‖(t:ℂ)*Complex.I‖ := by
        gcongr
        exact norm_add_le _ _
      _ ≤ ‖(1/2:ℂ)‖+‖(m:ℂ)‖+‖(k:ℂ)‖+‖(t:ℂ)*Complex.I‖ := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ _ := by simp; linarith
  calc
    _ = ‖Complex.Gamma (z+(2*m:ℕ))/Complex.Gamma z‖ := by
      rw [he,Complex.Gamma_conj,norm_div,norm_div,Complex.norm_conj]
    _ = ‖(ascPochhammer ℂ (2*m)).eval z‖ := congrArg (fun w : ℂ => ‖w‖) hq
    _ ≤ (‖z‖+((2*m:ℕ):ℝ))^(2*m) := metaplectic_ascPochhammer_norm _ _
    _ ≤ ((|k|+3*(m:ℝ)+1)*(1+|t|))^(2*m) := by
      apply pow_le_pow_left₀ (by positivity)
      push_cast
      nlinarith [abs_nonneg k,abs_nonneg t,show (0:ℝ) ≤ m by positivity]
    _ = _ := mul_pow _ _ _

lemma metaplecticGamma_symmetric_factor (ℓ : ℤ) (m : ℕ) (t : ℝ) :
    metaplecticGammaQuotient ℓ ((1/2:ℂ)-(m:ℂ)+(t:ℂ)*Complex.I) =
      (Complex.Gamma ((1/2:ℂ)+(m:ℂ)+((metaplecticAngularShift ℓ-1/6:ℝ):ℂ)-(t:ℂ)*Complex.I) /
       Complex.Gamma ((1/2:ℂ)-(m:ℂ)+((metaplecticAngularShift ℓ-1/6:ℝ):ℂ)+(t:ℂ)*Complex.I)) *
      (Complex.Gamma ((1/2:ℂ)+(m:ℂ)+((metaplecticAngularShift ℓ+1/6:ℝ):ℂ)-(t:ℂ)*Complex.I) /
       Complex.Gamma ((1/2:ℂ)-(m:ℂ)+((metaplecticAngularShift ℓ+1/6:ℝ):ℂ)+(t:ℂ)*Complex.I)) := by
  have hk : (metaplecticAngularShift ℓ:ℂ) = (|ℓ|:ℤ)/2 := by
    simp only [metaplecticAngularShift,Complex.ofReal_div,Complex.ofReal_intCast,Complex.ofReal_ofNat]
  unfold metaplecticGammaQuotient
  have h1 : 5/6+(|ℓ|:ℤ)/2-((1/2:ℂ)-(m:ℂ)+(t:ℂ)*Complex.I) =
      (1/2:ℂ)+(m:ℂ)+((metaplecticAngularShift ℓ-1/6:ℝ):ℂ)-(t:ℂ)*Complex.I := by
    push_cast
    rw [hk]
    ring
  have h2 : 7/6+(|ℓ|:ℤ)/2-((1/2:ℂ)-(m:ℂ)+(t:ℂ)*Complex.I) =
      (1/2:ℂ)+(m:ℂ)+((metaplecticAngularShift ℓ+1/6:ℝ):ℂ)-(t:ℂ)*Complex.I := by
    push_cast
    rw [hk]
    ring
  have h3 : (1/2:ℂ)-(m:ℂ)+(t:ℂ)*Complex.I+(|ℓ|:ℤ)/2-1/6 =
      (1/2:ℂ)-(m:ℂ)+((metaplecticAngularShift ℓ-1/6:ℝ):ℂ)+(t:ℂ)*Complex.I := by
    push_cast
    rw [hk]
    ring
  have h4 : (1/2:ℂ)-(m:ℂ)+(t:ℂ)*Complex.I+(|ℓ|:ℤ)/2+1/6 =
      (1/2:ℂ)-(m:ℂ)+((metaplecticAngularShift ℓ+1/6:ℝ):ℂ)+(t:ℂ)*Complex.I := by
    push_cast
    rw [hk]
    ring
  rw [h1,h2,h3,h4]
  ring

/-- Sharp exponent on the far-left half-integral lines, sufficient for
arbitrary-power angular dual truncation. Constants depend only on ℓ,m. -/
theorem metaplecticGamma_half_integer_bound (ℓ : ℤ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖metaplecticGammaQuotient ℓ ((1/2:ℂ)-(m:ℂ)+(t:ℂ)*Complex.I)‖ ≤
        C*(1+|t|)^(4*m) := by
  let k := metaplecticAngularShift ℓ
  let A := (|k-1/6|+3*(m:ℝ)+1)^(2*m)
  let B := (|k+1/6|+3*(m:ℝ)+1)^(2*m)
  have hA : 0 < A := pow_pos (by positivity) _
  have hB : 0 < B := pow_pos (by positivity) _
  refine ⟨A*B,mul_pos hA hB,?_⟩
  intro t
  rw [metaplecticGamma_symmetric_factor,norm_mul]
  have hminus := metaplectic_symmetric_gamma_ratio (k-1/6) m t
  have hplus := metaplectic_symmetric_gamma_ratio (k+1/6) m t
  calc
    _ ≤ (A*(1+|t|)^(2*m))*(B*(1+|t|)^(2*m)) :=
      mul_le_mul hminus hplus (_root_.norm_nonneg _) (by positivity)
    _ = _ := by
      rw [show 4*m = 2*m+2*m by omega,pow_add]
      ring

end CubicFirstMoment

end

end OAI
