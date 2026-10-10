import OAI.NumberTheory.Ostmann.QuadraticSievePoissonLattice

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory
open scoped SchwartzMap FourierTransform Real

noncomputable def dilatedSchwartz (t : ℝ) (ht : t ≠ 0) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (Units.mk0 t ht) : ℝ ≃L[ℝ] ℝ) f

@[simp] theorem dilatedSchwartz_apply (t : ℝ) (ht : t ≠ 0) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    dilatedSchwartz t ht f x = f (t * x) := rfl

theorem fourier_comp_dilation (f : ℝ → ℂ) (t : ℝ) (ht : t ≠ 0) (w : ℝ) :
    𝓕 (fun x => f (t * x)) w = |t⁻¹| • 𝓕 f (w / t) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  calc
    (∫ x : ℝ, 𝐞 (-(x * w)) • f (t * x)) =
        ∫ x : ℝ, 𝐞 (-((t * x) * (w / t))) • f (t * x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      congr 2
      field_simp
    _ = _ := Measure.integral_comp_mul_left
      (fun x : ℝ => 𝐞 (-(x * (w / t))) • f x) t

theorem fourier_dilatedSchwartz (t : ℝ) (ht : t ≠ 0) (f : 𝓢(ℝ, ℂ)) (w : ℝ) :
    𝓕 (dilatedSchwartz t ht f) w = |t⁻¹| • 𝓕 f (w / t) :=
  fourier_comp_dilation f t ht w

theorem periodic_weighted_poisson_scaled (q : ℕ) [NeZero q] (M : ℝ) (hM : 0 < M)
    (c : Fin q → ℂ) (f : 𝓢(ℝ, ℂ)) :
    (∑' m : ℤ, c ((Int.divModEquiv q m).2) * f ((m : ℝ) / M)) =
      ∑' h : ℤ, ((M / q : ℝ) : ℂ) *
        (∑ a : Fin q, c a * fourier h (((a.val : ℝ) / q : ℝ) : UnitAddCircle)) *
        𝓕 f ((h : ℝ) * M / q) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (Nat.pos_of_neZero q)
  let t : ℝ := (q : ℝ) / M
  have ht : 0 < t := div_pos hq hM
  let g := dilatedSchwartz t ht.ne' f
  have hin (m : ℤ) : g ((m : ℝ) / q) = f ((m : ℝ) / M) := by
    rw [dilatedSchwartz_apply]
    congr 1
    dsimp [t]
    field_simp
  have hfreq (h : ℤ) : 𝓕 g (h : ℝ) = ((M / q : ℝ) : ℂ) * 𝓕 f ((h : ℝ) * M / q) := by
    rw [fourier_dilatedSchwartz, abs_of_pos (inv_pos.mpr ht)]
    have hi : t⁻¹ = M / q := by dsimp [t]; rw [inv_div]
    have hw : (h : ℝ) / t = (h : ℝ) * M / q := by dsimp [t]; field_simp
    rw [hi, hw, Complex.real_smul]
  calc
    _ = ∑' m : ℤ, c ((Int.divModEquiv q m).2) * g ((m : ℝ) / q) := by
      apply tsum_congr
      intro m
      rw [hin]
    _ = ∑' h : ℤ, (∑ a : Fin q,
        c a * fourier h (((a.val : ℝ) / q : ℝ) : UnitAddCircle)) * 𝓕 g (h : ℝ) :=
      periodic_weighted_poisson q c g
    _ = _ := by
      apply tsum_congr
      intro h
      rw [hfreq]
      ring

end Ostmann.QuadraticSieve

end OAI
