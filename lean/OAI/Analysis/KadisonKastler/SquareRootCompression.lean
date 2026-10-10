import OAI.Analysis.KadisonKastler.FreeProjectionMoments
import OAI.Analysis.KadisonKastler.TraceNormPerturbation

namespace OAI

/-! # Square roots in projection corners and the compression error -/

namespace KadisonKastler

noncomputable section

universe u

variable {B : Type u} [CStarAlgebra B]

local instance : PartialOrder B := CStarAlgebra.spectralOrder B
local instance : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

private theorem sqrt_scalar_sub_one_sq_le {t : ℝ} (ht : 0 ≤ t) :
    (Real.sqrt t - 1) ^ 2 ≤ (t - 1) ^ 2 := by
  calc
    (Real.sqrt t - 1) ^ 2 ≤ (Real.sqrt t - 1) ^ 2 * (Real.sqrt t + 1) ^ 2 := by
      have h : (1 : ℝ) ≤ (Real.sqrt t + 1) ^ 2 := by nlinarith [Real.sqrt_nonneg t]
      nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg (Real.sqrt t - 1))]
    _ = (t - 1) ^ 2 := by
      rw [← mul_pow]
      congr 1
      nlinarith [Real.sq_sqrt ht]

/-- A square root has the same two-sided projection support as the
positive element. -/
theorem sqrt_projection_support (s e : B) (hs : 0 ≤ s) (he : IsStarProjection e)
    (hse : s * e = s) :
    CFC.sqrt s * e = CFC.sqrt s ∧ e * CFC.sqrt s = CFC.sqrt s := by
  have hb : star (CFC.sqrt s) = CFC.sqrt s := (CFC.sqrt_nonneg s).isSelfAdjoint.star_eq
  have hs0 : s * (1 - e) = 0 := by rw [mul_sub, mul_one, hse, sub_self]
  have hz : CFC.sqrt s * (1 - e) = 0 := by
    apply (CStarRing.star_mul_self_eq_zero_iff _).mp
    rw [star_mul, star_sub, star_one, he.isSelfAdjoint.star_eq, hb]
    calc
      (1 - e) * CFC.sqrt s * (CFC.sqrt s * (1 - e)) =
          (1 - e) * (CFC.sqrt s * CFC.sqrt s) * (1 - e) := by noncomm_ring
      _ = 0 := by rw [CFC.sqrt_mul_sqrt_self s hs, mul_assoc, hs0, mul_zero]
  have hright : CFC.sqrt s * e = CFC.sqrt s := by
    rw [mul_sub, mul_one, sub_eq_zero] at hz
    exact hz.symm
  refine ⟨hright, ?_⟩
  simpa only [star_mul, hb, he.isSelfAdjoint.star_eq] using congrArg star hright

/-- The tracial two-norm of a positive square root. -/
theorem traceTwoNorm_sqrt (τ : FaithfulTracialState B) (s : B) (hs : 0 ≤ s) :
    traceTwoNorm τ (CFC.sqrt s) = Real.sqrt ((τ.toLinearMap s).re) := by
  rw [traceTwoNorm, (CFC.sqrt_nonneg s).isSelfAdjoint.star_eq,
    CFC.sqrt_mul_sqrt_self s hs]

/-- The tracial two-norm of a projection. -/
theorem traceTwoNorm_projection (τ : FaithfulTracialState B) (e : B)
    (he : IsStarProjection e) :
    traceTwoNorm τ e = Real.sqrt ((τ.toLinearMap e).re) := by
  rw [traceTwoNorm, he.isSelfAdjoint.star_eq, he.isIdempotentElem.eq]

/-- Taking the positive square root improves the distance to the
identity of the supporting projection corner. -/
theorem traceTwoNorm_sqrt_sub_projection_le (τ : FaithfulTracialState B)
    (s e : B) (hs : 0 ≤ s) (he : IsStarProjection e) (hse : s * e = s) :
    traceTwoNorm τ (CFC.sqrt s - e) ≤ traceTwoNorm τ (s - e) := by
  let b := CFC.sqrt s
  have hb : star b = b := (CFC.sqrt_nonneg s).isSelfAdjoint.star_eq
  have hsstar : star s = s := hs.isSelfAdjoint.star_eq
  obtain ⟨hbe, heb⟩ := sqrt_projection_support s e hs he hse
  change b * e = b at hbe
  change e * b = b at heb
  have hes : e * s = s := by
    simpa only [star_mul, he.isSelfAdjoint.star_eq, hsstar] using congrArg star hse
  have hbs : b = cfc Real.sqrt s := by
    dsimp [b]
    rw [CFC.sqrt_eq_real_sqrt s hs, cfcₙ_eq_cfc]
  have hcfcb : cfc (fun t : ℝ => (Real.sqrt t - 1) ^ 2) s =
      star (b - 1) * (b - 1) := by
    rw [cfc_pow (fun t : ℝ => Real.sqrt t - 1) 2 s,
      cfc_sub Real.sqrt (fun _ : ℝ => 1) s,
      cfc_const_one ℝ s, ← hbs, star_sub, hb, star_one, pow_two]
  have hcfcs : cfc (fun t : ℝ => (t - 1) ^ 2) s = star (s - 1) * (s - 1) := by
    rw [cfc_pow (fun t : ℝ => t - 1) 2 s,
      cfc_sub (fun t : ℝ => t) (fun _ : ℝ => 1) s,
      cfc_id' ℝ s, cfc_const_one ℝ s, star_sub, hsstar, star_one, pow_two]
  have horder : star (b - 1) * (b - 1) ≤ star (s - 1) * (s - 1) := by
    rw [← hcfcb, ← hcfcs]
    apply (cfc_le_iff _ _ s).mpr
    intro t ht
    exact sqrt_scalar_sub_one_sq_le (spectrum_nonneg_of_nonneg hs ht)
  have hdiff : star (s - e) * (s - e) - star (b - e) * (b - e) =
      star (s - 1) * (s - 1) - star (b - 1) * (b - 1) := by
    simp only [star_sub, hsstar, hb, he.isSelfAdjoint.star_eq, star_one,
      sub_mul, mul_sub, hse, hes, hbe, heb, he.isIdempotentElem.eq, mul_one, one_mul]
    abel
  have hnonneg : 0 ≤ star (s - e) * (s - e) - star (b - e) * (b - e) := by
    rw [hdiff]
    exact sub_nonneg.mpr horder
  obtain ⟨z, hz⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hnonneg
  have ht := τ.positive z
  rw [← hz, map_sub, Complex.sub_re] at ht
  have hleft := traceTwoNorm_sq τ (b - e)
  have hright := traceTwoNorm_sq τ (s - e)
  change traceTwoNorm τ (b - e) ≤ traceTwoNorm τ (s - e)
  nlinarith [traceTwoNorm_nonneg τ (b - e), traceTwoNorm_nonneg τ (s - e)]

/-- The actual square-root compression error in the scalar recovery
argument, from the two low-degree free moments. -/
theorem CenteredProjectionMoments.sqrt_compression_sandwich_error
    {τ : FaithfulTracialState B} {p e a : B} {n : ℕ} {η N : ℝ}
    (hn : 0 < n) (hp : IsStarProjection p) (he : IsStarProjection e)
    (hpτ : τ.toLinearMap p = (((n : ℝ)⁻¹ : ℝ) : ℂ))
    (heτ : τ.toLinearMap e = (η : ℂ))
    (h : CenteredProjectionMoments τ p e (n : ℝ)⁻¹ η) (hN : ‖a‖ ≤ N) :
    traceOneNorm τ (CFC.sqrt ((n : ℂ) • (e * p * e)) * a *
        CFC.sqrt ((n : ℂ) • (e * p * e)) - e * a * e) ≤
      2 * N * Real.sqrt ((n : ℝ) - 1) * η * Real.sqrt η := by
  let s : B := (n : ℂ) • (e * p * e)
  have hs : 0 ≤ s := by
    change 0 ≤ (n : ℂ) • (e * p * e)
    have hscale : (n : ℂ) • (e * p * e) = (n : ℝ) • (e * p * e) := by
      simp only [Nat.cast_smul_eq_nsmul]
    rw [hscale]
    exact smul_nonneg (Nat.cast_nonneg n)
      (by simpa only [he.isSelfAdjoint.star_eq] using star_left_conjugate_nonneg hp.nonneg e)
  have hse : s * e = s := by
    simp only [s, smul_mul_assoc, mul_assoc, he.isIdempotentElem.eq]
  have hη : 0 ≤ η := by
    have ht := τ.positive e
    simpa only [he.isSelfAdjoint.star_eq, he.isIdempotentElem.eq, heτ, Complex.ofReal_re] using ht
  have hnR : 0 ≤ (n : ℝ) - 1 := by
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr hn)
    linarith
  have htrace : τ.toLinearMap s = (η : ℂ) := h.trace_scaled_compression hn he hpτ heτ
  have hsqrt : traceTwoNorm τ (CFC.sqrt s) = Real.sqrt η := by
    rw [traceTwoNorm_sqrt τ s hs, htrace, Complex.ofReal_re]
  have heNorm : traceTwoNorm τ e = Real.sqrt η := by
    rw [traceTwoNorm_projection τ e he, heτ, Complex.ofReal_re]
  have hvar : traceTwoNorm τ (s - e) ^ 2 = ((n : ℝ) - 1) * η ^ 2 :=
    h.traceTwoNorm_scaled_compression_sub_sq hn hp he hpτ heτ
  have hsq : (Real.sqrt ((n : ℝ) - 1) * η) ^ 2 = ((n : ℝ) - 1) * η ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hnR]
  have hroot : traceTwoNorm τ (s - e) = Real.sqrt ((n : ℝ) - 1) * η := by
    have hnonneg := mul_nonneg (Real.sqrt_nonneg ((n : ℝ) - 1)) hη
    nlinarith [traceTwoNorm_nonneg τ (s - e)]
  have hdelta : traceTwoNorm τ (CFC.sqrt s - e) ≤ Real.sqrt ((n : ℝ) - 1) * η := by
    exact (traceTwoNorm_sqrt_sub_projection_le τ s e hs he hse).trans_eq hroot
  change traceOneNorm τ (CFC.sqrt s * a * CFC.sqrt s - e * a * e) ≤ _
  calc
    _ ≤ traceTwoNorm τ (CFC.sqrt s - e) * ‖a‖ *
        (traceTwoNorm τ (CFC.sqrt s) + traceTwoNorm τ e) :=
      traceOneNorm_sandwich_sub_le τ (CFC.sqrt s) e a
    _ ≤ (Real.sqrt ((n : ℝ) - 1) * η) * N * (Real.sqrt η + Real.sqrt η) := by
      rw [hsqrt, heNorm]
      gcongr
    _ = _ := by ring

end

end KadisonKastler

end OAI
