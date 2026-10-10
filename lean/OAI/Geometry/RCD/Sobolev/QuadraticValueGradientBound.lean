import OAI.Geometry.RCD.Sobolev.QuadraticLocalEnergy

namespace OAI

/-! # Turning value and Gram errors into a local gradient error -/

open Set MeasureTheory
open scoped NNReal ENNReal BigOperators

noncomputable section
namespace RegularPointCoordinates

private theorem cutoff_error_algebra {c w a b d G δ B T A : ℝ}
    (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) (hδ : 0 ≤ δ)
    (hA : 0 ≤ A) (hG : 0 ≤ G) (hw : |w| ≤ δ) (ha : a ≤ 2 * w + A * G)
    (hb₀ : 0 ≤ b) (hb : b ≤ B) (hd : |d| ≤ T) :
    c * a + 2 * (c * w * b) + 2 * (w * d) ≤
      2 * δ * (1 + B + T) + A * G := by
  have hw' : w ≤ δ := (le_abs_self w).trans hw
  have hcw : c * w ≤ δ := (mul_le_mul_of_nonneg_left hw' hc₀).trans
    (by nlinarith)
  have ha' : c * a ≤ 2 * δ + A * G := by
    have h₁ := mul_le_mul_of_nonneg_left ha hc₀
    have h₂ := mul_le_mul_of_nonneg_right hc₁ (mul_nonneg hA hG)
    nlinarith
  have hb' : c * w * b ≤ δ * B :=
    (mul_le_mul_of_nonneg_right hcw hb₀).trans (mul_le_mul_of_nonneg_left hb hδ)
  have hd' : w * d ≤ δ * T := by
    calc
      _ ≤ |w * d| := le_abs_self _
      _ = |w| * |d| := abs_mul _ _
      _ ≤ δ * T := mul_le_mul hw hd (abs_nonneg _) hδ
  nlinarith

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- The exact distance eikonal identity and the harmonic quadratic model
bound the local gradient error by its value error and the Gram error.
The constants B and T bound the actual trace and cutoff cross gradient. -/
theorem coordinateQuadratic_value_gradient_bound {n : ℕ} {Ω : Set X}
    (hfin : μ Ω ≠ ∞)
    (u : Fin n → SobolevSpace μ hQ) (C D L : ℝ≥0)
    (hu : ∀ j, IsSobolevHarmonicOn μ hQ Ω (u j))
    (hub : ∀ j, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (u j) x| ≤ C)
    (c q : SobolevSpace μ hQ) (χ : X → ℝ)
    (hχ : LipschitzWith L χ) (hcpt : HasCompactSupport χ)
    (hbound : ∀ x, |χ x| ≤ 1) (hnonneg : ∀ x, 0 ≤ χ x)
    (hsupp : tsupport χ ⊆ Ω) (hcrep : SobolevSpace.toLp μ hQ c =ᵐ[μ] χ)
    (hw : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (q - coordinateQuadratic μ hQ u C) x| ≤ D)
    {δ B T : ℝ} (hδ : 0 ≤ δ)
    (hsmall : ∀ᵐ x ∂μ.restrict Ω,
      |SobolevSpace.toLp μ hQ (q - coordinateQuadratic μ hQ u C) x| ≤ δ)
    (heik : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ q q x = 2 * SobolevSpace.toLp μ hQ q x)
    (htrace : ∀ᵐ x ∂μ.restrict Ω, (∑ j, localGamma μ hQ (u j) (u j) x) ≤ B)
    (hcut : ∀ᵐ x ∂μ.restrict Ω,
      |localGamma μ hQ c (coordinateQuadratic μ hQ u C) x| ≤ T) :
    let H := coordinateQuadratic μ hQ u C
    (∫ x in Ω, SobolevSpace.toLp μ hQ c x * localGamma μ hQ (q - H) (q - H) x ∂μ) ≤
      2 * δ * (1 + B + T) * μ.real Ω + (C : ℝ) ^ 2 *
        ∫ x in Ω, ∑ i, ∑ j, |localGamma μ hQ (u j) (u i) x - if j = i then 1 else 0| ∂μ := by
  dsimp only
  let H := coordinateQuadratic μ hQ u C
  let w := q - H
  let G : X → ℝ := fun x => ∑ i, ∑ j,
    |localGamma μ hQ (u j) (u i) x - if j = i then 1 else 0|
  let F : X → ℝ := fun x => SobolevSpace.toLp μ hQ c x *
    (localGamma μ hQ q q x - localGamma μ hQ H H x) +
    2 * (SobolevSpace.toLp μ hQ c x * SobolevSpace.toLp μ hQ w x *
      (∑ j, localGamma μ hQ (u j) (u j) x)) +
    2 * (SobolevSpace.toLp μ hQ w x * localGamma μ hQ c H x)
  have hG : Integrable G (μ.restrict Ω) := by
    apply integrable_finsetSum
    intro i _
    apply integrable_finsetSum
    intro j _
    exact ((localGamma_memL1 μ hQ (u j) (u i)).integrableOn.sub
      (integrableOn_const hfin)).abs
  have hc : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ c x| ≤ (1 : ℝ≥0) := by
    filter_upwards [hcrep] with x hx
    rw [hx]
    exact hbound x
  have hiw : ∀ᵐ x ∂μ,
      |SobolevSpace.toLp μ hQ c x * SobolevSpace.toLp μ hQ w x| ≤ (D : ℝ) := by
    filter_upwards [hc, hw] with x hx hy
    rw [abs_mul]
    simpa only [NNReal.coe_one, one_mul] using mul_le_mul hx hy (abs_nonneg _) zero_le_one
  have hFi : Integrable F (μ.restrict Ω) := by
    have hi₁ := ((localGamma_memL1 μ hQ q q).sub (localGamma_memL1 μ hQ H H)).bdd_mul
      (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ c))
      (by simpa only [Real.norm_eq_abs] using hc)
    have hi₂ := (integrable_finsetSum Finset.univ (fun j _ => localGamma_memL1 μ hQ (u j) (u j))).bdd_mul
      ((Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ c)).mul
        (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ w)))
      (by simpa only [Real.norm_eq_abs, Pi.mul_apply] using hiw)
    have hi₃ := (localGamma_memL1 μ hQ c H).bdd_mul
      (Lp.aestronglyMeasurable (SobolevSpace.toLp μ hQ w))
      (by simpa only [Real.norm_eq_abs] using hw)
    exact ((hi₁.add (hi₂.const_mul 2)).add (hi₃.const_mul 2)).integrableOn
  have hself := (Filter.eventually_all_finset (Finset.univ : Finset (Fin n))).mpr
    (fun j _ => localGamma_self μ hQ (u j))
  have hpoint : ∀ᵐ x ∂μ.restrict Ω, F x ≤ 2 * δ * (1 + B + T) + (C : ℝ) ^ 2 * G x := by
    filter_upwards [hsmall, heik, htrace, hcut, ae_restrict_of_ae hcrep,
      ae_restrict_of_ae (coordinateQuadratic_energy_error μ hQ u C hub),
      ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp μ hQ q) (SobolevSpace.toLp μ hQ H)),
      ae_restrict_of_ae hself] with x hsmallx heikx htracex hcutx hcpx hgramx hwx hselfx
    have hvalue : SobolevSpace.toLp μ hQ w x =
        SobolevSpace.toLp μ hQ q x - SobolevSpace.toLp μ hQ H x := hwx
    have hΓ : localGamma μ hQ q q x - localGamma μ hQ H H x ≤
        2 * SobolevSpace.toLp μ hQ w x + (C : ℝ) ^ 2 * G x := by
      have hl := (neg_le_abs (localGamma μ hQ H H x - 2 * SobolevSpace.toLp μ hQ H x)).trans hgramx
      rw [heikx]
      dsimp only [G] at *
      linarith
    apply cutoff_error_algebra (c := SobolevSpace.toLp μ hQ c x)
      (w := SobolevSpace.toLp μ hQ w x) (a := localGamma μ hQ q q x - localGamma μ hQ H H x)
      (b := ∑ j, localGamma μ hQ (u j) (u j) x) (d := localGamma μ hQ c H x)
      (G := G x) (A := (C : ℝ) ^ 2)
    · rw [hcpx]; exact hnonneg x
    · rw [hcpx]; exact (le_abs_self _).trans (hbound x)
    · exact hδ
    · positivity
    · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
    · exact hsmallx
    · exact hΓ
    · apply Finset.sum_nonneg
      intro j hj
      rw [hselfx j hj]
      positivity
    · exact htracex
    · exact hcutx
  have hiConst : Integrable (fun _ : X => 2 * δ * (1 + B + T)) (μ.restrict Ω) :=
    integrableOn_const hfin
  have hmono := integral_mono_ae hFi (hiConst.add (hG.const_mul ((C : ℝ) ^ 2))) hpoint
  have hsum := integral_add hiConst (hG.const_mul ((C : ℝ) ^ 2))
  simp only [Pi.add_apply] at hmono
  rw [hsum, integral_const, integral_const_mul] at hmono
  rw [coordinateQuadratic_local_difference_energy μ hQ u C D 1 L hu hub c q χ
    hχ hcpt hbound hnonneg hsupp hcrep hw]
  change (∫ x in Ω, F x ∂μ) ≤ _
  simpa only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul,
    G, mul_comm (μ Ω).toReal] using hmono

end RegularPointCoordinates

end

end OAI
