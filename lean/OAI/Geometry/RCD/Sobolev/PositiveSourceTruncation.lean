import OAI.Geometry.RCD.Sobolev.DirichletContractions

namespace OAI

/-!
# Truncation tests for the positive-source estimate

The clipped function belongs to the genuine Dirichlet space. Locality,
including on the clipping level set, identifies its energy with the
original function's energy below the level. Thus a source mass bound
controls the truncated energy linearly in the level.
-/

open Set MeasureTheory Filter
open scoped InnerProductSpace NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Positive clipping, with a nonnegative upper level. -/
def positiveClip (t x : ℝ) : ℝ := min (max x 0) t

theorem positiveClip_lipschitz (t : ℝ) : LipschitzWith 1 (positiveClip t) :=
  ((LipschitzWith.id : LipschitzWith 1 (fun x : ℝ => x)).max_const 0).min_const t

theorem positiveClip_zero {t : ℝ} (ht : 0 ≤ t) : positiveClip t 0 = 0 := by
  simp only [positiveClip, max_self, min_eq_left ht]

/-- The actual clipped Sobolev function. -/
def positiveTruncation (H : SobolevSpace μ hQ) (t : ℝ) (ht : 0 ≤ t) : SobolevSpace μ hQ :=
  SobolevSpace.compContraction μ hQ (positiveClip_lipschitz t) (positiveClip_zero ht) H

theorem positiveTruncation_coe (H : SobolevSpace μ hQ) {t : ℝ} (ht : 0 ≤ t) :
    SobolevSpace.toLp μ hQ (positiveTruncation μ hQ H t ht) =ᵐ[μ]
      fun x => positiveClip t (SobolevSpace.toLp μ hQ H x) :=
  (positiveClip_lipschitz t).coeFn_compLp (positiveClip_zero ht) _

theorem positiveTruncation_mem_dirichlet {Ω : Set X} (H : SobolevSpace μ hQ)
    (hH : H ∈ SobolevSpace.dirichlet μ hQ Ω) {t : ℝ} (ht : 0 ≤ t) :
    positiveTruncation μ hQ H t ht ∈ SobolevSpace.dirichlet μ hQ Ω :=
  SobolevSpace.compContraction_mem_dirichlet μ hQ (positiveClip_lipschitz t)
    (positiveClip_zero ht) Ω H hH

theorem positiveTruncation_bounds (H : SobolevSpace μ hQ) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ (positiveTruncation μ hQ H t ht) x ∧
      SobolevSpace.toLp μ hQ (positiveTruncation μ hQ H t ht) x ≤ t := by
  filter_upwards [positiveTruncation_coe μ hQ H ht] with x hx
  rw [hx]
  exact ⟨le_min (le_max_right _ _) ht, min_le_right _ _⟩

variable [BorelSpace X] [ProperSpace X]

/-- The energy density of the clipping, paired with the original function,
vanishes on and above the level and agrees below it. -/
theorem positiveTruncation_gamma (H : SobolevSpace μ hQ)
    (hH : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ H x)
    {t : ℝ} (ht : 0 ≤ t) :
    localGamma μ hQ H (positiveTruncation μ hQ H t ht) =ᵐ[μ]
      fun x => if SobolevSpace.toLp μ hQ H x < t then localGamma μ hQ H H x else 0 := by
  let T := positiveTruncation μ hQ H t ht
  filter_upwards [positiveTruncation_coe μ hQ H ht, hH,
    localGamma_comm μ hQ H T, localGamma_eq_on_eq μ hQ T H H,
    localGamma_zero_on_level μ hQ T H t] with x hx h0 hc he hz
  by_cases hlt : SobolevSpace.toLp μ hQ H x < t
  · rw [ite_eq_left hlt, hc]
    apply he
    rw [hx, positiveClip, max_eq_left h0, min_eq_left hlt.le]
  · rw [ite_eq_right hlt, hc]
    apply hz
    rw [hx, positiveClip, max_eq_left h0, min_eq_right (le_of_not_gt hlt)]

/-- The two energies agree exactly, so no Cauchy--Schwarz loss occurs. -/
theorem positiveTruncation_energy (H : SobolevSpace μ hQ)
    (hH : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ H x)
    {t : ℝ} (ht : 0 ≤ t) :
    energyForm μ hQ (positiveTruncation μ hQ H t ht) (positiveTruncation μ hQ H t ht) =
      energyForm μ hQ H (positiveTruncation μ hQ H t ht) := by
  let T := positiveTruncation μ hQ H t ht
  have hg : localGamma μ hQ T T =ᵐ[μ] localGamma μ hQ H T := by
    filter_upwards [positiveTruncation_coe μ hQ H ht, hH,
      localGamma_eq_on_eq μ hQ T H T, localGamma_zero_on_level μ hQ T T t,
      positiveTruncation_gamma μ hQ H hH ht] with x hx h0 he hz hg
    by_cases hlt : SobolevSpace.toLp μ hQ H x < t
    · apply he
      rw [hx, positiveClip, max_eq_left h0, min_eq_left hlt.le]
    · rw [hg, ite_eq_right hlt]
      apply hz
      rw [hx, positiveClip, max_eq_left h0, min_eq_right (le_of_not_gt hlt)]
  rw [← integral_localGamma_eq_energyForm, ← integral_localGamma_eq_energyForm]
  exact integral_congr_ae hg

/-- For a source of mass at most `P`, the energy of the truncation is at
most `P*t`. The hypothesis is its action on bounded nonnegative tests. -/
theorem positiveTruncation_energy_le (Ω : Set X) (H : SobolevSpace.dirichlet μ hQ Ω)
    (hH : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ H.val x) (P : ℝ)
    (hsource : ∀ φ : SobolevSpace.dirichlet μ hQ Ω, ∀ s : ℝ, 0 ≤ s →
      (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ.val x ∧ SobolevSpace.toLp μ hQ φ.val x ≤ s) →
      energyForm μ hQ H.val φ.val ≤ P * s)
    {t : ℝ} (ht : 0 ≤ t) :
    energyForm μ hQ (positiveTruncation μ hQ H.val t ht)
      (positiveTruncation μ hQ H.val t ht) ≤ P * t := by
  rw [positiveTruncation_energy μ hQ H.val hH ht]
  exact hsource ⟨_, positiveTruncation_mem_dirichlet μ hQ H.val H.property ht⟩ t ht
    (positiveTruncation_bounds μ hQ H.val ht)

end RegularPointCoordinates

end

end OAI
