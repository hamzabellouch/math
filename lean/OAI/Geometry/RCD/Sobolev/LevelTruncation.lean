import OAI.Geometry.RCD.Sobolev.PositiveSourceTruncation

namespace OAI

/-!
# Two-level truncations in the Dirichlet space

These bounded tests give the superlevel iteration for the torsion function.
Locality at both clipping levels proves the exact energy identity.
-/

open Set MeasureTheory
open scoped NNReal InnerProductSpace

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

def levelClip (k l s : ℝ) : ℝ := positiveClip (l - k) (s - k)

theorem levelClip_lipschitz (k l : ℝ) : LipschitzWith 1 (levelClip k l) := by
  have ht : LipschitzWith 1 (fun x : ℝ => x - k) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    rw [show x - k - (y - k) = x - y by ring]
  change LipschitzWith 1 (positiveClip (l - k) ∘ fun x : ℝ => x - k)
  simpa only [one_mul] using (positiveClip_lipschitz (l - k)).comp ht

theorem levelClip_zero {k l : ℝ} (hk : 0 ≤ k) (hkl : k ≤ l) : levelClip k l 0 = 0 := by
  simp only [levelClip, positiveClip, zero_sub, max_eq_right (neg_nonpos.mpr hk),
    min_eq_left (sub_nonneg.mpr hkl)]

def levelTruncation (u : SobolevSpace μ hQ) {k l : ℝ} (hk : 0 ≤ k) (hkl : k ≤ l) :
    SobolevSpace μ hQ :=
  SobolevSpace.compContraction μ hQ (levelClip_lipschitz k l) (levelClip_zero hk hkl) u

theorem levelTruncation_coe (u : SobolevSpace μ hQ) {k l : ℝ}
    (hk : 0 ≤ k) (hkl : k ≤ l) :
    SobolevSpace.toLp μ hQ (levelTruncation μ hQ u hk hkl) =ᵐ[μ]
      fun x => levelClip k l (SobolevSpace.toLp μ hQ u x) :=
  (levelClip_lipschitz k l).coeFn_compLp (levelClip_zero hk hkl) _

theorem levelTruncation_mem_dirichlet (Ω : Set X) (u : SobolevSpace.dirichlet μ hQ Ω)
    {k l : ℝ} (hk : 0 ≤ k) (hkl : k ≤ l) :
    levelTruncation μ hQ u.val hk hkl ∈ SobolevSpace.dirichlet μ hQ Ω :=
  SobolevSpace.compContraction_mem_dirichlet μ hQ (levelClip_lipschitz k l)
    (levelClip_zero hk hkl) Ω u.val u.property

variable [BorelSpace X] [ProperSpace X]

/-- The bounded two-level test loses no energy in pairing with its source. -/
theorem levelTruncation_energy (u : SobolevSpace μ hQ) {k l : ℝ}
    (hk : 0 ≤ k) (hkl : k ≤ l) :
    energyForm μ hQ (levelTruncation μ hQ u hk hkl) (levelTruncation μ hQ u hk hkl) =
      energyForm μ hQ u (levelTruncation μ hQ u hk hkl) := by
  let T := levelTruncation μ hQ u hk hkl
  have heq : localGamma μ hQ T T =ᵐ[μ] localGamma μ hQ u T := by
    filter_upwards [levelTruncation_coe μ hQ u hk hkl,
      localGamma_zero_on_level μ hQ T T 0, localGamma_zero_on_level μ hQ T u 0,
      localGamma_zero_on_level μ hQ T T (l - k), localGamma_zero_on_level μ hQ T u (l - k),
      localGamma_zero_on_level μ hQ (u - T) T k, localGamma_sub_left μ hQ u T T,
      localGamma_comm μ hQ T u, Lp.coeFn_sub (SobolevSpace.toLp μ hQ u)
        (SobolevSpace.toLp μ hQ T)] with x hx h00 h01 hl0 hl1 hk0 hsub hc hcoe
    by_cases hlow : SobolevSpace.toLp μ hQ u x ≤ k
    · have hz : SobolevSpace.toLp μ hQ T x = 0 := by
        rw [hx]
        simp only [levelClip, positiveClip, max_eq_right (sub_nonpos.mpr hlow),
          min_eq_left (sub_nonneg.mpr hkl)]
      rw [h00 hz, ← hc, h01 hz]
    · by_cases hhigh : l ≤ SobolevSpace.toLp μ hQ u x
      · have hz : SobolevSpace.toLp μ hQ T x = l - k := by
          rw [hx]
          simp only [levelClip, positiveClip,
            max_eq_left (sub_nonneg.mpr (hkl.trans hhigh)),
            min_eq_right (sub_le_sub_right hhigh k)]
        rw [hl0 hz, ← hc, hl1 hz]
      · have hz : SobolevSpace.toLp μ hQ (u - T) x = k := by
          rw [map_sub, hcoe, Pi.sub_apply, hx]
          simp only [levelClip, positiveClip]
          rw [max_eq_left (by linarith), min_eq_left (by linarith)]
          ring
        have hn := hk0 hz
        rw [hsub] at hn
        linarith
  rw [← integral_localGamma_eq_energyForm, ← integral_localGamma_eq_energyForm]
  exact integral_congr_ae heq

/-- A unit-source torsion solution satisfies the exact truncated energy
identity required for its superlevel iteration. -/
theorem torsion_level_energy (Ω : Set X) (u : SobolevSpace.dirichlet μ hQ Ω)
    (hsolve : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      energyForm μ hQ u.val φ.val = ∫ x in Ω, SobolevSpace.toLp μ hQ φ.val x ∂μ)
    {k l : ℝ} (hk : 0 ≤ k) (hkl : k ≤ l) :
    energyForm μ hQ (levelTruncation μ hQ u.val hk hkl) (levelTruncation μ hQ u.val hk hkl) =
      ∫ x in Ω, levelClip k l (SobolevSpace.toLp μ hQ u.val x) ∂μ := by
  rw [levelTruncation_energy]
  let φ : SobolevSpace.dirichlet μ hQ Ω :=
    ⟨levelTruncation μ hQ u.val hk hkl, levelTruncation_mem_dirichlet μ hQ Ω u hk hkl⟩
  exact (hsolve φ).trans (integral_congr_ae
    (ae_restrict_of_ae (levelTruncation_coe μ hQ u.val hk hkl)))

end RegularPointCoordinates

end

end OAI
