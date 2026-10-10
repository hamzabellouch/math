import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSymmetryIndependence
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedSymbol

namespace OAI

/-! # The injective physical modulation frame of the actual matched profile -/

open scoped ContDiff ZeroAtInfty

namespace DefocusingNLS

open ProfileCertificate
local notation "E" => EuclideanSpace ℝ (Fin 12)

abbrev ProfileSymmetryParameters := ℝ × E × ℝ

noncomputable def profileSymmetryFrame {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (q t : V) (D : E →L[ℝ] V) : ProfileSymmetryParameters →L[ℝ] V where
  toFun p := p.1 • q + D p.2.1 + p.2.2 • t
  map_add' p r := by simp only [Prod.fst_add, Prod.snd_add, add_smul, map_add]; abel
  map_smul' c p := by
    change (c * p.1) • q + D (c • p.2.1) + (c * p.2.2) • t =
      c • (p.1 • q + D p.2.1 + p.2.2 • t)
    simp only [map_smul, smul_add, smul_smul]
  cont := by fun_prop

theorem homogeneous_physical_symmetry_frame (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (hsymbol : ∀ n : ℕ, ∃ D : ℝ, ∀ y : E, 1 ≤ ‖y‖ →
      ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ)))
    (h0 : Q 0 ≠ 0) (heven : ∀ y, Q (-y) = Q y)
    (hstat : ∀ y, stationarySimilarityDefect a b m Q y = 0)
    (q : HomogeneousY a k)
    (hq : ∀ y, homogeneousPhysicalCLM a k ha ha1 hk q y = Q y) :
    ∃ F : ProfileSymmetryParameters →L[ℝ] HomogeneousY a k,
      Function.Injective F ∧ ∀ p y, homogeneousPhysicalCLM a k ha ha1 hk (F p) y =
        (p.1 : ℂ) * (Complex.I * Q y) +
        (p.2.2 : ℂ) * (((a : ℂ) - Complex.I * (b : ℂ)) * Q y + cartesianTransport Q y) +
          cartesianDerivative p.2.1 Q y := by
  obtain ⟨D, hD⟩ := homogeneous_profile_translation_map a k ha ha1 hk Q hQ hsymbol
  obtain ⟨t, ht⟩ := homogeneous_profile_time_direction a b k ha ha1 hk m Q hQ hsymbol q hq hstat
  let F := profileSymmetryFrame (Complex.I • q) t D
  have hF (p : ProfileSymmetryParameters) (y : E) :
      homogeneousPhysicalCLM a k ha ha1 hk (F p) y =
        (p.1 : ℂ) * (Complex.I * Q y) +
        (p.2.2 : ℂ) * (((a : ℂ) - Complex.I * (b : ℂ)) * Q y + cartesianTransport Q y) +
          cartesianDerivative p.2.1 Q y := by
    change homogeneousPhysicalCLM a k ha ha1 hk
      (p.1 • (Complex.I • q) + D p.2.1 + p.2.2 • t) y = _
    simp only [map_add, ContinuousLinearMap.map_smul_of_tower,
      ZeroAtInftyContinuousMap.add_apply, ZeroAtInftyContinuousMap.smul_apply,
      map_smul, smul_eq_mul, Complex.real_smul, hq, hD, ht]
    ring
  refine ⟨F, (injective_iff_map_eq_zero F).mpr ?_, hF⟩
  intro p hp
  let Q₀ := homogeneousPhysicalCLM a k ha ha1 hk q
  have heq : ⇑Q₀ = Q := funext hq
  have hz (y : E) : (p.1 : ℂ) * (Complex.I * Q₀ y) +
      (p.2.2 : ℂ) * (((a : ℂ) - Complex.I * (b : ℂ)) * Q₀ y + cartesianTransport Q₀ y) +
        cartesianDerivative p.2.1 Q₀ y = 0 := by
    rw [heq, ← hF, hp, map_zero]
    rfl
  obtain ⟨hs, ht, hv⟩ := physical_symmetry_directions_independent a b ha Q₀
    (heq.symm ▸ hQ.differentiable (by simp)) (by simpa only [heq] using h0)
    (by simpa only [heq] using heven) p.1 p.2.2 p.2.1 hz
  exact Prod.ext hs (Prod.ext hv ht)

theorem radialMatched_physical_symmetry_frame (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (k : ℝ)
    (ha : 0 < radialShootingA n) (ha1 : radialShootingA n < 1) (hk : 8 < k)
    (q : HomogeneousY (radialShootingA n) k)
    (hq : ∀ y, homogeneousPhysicalCLM (radialShootingA n) k ha ha1 hk q y =
      radialMatchedCartesian n z y) :
    ∃ F : ProfileSymmetryParameters →L[ℝ] HomogeneousY (radialShootingA n) k,
      Function.Injective F ∧ ∀ p y,
        homogeneousPhysicalCLM (radialShootingA n) k ha ha1 hk (F p) y =
          (p.1 : ℂ) * (Complex.I * radialMatchedCartesian n z y) +
          (p.2.2 : ℂ) * (((radialShootingA n : ℂ) -
            Complex.I * (radialShootingB (profileMatchingParameter z) : ℂ)) *
              radialMatchedCartesian n z y + cartesianTransport (radialMatchedCartesian n z) y) +
          cartesianDerivative p.2.1 (radialMatchedCartesian n z) y := by
  apply homogeneous_physical_symmetry_frame _ _ k ha ha1 hk
    (n + radialInnerShootingThreshold) _ (radialMatchedCartesian_contDiff n z hX hz)
    ?_ ?_ ?_ (radialMatchedCartesian_stationary n z hX hz) q hq
  · intro j
    obtain ⟨D, _, hD⟩ := radialMatchedCartesian_symbol n z hX hz j
    exact ⟨D, hD⟩
  · simpa only [radialMatchedCartesian, norm_zero] using radialMatchedProfile_ne_zero n z hX 0 le_rfl
  · intro y
    simp only [radialMatchedCartesian, norm_neg]

end DefocusingNLS

end OAI
