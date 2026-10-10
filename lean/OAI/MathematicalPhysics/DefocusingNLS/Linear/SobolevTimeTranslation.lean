import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevLocalContinuousFlow

namespace OAI

/-! # Time translation and restarting the strong Schrödinger flow -/

open Filter Topology Set

namespace DefocusingNLS

/-- The strong physical equation is autonomous, so translating time preserves it. -/
theorem hasDerivAt_schrodinger_timeTranslation
    (k : ℝ) (hk : 6 < k) (m : ℕ) (u : ℝ → FourierL2) (s t : ℝ)
    (hu : HasDerivAt (fun r => lowerSobolevInclusion (u r))
      (lowerSobolevGenerator (u (s + t)) -
        Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (u (s + t)))) (s + t)) :
    HasDerivAt (fun r => lowerSobolevInclusion (u (s + r)))
      (lowerSobolevGenerator (u (s + t)) -
        Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (u (s + t)))) t := by
  simpa only [Function.comp_def, one_smul] using
    hu.scomp t ((hasDerivAt_id t).const_add s)

theorem continuousOn_timeTranslation (u : ℝ → FourierL2) (a b s : ℝ)
    (hu : ContinuousOn u (Ioo a b)) :
    ContinuousOn (fun t => u (s + t)) (Ioo (a - s) (b - s)) := by
  apply hu.comp (continuous_const.add continuous_id).continuousOn
  intro t ht
  change s + t ∈ Ioo a b
  constructor <;> linarith [ht.1, ht.2]

/-- A translated strong solution is a restriction of the maximal flow through its new datum. -/
theorem strongSobolev_timeTranslation_restricts_maximal
    (k : ℝ) (hk : 6 < k) (m : ℕ) (u : ℝ → FourierL2) (a b s : ℝ)
    (hs : s ∈ Ioo a b) (huc : ContinuousOn u (Ioo a b))
    (hu : ∀ t ∈ Ioo a b, HasDerivAt (fun r => lowerSobolevInclusion (u r))
      (lowerSobolevGenerator (u t) -
        Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (u t))) t) :
    Ioo (a - s) (b - s) ⊆ maximalSobolevInteractionDomain k hk m (u s) ∧
      EqOn (fun t => u (s + t)) (maximalSobolevSchrodingerFlow k hk m (u s))
        (Ioo (a - s) (b - s)) := by
  apply strongSobolevSchrodingerSolution_restricts_maximal k hk m (u s)
    (fun t => u (s + t)) (a - s) (b - s) (by linarith [hs.1]) (by linarith [hs.2])
    (by simp) (continuousOn_timeTranslation u a b s huc)
  intro t ht
  apply hasDerivAt_schrodinger_timeTranslation
  apply hu
  constructor <;> linarith [ht.1, ht.2]

/-- At every time of a maximal trajectory, the local flow through its value agrees with
the original trajectory on an open interval about that time. -/
theorem maximalSobolevSchrodingerFlow_local_restart
    (k : ℝ) (hk : 6 < k) (m : ℕ) (f₀ : FourierL2) (s : ℝ)
    (hs : s ∈ maximalSobolevInteractionDomain k hk m f₀) :
    ∃ a b : ℝ, a < 0 ∧ 0 < b ∧
      Ioo a b ⊆ maximalSobolevInteractionDomain k hk m
        (maximalSobolevSchrodingerFlow k hk m f₀ s) ∧
      ∀ t ∈ Ioo a b,
        s + t ∈ maximalSobolevInteractionDomain k hk m f₀ ∧
        maximalSobolevSchrodingerFlow k hk m f₀ (s + t) =
          maximalSobolevSchrodingerFlow k hk m
            (maximalSobolevSchrodingerFlow k hk m f₀ s) t := by
  obtain ⟨P, hP⟩ := mem_iUnion.mp hs
  have hsub := P.subset_maximalDomain
  obtain ⟨hdom, heq⟩ := strongSobolev_timeTranslation_restricts_maximal k hk m
    (maximalSobolevSchrodingerFlow k hk m f₀) P.left P.right s hP
    ((continuousOn_maximalSobolevSchrodingerFlow k hk m f₀).mono hsub)
    (fun t ht => hasDerivAt_maximalSobolevSchrodingerFlow k hk m f₀ (hsub ht))
  refine ⟨P.left - s, P.right - s, by linarith [hP.1], by linarith [hP.2], hdom, ?_⟩
  intro t ht
  refine ⟨hsub ?_, heq ht⟩
  constructor <;> linarith [ht.1, ht.2]

end DefocusingNLS

end OAI
