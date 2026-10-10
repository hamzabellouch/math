import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.SymmetryRangeGenerator
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedCommonOrder
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousRealStableCoordinates
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffStableTransfer

namespace OAI

/-! # Stable contraction retaining its contour generator and decay -/

open Set Filter Topology
open scoped SchwartzMap ContDiff NNReal

namespace DefocusingNLS
open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

attribute [local irreducible] homogeneousComplexLinearizedStep homogeneousStableCoordinates
  expandingProfileTrajectory

theorem radialMatched_exists_stable_transfer_with_contour (hRou : RectangleRouche) :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
        (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius)) →
      (hz : radialMatchingMap n z = 0) →
      ∀ (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ)),
      (∀ y : E, 1 ≤ ‖y‖ → χ y = 0) → (∀ y : E, ‖y‖ ≤ 1 / 2 → χ y = 1) →
      ∃ N : ℕ, ∃ hk10 : 10 < ((N + 1 : ℕ) : ℝ),
        let hk : 8 < ((N + 1 : ℕ) : ℝ) := lt_trans (by norm_num) hk10
        let a := radialShootingA n
        let ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
        let ha1 := (radialShootingA_bounds n (profileMatchingParameter z)).2
        let b := radialShootingB (profileMatchingParameter z)
        let m := n + radialInnerShootingThreshold
        let Qp := radialMatchedCartesian n z
        let hQp := radialMatchedCartesian_contDiff n z hX hz
        ∃ q : HomogeneousY a ((N + 1 : ℕ) : ℝ),
          (∀ x : E, homogeneousPhysicalCLM a ((N + 1 : ℕ) : ℝ) ha ha1 hk q x = Qp x) ∧
          ∃ P : (HomogeneousY a ((N + 1 : ℕ) : ℝ) × HomogeneousY a ((N + 1 : ℕ) : ℝ)) →L[ℂ]
              (HomogeneousY a ((N + 1 : ℕ) : ℝ) × HomogeneousY a ((N + 1 : ℕ) : ℝ)),
            IsIdempotentElem P ∧ FiniteDimensional ℂ P.range ∧
            ∃ hcomm : ∀ t, Commute (homogeneousComplexLinearizedStep a b ((N + 1 : ℕ) : ℝ)
              ha ha1 hk m q t) P,
            HasSymmetryRangeGenerator
              (homogeneousComplexLinearizedStep a b ((N + 1 : ℕ) : ℝ) ha ha1 hk m q) P hcomm ∧
            ∃ D δ : ℝ, 0 < δ ∧
              (∀ t : ℝ≥0, ∀ v, P v = 0 →
                ‖homogeneousComplexLinearizedStep a b ((N + 1 : ℕ) : ℝ)
                  ha ha1 hk m q t v‖ ≤ D * Real.exp (-δ * (t : ℝ)) * ‖v‖) ∧
            ∃ Q : ℝ, ∃ hQ : 0 ≤ Q,
              ∃ hqb : ∀ L : Radius,
                ‖cutoffProfileCoefficient a (N + 1 : ℕ) ha1 hk χ hχ Qp hQp L‖ ≤ Q,
              ∀ β : ℝ, 0 < β → ∃ T₀ : ℝ, 0 ≤ T₀ ∧
                ∀ (T : ℝ) (hT : 0 ≤ T), T₀ ≤ T → ∃ L₀ : ℝ,
                  ∀ L : Radius, L₀ ≤ L.1 → ∀ f : FourierL2, ‖f‖ ≤ 1 →
                    homogeneousStableCoordinates a (N + 1 : ℕ) ha ha1 hk P
                      (homogeneousLocalizationCLM a (N + 1 : ℕ) L.1 ha ha1 hk L.2 χ f) = 0 →
                    ‖expandingProfileTrajectory a b (N + 1 : ℕ) L.1 T ha ha1 hk L.2 hT m Q hQ
                      (sampledCutoffProfilePath a (N + 1 : ℕ) L.1 T ha ha1 hk L.2 χ hχ Qp hQp)
                      (fun t => hqb (expandingRadiusCurve L.1 T L.2 t)) f
                      ⟨T, hT, le_rfl⟩‖ < β := by
  filter_upwards [radialMatched_exists_common_order hRou] with n hn
  intro z hX hz χ hχ hχzero hχone
  obtain ⟨N, hk10, q, hq, hg, hbound, c, hc, R, C, hC, he⟩ :=
    hn z hX hz χ hχ hχzero hχone
  let k : ℝ := (N + 1 : ℕ)
  have hk : 8 < k := lt_trans (by norm_num) hk10
  let a := radialShootingA n
  have ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
  have ha1 := (radialShootingA_bounds n (profileMatchingParameter z)).2
  let b := radialShootingB (profileMatchingParameter z)
  let m := n + radialInnerShootingThreshold
  let Qp := radialMatchedCartesian n z
  have hQp := radialMatchedCartesian_contDiff n z hX hz
  obtain ⟨P, hP, hfin, hcomm, ⟨D, δ, hD, hδ, hdecay⟩, G, hG, hspec, hspan⟩ := hg
  obtain ⟨Q, hQ, hqb⟩ := hbound
  obtain ⟨C₀, hC₀, hCb⟩ := exists_homogeneousLocalization_bound a k ha ha1 hk χ
  let π := homogeneousStableCoordinates a k ha ha1 hk P
  let C₁ := C * (‖homogeneousPhysicalCLM a k ha ha1 hk‖ * (D * C₀)) ^ 2
  have hlim := tendsto_escapedEnergyBound c (2 * δ) 1 C₁ hc (by linarith)
  refine ⟨N, hk10, q, hq, P, hP, hfin, hcomm, ⟨G, hG, hspec, hspan⟩, D, δ, hδ, hdecay, Q, hQ, hqb, ?_⟩
  intro β hβ
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (pow_pos hβ 2)))
  refine ⟨max 0 T₀, le_max_left _ _, ?_⟩
  intro T hT hTT
  have hsmall : escapedEnergyBound c (2 * δ) 1 C₁ T < β ^ 2 :=
    hT₀ T ((le_max_right 0 T₀).trans hTT)
  apply sampledCutoffProfile_uniform_stable_contraction a b k T Q C₀ c C R D δ β
    ha ha1 hk10 hT hQ hC₀ hc.le hC hD hβ m χ hχ hχzero hχone Qp hQp q hq hqb hCb π R he
  · intro u hu t
    exact homogeneousStableCoordinates_decay a k ha ha1 hk b m q P D δ hdecay T hT u hu t
  · exact hsmall

end DefocusingNLS

end OAI
