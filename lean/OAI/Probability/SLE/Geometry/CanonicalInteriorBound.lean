import OAI.Probability.SLE.Gauge.PrescribedCanonicalTransfer
import OAI.Probability.SLE.Gauge.PrescribedUniformGeometry

namespace OAI

/-! The canonical finite-law failure estimate gives the exact uniform
  interior bound used in the prescribed upper cover. -/
noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (M : CanonicalMass P κ B hBm γ G)

def prescribedCenteredFailure (W : Target.WienerLaw) (n : ℕ) {J : ℕ}
    (e : Fin J → ℤ×ℕ) (C c : ℝ) (z : ℂ) : ℝ≥0∞ :=
  finiteCenteredLaw P κ B γ G z (Target.entryPhysicalLevel κ W (n,none) (2048*Real.pi) z)
    (M.prescribedTestFailures W n e C c z
      (fun i ω => radiusLevelTime (γ ω) (G ω) z
        (Target.entryPhysicalLevel κ W (n,some (e i)) (2048*Real.pi) z+
          2*Target.a κ*(Target.batchLevel κ W n:ℝ))))

theorem eventually_prescribed_interior_bound
    (hB : IsBrownianReal B P) (hc : ∀ ω, Continuous (fun t => B t ω))
    (h0 : ∀ ω, B 0 ω=0) (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hpublished : PublishedTraceGeneration (P.map (sourceDriverPath B hc)) κ (fun t p => p t))
    (W : Target.WienerLaw) (hm1 : 0 < Target.moment κ W 1)
    (hJ : ∀ n, 1≤n → Target.moment κ W 1^n ≤ Target.moment κ W n)
    (J : ℕ → ℕ) (e : ∀ n, Fin (J n) → ℤ×ℕ)
    (he : ∀ n i, (e n i).2 < Target.multiplicity κ W n (e n i).1)
    (C c R : ℝ) (K : Set ℂ)
    (hfailure : ∀ᶠ n in atTop, ∀ ij∈prescribedGridIndex R (Target.entryRadius κ W (n,none)) K,
      Real.exp (-(n:ℝ)) ≤ (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij).im →
      M.prescribedCenteredFailure W n (e n) C c
        (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij) ≤
        ENNReal.ofReal (Real.exp (-((2:ℝ)^n/16)))) :
    ∀ᶠ n in atTop, ∀ ij∈prescribedGridIndex R (Target.entryRadius κ W (n,none)) K,
      Real.exp (-(n:ℝ)) ≤ (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij).im →
      P {ω | ij∈prescribedMissedIndices κ W n (e n) C c R K (range (γ ω)∩K)
        (M.rational.physicalTerminal ω)} ≤
      ENNReal.ofReal ((uniformInverseAngleConstant κ 1*(2048*Real.pi)^codimension κ*
        (2:ℝ)^(-codimension κ))*(Target.entryRadius κ W (n,none))^codimension κ*
        (prescribedGridCenter (Target.entryRadius κ W (n,none)) ij).im^(-codimension κ)*
        Real.exp (-((2:ℝ)^n/16))) := by
  filter_upwards [hfailure,Target.eventually_prescribed_uniform_geometry hκ W hm1 hJ,
    Target.eventually_entryPhysicalLevel_large hκ W (by positivity : 0<2048*Real.pi) 1]
    with n hn hg hl
  intro ij hij hy
  let z := prescribedGridCenter (Target.entryRadius κ W (n,none)) ij
  obtain ⟨hlevels,hsmall,hends⟩ := hg z hy
  let V := Target.entryPhysicalLevel κ W (n,none) (2048*Real.pi) z
  have hV : 1<V := hl none z hy
  have hend (i : Fin (J n)) : Target.entryPhysicalLevel κ W (n,some (e n i)) (2048*Real.pi) z+
      2*Target.a κ*(Target.batchLevel κ W n:ℝ) ≤ V-1 := by
    have hh := hends (e n i).1 (e n i).2 (he n i)
    dsimp only [V]
    linarith
  exact M.prescribed_missed_from_finite_failure hB hc h0 hκ hκ8 F hw hpublished W n (e n)
    C c R K ij hij hlevels (V-1) (by linarith) (by linarith) hend hsmall
    _ (Real.exp_pos _).le (hn ij hij hy)

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI
