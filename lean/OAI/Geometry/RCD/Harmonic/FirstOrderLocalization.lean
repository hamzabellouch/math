import OAI.Geometry.RCD.Coordinates.TransformationInput

namespace OAI

/-! # Restricting harmonic splitting data to nearby balls -/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

omit [BorelSpace X] in
theorem dirichlet_mono {s t : Set X} (hst : s ⊆ t) :
    SobolevSpace.dirichlet μ hQ s ≤ SobolevSpace.dirichlet μ hQ t := by
  apply Submodule.topologicalClosure_mono
  rintro v ⟨f, C, hf, hfc, hfs, hfv⟩
  exact ⟨f, C, hf, hfc, hfs.trans hst, hfv⟩

omit [BorelSpace X] in
theorem IsSobolevHarmonicOn.mono {s t : Set X} {u : SobolevSpace μ hQ}
    (hu : IsSobolevHarmonicOn μ hQ t u) (hst : s ⊆ t) :
    IsSobolevHarmonicOn μ hQ s u := by
  intro φ hφ
  exact hu φ (dirichlet_mono μ hQ hst hφ)

/-- First-order splitting conditions localize with exactly the volume-ratio
loss in the averaged Gram error. Harmonicity and representatives are genuine
restrictions of the same original functions. -/
theorem FirstOrderSplittingOn.restrict_ball {n : ℕ} {p q : X} {R r ε C : ℝ}
    {u : Fin n → SobolevSpace μ hQ} {v : X → Euclidean n}
    (h : FirstOrderSplittingOn μ hQ p R ε u v)
    (hsub : ball q r ⊆ ball p R) (hε : 0 ≤ ε) (hC : 1 ≤ C)
    (hszero : μ (ball q r) ≠ 0) (hsfin : μ (ball q r) ≠ ∞)
    (htzero : μ (ball p R) ≠ 0) (htfin : μ (ball p R) ≠ ∞)
    (hvol : μ.real (ball p R) ≤ C * μ.real (ball q r)) :
    FirstOrderSplittingOn μ hQ q r (C * ε) u v := by
  have heC : ε ≤ C * ε := by nlinarith
  refine ⟨fun i => ae_restrict_of_ae_restrict_of_subset hsub (h.representative i),
    h.continuous.mono hsub, fun i => (h.harmonic i).mono μ hQ hsub, ?_, ?_⟩
  · intro i
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (h.gradient i)] with x hx
    have hsq : (1 + ε) ^ 2 ≤ (1 + C * ε) ^ 2 := by nlinarith
    exact hx.trans hsq
  · intro i j
    have hf : IntegrableOn (fun x => |localGamma μ hQ (u i) (u j) x -
        (if i = j then 1 else 0)|) (ball p R) μ :=
      ((localGamma_memL1 μ hQ (u i) (u j)).integrableOn.sub (integrableOn_const htfin)).abs
    exact average_nonneg_le_of_subset μ hsub (ENNReal.toReal_pos hszero hsfin)
      (ENNReal.toReal_pos htzero htfin) hf (fun _ => abs_nonneg _) hε hvol (h.gram i j)

end RegularPointCoordinates

end

end OAI
