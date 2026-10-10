import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingForceSupport
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneCompactH2

namespace OAI

/-! Finite-time strong regularity of the actual expanding drift. A finite
prefix agrees on an open time neighborhood, including at the endpoints. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Recorder VelocityDetector Set Filter
open scoped ContDiff Topology

theorem expandingDrift_eq_finite_near
    (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    {σ D K : ℝ} (hσ : 0 < σ) (hD : 1 ≤ D) (hK : 0 ≤ K)
    (T : ℝ) (N : ℕ) (hN : T + 2 ≤ (N : ℝ)) {t : ℝ} (ht : t ≤ T) (x : Plane) :
    Function.uncurry (expandingDrift M hM blank m σ D K) =ᶠ[𝓝 (t,x)]
      Function.uncurry (finiteDrift M hM blank m σ D K N) := by
  have htime : ∀ᶠ y : ℝ × Plane in 𝓝 (t,x), y.1 < T + 1 :=
    (isOpen_lt continuous_fst continuous_const).mem_nhds (by change t < T + 1; linarith)
  filter_upwards [htime] with y hy
  exact congrFun (expandingDrift_eq_prefix M hM blank m hσ hD hK (T+1) N
    (by linarith) hy.le) y.2

theorem expandingDrift_component_regularity
    (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    {σ D K : ℝ} (hσ : 0 < σ) (hD : 1 ≤ D) (hK : 0 ≤ K)
    (T : ℝ) (j : Fin 2) :
    let F := fun t x => expandingDrift M hM blank m σ D K t x j
    PlaneCInH2 F (Icc 0 T) ∧ PlaneC1L2 F (planeTemporalDerivative F) (Icc 0 T) := by
  let N : ℕ := ⌈T + 2⌉₊
  let F := fun t x => expandingDrift M hM blank m σ D K t x j
  let G := fun t x => finiteDrift M hM blank m σ D K N t x j
  have hG : ContDiff ℝ ∞ (Function.uncurry G) :=
    (contDiff_apply ℝ ℝ j).comp (finiteDrift_smooth M hM blank m σ D K N)
  obtain ⟨L, hL, hz⟩ := finiteDrift_compact_family M hM blank m hσ hD hK N
  have hzG : ∀ t x, x ∉ L → G t x = 0 := by
    intro t x hx
    change finiteDrift M hM blank m σ D K N t x j = 0
    rw [hz t x hx]
    rfl
  have hFG : ∀ t ∈ Icc (0 : ℝ) T, F t = G t := by
    intro t ht
    funext x
    exact congrArg (fun v : Plane => v j)
      ((expandingDrift_eq_finite_near M hM blank m hσ hD hK T N
        (Nat.le_ceil _) ht.2 x).self_of_nhds)
  have hdFG : ∀ t ∈ Icc (0 : ℝ) T,
      planeTemporalDerivative F t = planeTemporalDerivative G t := by
    intro t ht
    funext x
    have he : Function.uncurry F =ᶠ[𝓝 (t,x)] Function.uncurry G := by
      filter_upwards [expandingDrift_eq_finite_near M hM blank m hσ hD hK T N
        (Nat.le_ceil _) ht.2 x] with y hy
      exact congrArg (fun v : Plane => v j) hy
    exact congrArg (fun A : (ℝ × Plane) →L[ℝ] ℝ => A (1,0))
      (he.fderiv_eq (𝕜 := ℝ))
  exact ⟨(compact_family_cInH2 hG hL hzG T).congr_slices (fun t ht => (hFG t ht).symm),
    (compact_family_c1L2 hG hL hzG T).congr_slices
      (fun t ht => (hFG t ht).symm) (fun t ht => (hdFG t ht).symm)⟩

end ForcedComputation.ExpandingDetector

end

end OAI
