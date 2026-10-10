import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingScalar
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorForceSupport

namespace OAI

/-! The actual Navier–Stokes force has compact horizontal support on each
finite time interval, including all time derivatives of the prescribed drift. -/

noncomputable section
namespace ForcedComputation.ExpandingDetector
open ShearFlows Recorder VelocityDetector Set Filter
open scoped ContDiff Topology

def finiteDrift (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    (σ D K : ℝ) (N : ℕ) (t : ℝ) (x : Plane) : Plane :=
  ∑ n ∈ Finset.range N, stageDrift M hM blank m σ D K n t x

theorem finiteDrift_smooth (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    (σ D K : ℝ) (N : ℕ) :
    ContDiff ℝ ∞ (Function.uncurry (finiteDrift M hM blank m σ D K N)) := by
  change ContDiff ℝ ∞ (fun y : ℝ × Plane =>
    ∑ n ∈ Finset.range N, stageDrift M hM blank m σ D K n y.1 y.2)
  exact ContDiff.sum (fun n _ => stageDrift_smooth M hM blank m σ D K n)

theorem finiteDrift_compact_family (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    {σ D K : ℝ} (hσ : 0 < σ) (hD : 1 ≤ D) (hK : 0 ≤ K) (N : ℕ) :
    ∃ L : Set Plane, IsCompact L ∧
      ∀ t x, x ∉ L → finiteDrift M hM blank m σ D K N t x = 0 := by
  classical
  have hi (n : Fin N) : ∃ L : Set Plane, IsCompact L ∧
      ∀ t x, x ∉ L → stageDrift M hM blank m σ D K n.val t x = 0 :=
    recorderStageField_compact_family M hM blank (m + n.val) _
      (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (duration_ge_two hσ hD hK n.val))
      (radius_pos hσ hD hK n.val)
  choose L hL hz using hi
  refine ⟨⋃ n : Fin N, L n, isCompact_iUnion hL, ?_⟩
  intro t x hx
  apply Finset.sum_eq_zero
  intro n hn
  exact hz ⟨n, Finset.mem_range.mp hn⟩ t x
    (fun hh => hx (mem_iUnion.mpr ⟨⟨n, Finset.mem_range.mp hn⟩, hh⟩))

theorem expandingForce_compact_on_finite_intervals
    (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (m : ℕ)
    {σ D K : ℝ} (hσ : 0 < σ) (hD : 1 ≤ D) (hK : 0 ≤ K)
    (ν : ℝ) (p : Plane) (T : ℝ) :
    ∃ L : Set Plane, IsCompact L ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ x : Space,
      horizontalLinear x ∉ L →
      triangularForce ν (expandingDrift M hM blank m σ D K) (unitImpulse p) (t, x) = 0 := by
  let N : ℕ := ⌈T + 2⌉₊
  let a := finiteDrift M hM blank m σ D K N
  have ha : ContDiff ℝ ∞ (Function.uncurry a) := finiteDrift_smooth M hM blank m σ D K N
  have hfull := expandingDrift_smooth M hM blank m hσ hD hK
  obtain ⟨L, hL, hz⟩ := finiteDrift_compact_family M hM blank m hσ hD hK N
  let L' := L ∪ tsupport (spatialImpulse p)
  have hL' : IsCompact L' := hL.union (spatialImpulse_compactSupport p).isCompact
  refine ⟨L', hL', ?_⟩
  intro t ht x hx
  have hzero : triangularForce ν a (unitImpulse p) (t, x) = 0 := by
    apply triangularForce_zero_of_neighborhood ha hL'.isClosed.isOpen_compl _ ν t hx
    intro s y hy
    refine ⟨hz s y (fun h => hy (Or.inl h)), ?_⟩
    change smoothPulse 0 1 s * spatialImpulse p y = 0
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (Or.inr h)), mul_zero]
  have he : triangularVelocity (expandingDrift M hM blank m σ D K) (fun _ _ => 0) =ᶠ[𝓝 (t,x)]
      triangularVelocity a (fun _ _ => 0) := by
    have htime : ∀ᶠ y : SpaceTime in 𝓝 (t,x), y.1 < T + 1 :=
      (isOpen_lt continuous_fst continuous_const).mem_nhds (by change t < T + 1; linarith [ht.2])
    filter_upwards [htime] with y hy
    have hp := expandingDrift_eq_prefix M hM blank m hσ hD hK (T + 1) N
      (by have hN : T + 2 ≤ (N : ℝ) := Nat.le_ceil _; linarith) hy.le
    simp only [triangularVelocity, triangularLift, hp]
    rfl
  rw [triangularForce_eq_residual hfull, Pi.add_apply, residual_congr_germ he ν]
  rw [triangularForce_eq_residual ha, Pi.add_apply] at hzero
  exact hzero

end ForcedComputation.ExpandingDetector

end

end OAI
