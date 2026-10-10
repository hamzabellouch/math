import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.PlanarSuspensionBridge

namespace OAI

/-! Finite concatenation of exact planar pulse curves. Local ODE identities
and matching endpoints determine the actual autonomous fluid trajectory. -/

noncomputable section
namespace ForcedComputation
open ShearFlows Set

theorem continuousOn_suspensionPath {γ : ℝ → Plane} {S : Set ℝ}
    (hγ : ContinuousOn γ S) : ContinuousOn (suspensionPath γ) S := by
  apply continuousOn_pi.mpr
  intro j
  fin_cases j
  · change ContinuousOn (fun t => γ t 0) S
    exact (continuous_apply 0).comp_continuousOn hγ
  · change ContinuousOn (fun t => γ t 1) S
    exact (continuous_apply 1).comp_continuousOn hγ
  · change ContinuousOn (fun t : ℝ => t) S
    exact continuousOn_id

theorem suspension_chain {H : FieldExpr} (hH : H.Valid)
    (hP : CubePeriodic 1 (SpatialExpression.spatialValue H))
    {Φ : ℝ → Space → Space}
    (hΦ : IsMaterialFlow 1 (fun y => SpatialExpression.suspensionField H y.2) Φ)
    {N : ℕ} {cuts : ℕ → ℝ} {γ : ℕ → ℝ → Plane} {p : ℕ → Plane} {x : Space}
    (hzero : cuts 0 = 0) (hx : x = atHeight (p 0) 0)
    (hcuts : ∀ i < N, cuts i ≤ cuts (i + 1))
    (hstart : ∀ i < N, γ i (cuts i) = p i)
    (hend : ∀ i < N, γ i (cuts (i + 1)) = p (i + 1))
    (hc : ∀ i < N, ContinuousOn (γ i) (Icc (cuts i) (cuts (i + 1))))
    (hd : ∀ i < N, ∀ s ∈ Ico (cuts i) (cuts (i + 1)),
      HasDerivAt (γ i) (PlanarHamiltonian.field
        (fun Y => SpatialExpression.spatialValue H (atHeight Y s)) (γ i s)) s)
    (hg : ∀ i < N, ∀ s ∈ Ico (cuts i) (cuts (i + 1)), unitSpatialClock (γ i s) = 1) :
    (∀ i ≤ N, Φ (cuts i) x = atHeight (p i) (cuts i)) ∧
      (∀ i < N, EqOn (fun s => Φ s x) (suspensionPath (γ i))
        (Icc (cuts i) (cuts (i + 1)))) := by
  have ha : ∀ i ≤ N, Φ (cuts i) x = atHeight (p i) (cuts i) := by
    intro i
    induction i with
    | zero =>
        intro _
        rw [hzero, hΦ.initial, hx]
    | succ i ih =>
        intro hi
        have hi' : i < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) hi
        have he := suspensionField_tracks_interval hH hP x
          (continuousOn_suspensionPath (hc i hi'))
          (by change atHeight (γ i (cuts i)) (cuts i) = Φ (cuts i) x
              rw [hstart i hi', ih (Nat.le_of_lt hi')])
          (hd i hi') (hg i hi') hΦ
        have hh := he ⟨hcuts i hi', le_rfl⟩
        simpa only [suspensionPath, hend i hi', Nat.succ_eq_add_one] using hh
  refine ⟨ha, ?_⟩
  intro i hi
  exact suspensionField_tracks_interval hH hP x
    (continuousOn_suspensionPath (hc i hi))
    (by change atHeight (γ i (cuts i)) (cuts i) = Φ (cuts i) x
        rw [hstart i hi, ha i (Nat.le_of_lt hi)]) (hd i hi) (hg i hi) hΦ

theorem finite_cuts_cover (n : ℕ) (cuts : ℕ → ℝ)
    (hcuts : ∀ i < n + 1, cuts i ≤ cuts (i + 1)) {s : ℝ}
    (hs : s ∈ Icc (cuts 0) (cuts (n + 1))) :
    ∃ i < n + 1, s ∈ Icc (cuts i) (cuts (i + 1)) := by
  induction n with
  | zero => exact ⟨0, by omega, hs⟩
  | succ n ih =>
      by_cases hsn : s ≤ cuts (n + 1)
      · obtain ⟨i, hi, his⟩ := ih (fun i hi => hcuts i (by omega)) ⟨hs.1, hsn⟩
        exact ⟨i, by omega, his⟩
      · exact ⟨n + 1, by omega, ⟨(lt_of_not_ge hsn).le, hs.2⟩⟩

theorem suspension_chain_mem {N : ℕ} (hN : 0 < N) {cuts : ℕ → ℝ}
    (hzero : cuts 0 = 0) (hone : cuts N = 1)
    (hcuts : ∀ i < N, cuts i ≤ cuts (i + 1))
    {γ : ℕ → ℝ → Plane} {Φ : ℝ → Space → Space} {x : Space} {S : Set Plane}
    (he : ∀ i < N, EqOn (fun s => Φ s x) (suspensionPath (γ i))
      (Icc (cuts i) (cuts (i + 1))))
    (hmem : ∀ i < N, ∀ s ∈ Icc (cuts i) (cuts (i + 1)), γ i s ∈ S) :
    ∀ s ∈ Icc (0 : ℝ) 1, horizontal (Φ s x) ∈ S := by
  intro s hs
  cases N with
  | zero => omega
  | succ n =>
      obtain ⟨i, hi, his⟩ := finite_cuts_cover n cuts hcuts
        (by simpa only [hzero, hone] using hs)
      have hes : Φ s x = suspensionPath (γ i) s := he i hi his
      rw [hes]
      simpa only [suspensionPath, atHeight_horizontal] using hmem i hi s his

end ForcedComputation

end

end OAI
