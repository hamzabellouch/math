import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.AutonomousStartup
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.StageFlow

namespace OAI

/-! The spatial-clock part of the eventually stationary construction. The
clock needs unit speed only along the selected planar trajectory. -/

noncomputable section
namespace ForcedComputation
open ShearFlows Set
open scoped ContDiff NNReal

def spatialSuspension (V : ℝ → Plane → Plane) (g : Plane → ℝ) (x : Space) : Space :=
  atHeight (V (x 2) (horizontal x)) (g (horizontal x))

theorem spatialSuspension_smooth {V : ℝ → Plane → Plane} {g : Plane → ℝ}
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (spatialSuspension V g) := by
  have hh : ContDiff ℝ ∞ horizontal := by
    have he : (selectTwo 0 1 : Space → Plane) = horizontal := funext selectTwo_zero_one
    rw [← he]
    exact (selectTwo 0 1).contDiff
  have hv : ContDiff ℝ ∞ (fun x : Space => V (x 2) (horizontal x)) :=
    hV.comp ((contDiff_apply ℝ ℝ (2 : Fin 3)).prodMk hh)
  apply contDiff_pi.mpr
  intro j
  fin_cases j
  · exact (contDiff_apply ℝ ℝ (0 : Fin 2)).comp hv
  · exact (contDiff_apply ℝ ℝ (1 : Fin 2)).comp hv
  · exact hg.comp hh

theorem spatialSuspension_periodic {V : ℝ → Plane → Plane} {g : Plane → ℝ}
    (hVt : ∀ (t : ℝ) (x : Plane) (n : ℤ), V (t + n) x = V t x)
    (hVx : ∀ t x (n : Fin 2 → ℤ), V t (x + fun j => (n j : ℝ)) = V t x)
    (hg : ∀ x (n : Fin 2 → ℤ), g (x + fun j => (n j : ℝ)) = g x) :
    ∀ x n, spatialSuspension V g (x + latticeVector 1 n) = spatialSuspension V g x := by
  intro x n
  have hh : horizontal (x + latticeVector 1 n) =
      horizontal x + fun j => (n j.castSucc : ℝ) := by
    ext j
    fin_cases j <;> simp [horizontal, latticeVector]
  have hz : (x + latticeVector 1 n) 2 = x 2 + (n 2 : ℝ) := by
    simp [latticeVector]
  simp only [spatialSuspension, hh, hz, hVt, hVx, hg]

def suspensionPath (ψ : ℝ → Plane) (s : ℝ) : Space := atHeight (ψ s) s

theorem suspensionPath_hasDerivAt {ψ : ℝ → Plane} {V : ℝ → Plane → Plane}
    {g : Plane → ℝ} {s : ℝ}
    (hψ : HasDerivAt ψ (V s (ψ s)) s) (hg : g (ψ s) = 1) :
    HasDerivAt (suspensionPath ψ)
      (spatialSuspension V g (suspensionPath ψ s)) s := by
  have he : spatialSuspension V g (suspensionPath ψ s) = atHeight (V s (ψ s)) 1 := by
    have hh (X : Plane) (z : ℝ) : horizontal (atHeight X z) = X := by
      funext j
      fin_cases j <;> rfl
    simp only [spatialSuspension, suspensionPath, hh]
    change atHeight (V s (ψ s)) (g (ψ s)) = _
    rw [hg]
  rw [he]
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases j
  · exact (hasDerivAt_pi.mp hψ) 0
  · exact (hasDerivAt_pi.mp hψ) 1
  · exact hasDerivAt_id s

theorem spatialSuspension_tracks {V : ℝ → Plane → Plane} {g : Plane → ℝ}
    {ψ : ℝ → Plane} {p : Plane} {Φ : ℝ → Space → Space} {K : ℝ≥0}
    (hψ : ∀ s, HasDerivAt ψ (V s (ψ s)) s) (hp : ψ 0 = p)
    (hg : ∀ s, 0 ≤ s → g (ψ s) = 1)
    (hK : LipschitzWith K (spatialSuspension V g))
    (hΦ : IsMaterialFlow 1 (fun y => spatialSuspension V g y.2) Φ)
    {s : ℝ} (hs : 0 ≤ s) : Φ s (atHeight p 0) = suspensionPath ψ s := by
  have hc : Continuous (suspensionPath ψ) := by
    have hcψ : Continuous ψ := continuous_iff_continuousAt.mpr (fun t => (hψ t).continuousAt)
    apply continuous_pi
    intro j
    fin_cases j
    · change Continuous (fun s => ψ s 0)
      exact (continuous_apply 0).comp hcψ
    · change Continuous (fun s => ψ s 1)
      exact (continuous_apply 1).comp hcψ
    · exact continuous_id
  have he : suspensionPath ψ 0 = Φ 0 (atHeight p 0) := by
    simp [suspensionPath, hp, hΦ.initial]
  exact hΦ.eqOn_of_candidate (fun _ => hK) (atHeight p 0) (suspensionPath ψ)
    hc.continuousOn he
    (fun t ht => suspensionPath_hasDerivAt (hψ t) (hg t ht.1)) ⟨hs, le_rfl⟩

theorem spatialSuspension_observation {V : ℝ → Plane → Plane} {g : Plane → ℝ}
    {ψ : ℝ → Plane} {p : Plane} {Φ : ℝ → Space → Space} {K : ℝ≥0}
    (hψ : ∀ s, HasDerivAt ψ (V s (ψ s)) s) (hp : ψ 0 = p)
    (hg : ∀ s, 0 ≤ s → g (ψ s) = 1)
    (hK : LipschitzWith K (spatialSuspension V g))
    (hΦ : IsMaterialFlow 1 (fun y => spatialSuspension V g y.2) Φ)
    (a b : ℝ) :
    (∃ s : ℝ, 0 ≤ s ∧ a < Φ s (atHeight p 0) 1 ∧ Φ s (atHeight p 0) 1 < b) ↔
      ∃ s : ℝ, 0 ≤ s ∧ a < ψ s 1 ∧ ψ s 1 < b := by
  have he (s : ℝ) (hs : 0 ≤ s) : Φ s (atHeight p 0) 1 = ψ s 1 := by
    rw [spatialSuspension_tracks hψ hp hg hK hΦ hs]
    rfl
  constructor <;> rintro ⟨s, hs, hlow, hupp⟩
  · exact ⟨s, hs, by simpa only [he s hs] using hlow,
      by simpa only [he s hs] using hupp⟩
  · exact ⟨s, hs, by simpa only [he s hs] using hlow,
      by simpa only [he s hs] using hupp⟩

/-- An individual finite processor segment can be lifted without making any
claim about the planar trajectory after that segment. -/
theorem spatialSuspension_tracks_interval {V : ℝ → Plane → Plane} {g : Plane → ℝ}
    {ψ : ℝ → Plane} {Φ : ℝ → Space → Space} {K : ℝ≥0} {a b : ℝ} (x : Space)
    (hc : ContinuousOn (suspensionPath ψ) (Icc a b))
    (hp : suspensionPath ψ a = Φ a x)
    (hψ : ∀ s ∈ Ico a b, HasDerivAt ψ (V s (ψ s)) s)
    (hg : ∀ s ∈ Ico a b, g (ψ s) = 1)
    (hK : LipschitzWith K (spatialSuspension V g))
    (hΦ : IsMaterialFlow 1 (fun y => spatialSuspension V g y.2) Φ) :
    EqOn (fun s => Φ s x) (suspensionPath ψ) (Icc a b) := by
  apply hΦ.eqOn_of_candidate (fun _ => hK) x (suspensionPath ψ) hc hp
  intro s hs
  exact suspensionPath_hasDerivAt (hψ s hs) (hg s hs)

end ForcedComputation

end

end OAI
