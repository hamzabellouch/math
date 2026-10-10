import OAI.Probability.DilutedSpin.ScheduledContinuity
import OAI.Probability.DilutedSpin.ScheduledFrameError

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open PrescribedTree
variable {Ω : Type} [Fintype Ω] {N L : ℕ}

/-- The actual single-copy conditional covariance of a reduced topology at a
specified evaluation depth, with all unary grid transitions retained. Outside
the available evaluation horizon it is zero; all induction applications are
inside the literal admissible regular-depth domain. -/
noncomputable def scheduledShapeEnergy (L d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) : ℝ :=
  if h : d<L then
    shapeEnergyAt (realize (L-(d+1)) (d+1) S q) d
      (kernelHeightCast (by omega) T) (vectorHeightCast (by omega) f)
  else 0

lemma scheduledShapeEnergy_nonneg (d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) :
    0 ≤ scheduledShapeEnergy L d S q T f := by
  unfold scheduledShapeEnergy
  split_ifs
  · exact shapeEnergyAt_nonneg _ _ _ _
  · exact le_rfl

lemma scheduledShapeEnergy_eq_realize (n d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (h : L=n+1+d) (T : KernelTower Ω L) (f : FinitePath Ω L → Fin N → ℝ) :
    scheduledShapeEnergy L d S q T f =
      shapeEnergyAt (realize n (d+1) S q) d (kernelHeightCast h T) (vectorHeightCast h f) := by
  subst L
  unfold scheduledShapeEnergy
  rw [dite_eq_left (by omega : d<n+1+d)]
  have he (n' : ℕ) (hn : n'=n) (hc : n+1+d=n'+1+d) :
      shapeEnergyAt (realize n' (d+1) S q) d (kernelHeightCast hc T) (vectorHeightCast hc f) =
        shapeEnergyAt (realize n (d+1) S q) d T f := by
    subst n'
    rfl
  exact he _ (by omega) _

@[simp] lemma scheduledShapeEnergy_heightCast {n m : ℕ} (h : n=m) (d : ℕ)
    (S : ReducedTopology) (q : S.Vertex → ℕ) (T : KernelTower Ω n)
    (f : FinitePath Ω n → Fin N → ℝ) :
    scheduledShapeEnergy m d S q (kernelHeightCast h T) (vectorHeightCast h f) =
      scheduledShapeEnergy n d S q T f := by
  cases h
  rfl

/-- Exact retained-coordinate identification used by the fiber estimate. The
child covariance at the later first split is precisely this same energy family,
not a separately selected experiment and not a two-copy depth average. -/
lemma descendantEnergyAt_eq_scheduled (n r d : ℕ) (S : ReducedTopology) (q : S.Vertex → ℕ)
    (T : KernelTower Ω (n+1+r+1+d)) (f : FinitePath Ω (n+1+r+1+d) → Fin N → ℝ) :
    descendantEnergyAt (realize n (r+1+d+1) S q) r d T f =
      scheduledShapeEnergy (n+1+r+1+d) (r+1+d) S q T f := by
  rw [scheduledShapeEnergy_eq_realize n (r+1+d) S q (by omega)]
  exact descendantEnergyAt_eq_shapeEnergyAt _ r d T f

/-- The left side of the multileaf step belongs to the same literal scheduled
covariance family as its proper-child energies. -/
lemma scheduledShapeEnergy_node (n r d : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ))
    (C : Fin k → ReducedTopology) (q : (j : Fin k) → (C j).Vertex → ℕ)
    (hq : ∀ j v, r+1+d+1≤q j v)
    (T : KernelTower Ω (n+1+r+1+d)) (f : FinitePath Ω (n+1+r+1+d) → Fin N → ℝ) :
    scheduledShapeEnergy (n+1+r+1+d) d (.node k hk C) (rootSchedule (r+1+d) q) T f =
      shapeEnergyAt (stem (.node k (fun j => realize n (r+1+d+1) (C j) (q j))) r) d T f := by
  rw [scheduledShapeEnergy_eq_realize (n+1+r) d _ _ rfl]
  have hlow : ∀ v : (ReducedTopology.node k hk C).Vertex, d+1+r≤rootSchedule (r+1+d) q v := by
    intro v
    cases v with
    | none => simp only [rootSchedule]; omega
    | some v => have hh := hq v.1 v.2; dsimp only [rootSchedule]; omega
  rw [realize_stem (n+1) r (d+1) _ _ hlow]
  simp only [realize,rootSchedule,show ¬d+1+r<r+1+d by omega,ite_false,
    show d+1+r+1=r+1+d+1 by omega]
  rfl

end DilutedSpinGlass.ReducedTopology
end

end

end OAI
