import OAI.Analysis.LienardCycles.BaseTransport

namespace OAI

universe uP

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

namespace QuinticLienard.ArchSymmetries
open ScalarArcs ArcFamilies CanonicalVariation WidthCoordinates
variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ContDiff ℝ ω Φ)
    (hloc : ∀ x : State P, ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)

include hΦ hloc

theorem base_affine {p q : P} {t r c H C : ℝ} (hr : 0 < r) (hc : 0 < c)
    (he : ∀ x, Φ (q,H+c^2*x) = C+c*Φ (p,x)) :
    baseAtWidth Φ ((q,H+c^2*t),c*r) = H+c^2*baseAtWidth Φ ((p,t),r) := by
  have hs := base_spec Φ hΦ hloc (p := p) (t := t) hr
  have hw := width_affine Φ hΦ hs.1 hc he
  rw [hs.2] at hw
  exact base_eq Φ hΦ hloc (mul_pos hc hr)
    (by nlinarith [sq_pos_of_pos hc]) hw

end QuinticLienard.ArchSymmetries

end OAI
