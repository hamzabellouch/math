import OAI.Geometry.NodalSets.Elliptic.BallPacking
import OAI.Geometry.NodalSets.Elliptic.FiniteCoverIntegral

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
noncomputable section

lemma packing_volume_weight {Q : Set Coord} (hQ : IsCompact Q)
    {s : Coord → ℝ} (hs : ContinuousOn s Q) (t : Finset Coord) (r : Coord → ℝ)
    {N : ℝ} (hN : 0 ≤ N) (ht : (↑t : Set Coord) ⊆ Q)
    (hr : ∀ x ∈ t, 0 ≤ r x) (hspos : ∀ x ∈ Q, 0 ≤ s x)
    (hscale : ∀ x ∈ t, N*s x*r x = 1)
    (hcov : Q ⊆ ⋃ x ∈ t, sourceClosedBall x (5*r x))
    (hcomp : ∀ x ∈ t, ∀ y ∈ Q ∩ sourceClosedBall x (5*r x), s y ≤ 2*s x) :
    N*(∫ x in Q, s x) ≤ 2*(Real.pi^2/2)*5^4 * ∑ x ∈ t, r x^3 := by
  have hh := integral_le_finite_cover (μ := volume) hQ.measurableSet (hs.integrableOn_compact hQ)
    t (fun x ↦ sourceClosedBall x (5*r x)) (fun x ↦ 2*s x)
    (fun x _ ↦ (sourceClosedBall_isCompact x _).measurableSet)
    (fun x _ ↦ (sourceClosedBall_isCompact x _).measure_ne_top)
    (fun x hx ↦ mul_nonneg (by norm_num) (hspos x (ht hx))) hcov hcomp
  apply (mul_le_mul_of_nonneg_left hh hN).trans
  rw [Finset.mul_sum,Finset.mul_sum]
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro x hx
  rw [sourceClosedBall_volume x (mul_nonneg (by norm_num) (hr x hx))]
  calc
    N * (Real.pi^2/2*(5*r x)^4*(2*s x)) =
        (2*(Real.pi^2/2)*5^4*r x^3)*(N*s x*r x) := by ring
    _ = _ := by rw [hscale x hx,mul_one]

end
end Yau.Geometry

end OAI
