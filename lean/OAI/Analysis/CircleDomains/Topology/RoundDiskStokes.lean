import OAI.Analysis.CircleDomains.Sobolev.FiniteOffsetStokes
import OAI.Analysis.CircleDomains.Topology.RoundDiskDistance

namespace OAI

/-! Stokes with the manuscript's actual distance to the distinguished
round disk. Packing the other round disks gives the square-norm bound. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology BigOperators

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem finite_round_disk_stokes_bound
    (hgreen : FiniteCircleGreenFormula)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : PositiveJordanParametrization H γ)
    (n : ℕ) (c : Fin n → ℂ) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hin : ∀ i, closedBall (c i) (r i) ⊆ jordanInterior H)
    (O : Set ℂ) (hO : IsOpen O)
    (hsub : (closure (jordanInterior H) \ ⋃ i, ball (c i) (r i)) ⊆ O)
    (u : ℂ → UnitAddCircle) (hu : SmoothCircleOn u O)
    {L : ℝ} (hL : 0 ≤ L) (hbounded : jordanInterior H ⊆ closedBall 0 L)
    (henergy : MemLp (circleFDeriv u) 2
      (volume.restrict (jordanInterior H \ ⋃ i, closedBall (c i) (r i))))
    (b : Fin n) (rb ρ : ℝ) (hrb : 0 ≤ rb) (hρ : 0 < ρ) (hradius : r b = rb + ρ)
    (haway : O ⊆ (closedBall (c b) rb)ᶜ)
    (v : Fin n → ℝ → ℝ) (hv : ∀ i, Continuous (v i))
    (hproj : ∀ i t, (v i t : UnitAddCircle) = u (unitCircleParam (c i) (r i) t))
    (hb : v b 1 - v b 0 = 1) (hzero : ∀ i ≠ b, v i 1 = v i 0)
    (A : Fin n → ℝ) (hA : ∀ i ≠ b, ∀ t ∈ Icc (0 : ℝ) 1, |v i t - v i 0| ≤ A i) :
    |circleFormIntegral (fun z => infDist z (closedBall (c b) rb)) u γ| ≤
      Real.sqrt Real.pi * L * Real.sqrt
        (∫ z in jordanInterior H \ ⋃ i, closedBall (c i) (r i), ‖circleFDeriv u z‖ ^ 2) +
      ρ + 2 * Real.pi * L * Real.sqrt (∑ i ∈ Finset.univ.erase b, A i ^ 2) := by
  have he := finite_offset_stokes_bound hgreen H γ hγ n c r hr hd hin O hO hsub
    (fun z => infDist z (closedBall (c b) rb))
    ((contDiffOn_infDist_closedBall (c b) hrb).mono haway)
    (lipschitz_infDist_pt _) u hu hL (fun z hz => hbounded hz.1) henergy
    b ρ hρ.le v hv hproj hb (fun t _ => by
      rw [hradius]
      exact infDist_closedBall_unitCircle_offset (c b) hrb hρ t) hzero A hA
  have hall := sum_radii_sq_le_of_disjoint_closed_disks c r (fun i => (hr i).le)
    hL hd (fun i => (hin i).trans hbounded)
  have hrad : (∑ i ∈ Finset.univ.erase b, r i ^ 2) ≤ L ^ 2 := by
    refine le_trans ?_ hall
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset b Finset.univ)
      (fun i _ _ => sq_nonneg (r i))
  exact he.trans (add_le_add le_rfl
    (circle_costs_le_square_norm (Finset.univ.erase b) r A hL hrad))

end CircleDomainRigidity

end

end OAI
