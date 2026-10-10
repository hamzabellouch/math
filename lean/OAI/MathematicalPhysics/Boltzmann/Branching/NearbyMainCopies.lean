import OAI.MathematicalPhysics.Boltzmann.Branching.MainCoreScaleWindow

namespace OAI

/-! # Nearby retained collision points use the same periodic origin -/

noncomputable section

open Set
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.JetGeometry

namespace BoltzmannNonuniqueness.JetLattice

theorem nearby_enlargements_same_lattice {s₀ η t₁ t₂ : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
    (ht₁ : t₁ ≤ 1/32) (ht₂ : t₂ ≤ 1/32)
    {i j : Label} {x y : Velocity}
    (hx : x ∈ spatialEnlargement s₀ η t₁ i)
    (hy : y ∈ spatialEnlargement s₀ η t₂ j) (hxy : ‖x-y‖ < 1/4) :
    i.lattice = j.lattice := by
  have hix := enlargement_inside_baseBall hs₀ hη i.annulus i.positive hx.1
  have hjy := enlargement_inside_baseBall hs₀ hη j.annulus j.positive hy.1
  rw [Metric.mem_ball,dist_zero_right] at hix hjy
  have htrans (k : Fin 2) : i.lattice k.castSucc = j.lattice k.castSucc := by
    by_contra hne
    have hi := PiLp.norm_apply_le (transverse x-transverseShift i.lattice) k
    have hj := PiLp.norm_apply_le (transverse y-transverseShift j.lattice) k
    have hdist := PiLp.norm_apply_le (x-y) k.castSucc
    change |x k.castSucc-(i.lattice k.castSucc : ℝ)| ≤ _ at hi
    change |y k.castSucc-(j.lattice k.castSucc : ℝ)| ≤ _ at hj
    change |x k.castSucc-y k.castSucc| ≤ ‖x-y‖ at hdist
    have h₁ := abs_sub_le (i.lattice k.castSucc : ℝ) (x k.castSucc) (y k.castSucc)
    have h₂ := abs_sub_le (i.lattice k.castSucc : ℝ) (y k.castSucc) (j.lattice k.castSucc)
    rw [abs_sub_comm (i.lattice k.castSucc : ℝ) (x k.castSucc)] at h₁
    have hsep := integer_distance hne
    linarith
  have hax : i.lattice (Fin.last 2) = j.lattice (Fin.last 2) := by
    by_contra hne
    have hi := hx.2
    have hj := hy.2
    have hdist := PiLp.norm_apply_le (x-y) (Fin.last 2)
    change |axial x-axial y| ≤ ‖x-y‖ at hdist
    have h₁ := abs_sub_le (axialShift i.lattice) (axial x) (axial y)
    have h₂ := abs_sub_le (axialShift i.lattice) (axial y) (axialShift j.lattice)
    rw [abs_sub_comm (axialShift i.lattice) (axial x)] at h₁
    have hsep : 1 ≤ |axialShift i.lattice-axialShift j.lattice| := integer_distance hne
    linarith
  funext k
  exact Fin.lastCases hax htrans k

end BoltzmannNonuniqueness.JetLattice

namespace BoltzmannNonuniqueness.JetCopyDatum

theorem nearby_main_regions_same_lattice {s₀ η r : ℝ} {N : ℕ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η)
    {i j : JetLattice.Label} {z w : Published.SpaceTime}
    (hz : z ∈ mainCoreRegion s₀ η r N i) (hw : w ∈ mainCoreRegion s₀ η r N j)
    (hnear : ‖r • z.2-r • w.2‖ < 1/4) : i.lattice = j.lattice :=
  JetLattice.nearby_enlargements_same_lattice hs₀ hsmax hη hz.2.1 hw.2.1 hz.2.2 hw.2.2 hnear

end BoltzmannNonuniqueness.JetCopyDatum

end

end OAI
