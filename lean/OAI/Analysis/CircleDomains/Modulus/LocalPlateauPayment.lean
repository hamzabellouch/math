import OAI.Analysis.CircleDomains.Modulus.LocalRetainedBarrier
import OAI.Analysis.CircleDomains.Selection.LocalPlateauContour

namespace OAI

/-! A local quotient plateau, with zero value on the source anchor, pays for the fixed positive
transverse width near a protrusion. The inner contour is selected inside Lean. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer.RealTargetEnd

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {A : AssignedRealModelLimit M} {q : Sphere}
  (E : RealTargetEnd A q)

theorem local_plateau_norm_bound
    (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen G) (hε : Tendsto ε atTop (𝓝 0))
    (hπ : Continuous π)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hq : q ∈ Gᶜ) (l : ℕ) {U : Set Sphere} (hU : IsOpen U) (hqU : π q ∈ U)
    (hone : ∀ x ∈ U ∩ d.source, d.coordinate l x = 1)
    (H : ℂ ≃ₜ ℂ) (hHG : closure (jordanInterior H) ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    (hzero : ∀ z ∈ closure (jordanInterior H), d.physical l (Complex.equivRealProdCLM z) = 0)
    (c : ℂ) (δ : ℝ) (hanchor : closedBall c δ ⊆ A.function '' jordanInterior H)
    {Q : Set ℂ} (hQ : IsCompact Q) (hQE : Q ⊆ E.plane)
    {W : Set ℂ} (hW : IsClosed W) (hWconvex : Convex ℝ W)
    (hQW : Q ⊆ W) (hBW : closedBall c δ ⊆ W)
    {P : Set ℂ} (hP : IsCompact P) (hPG : P ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    (hPW : Disjoint (A.function '' P) W)
    (rot : Circle) {J : Set ℝ} (hJ : MeasurableSet J)
    (hprojection : J ⊆ (fun z => ((rotation rot).symm z).im) '' Q ∩
      Ioo (((rotation rot).symm c).im - δ) (((rotation rot).symm c).im + δ))
    {R : ℝ} (hR : 3 * M.radius ≤ R) (hWR : W ⊆ closedBall 0 R) :
    (volume J).toReal ≤ ((Real.sqrt Real.pi + 2) * R) *
      (Real.sqrt (∫ x in realChartDomain G \ (Complex.equivRealProdCLM '' P),
        gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x) +
       Real.sqrt (∑' s, (d.upper l s - d.lower l s) ^ 2)) := by
  have hKA : ((↑) : ℂ → Sphere) '' closedBall c δ ⊆ extendAtInfinity A.function '' G := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨p, hp, he⟩ := hanchor hz
    exact ⟨p, hHG (subset_closure hp), by simp only [extendAtInfinity_coe, he]⟩
  obtain ⟨k, hOne, hd⟩ := E.exists_plateau_contour_avoiding_anchor hπ hr hq l hU hqU hone
    (isCompact_closedBall c δ) hKA
  have hpay := E.local_barrier_payment hsch harea hG hε k l hOne H hHG hzero c δ hanchor hd
    hQ (hQE.trans (E.plane_inside k)) hW hWconvex hQW hBW hP hPG hPW rot hJ hprojection hR hWR
  apply hpay.trans
  have hR0 : 0 ≤ R := (mul_nonneg (by norm_num) M.radius_pos.le).trans hR
  have ha := Real.sqrt_nonneg (∫ x in realChartDomain G \ (Complex.equivRealProdCLM '' P),
    gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x)
  have hb := Real.sqrt_nonneg (∑' s, (d.upper l s - d.lower l s) ^ 2)
  have hp := Real.sqrt_nonneg Real.pi
  nlinarith [mul_nonneg hR0 ha, mul_nonneg hR0 hb, mul_nonneg hp (mul_nonneg hR0 hb)]

end CircleDomainRigidity.FiniteTransfer.RealTargetEnd

end

end OAI
