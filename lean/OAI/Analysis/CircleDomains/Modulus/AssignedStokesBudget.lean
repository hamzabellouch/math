import OAI.Analysis.CircleDomains.Modulus.DistinguishedStokesBudget

namespace OAI

/-! The actual finite model obeys the countable-band Stokes bound with
its singular mark removed. Disjointness and containment of its round
holes provide the radius budget; the source collar branches provide
the boundary oscillations. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology BigOperators

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem assigned_model_stokes_band_bound
    (hgreen : FiniteCircleGreenFormula)
    {I S : Type*} [Fintype I] {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    (c : I → ℂ) (r : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hext : ((↑) : ℂ → Sphere) ⁻¹' V = (⋃ i, closedBall (c i) (r i))ᶜ)
    (htarget : ∀ i, ((↑) : ℂ → Sphere) '' closedBall (c i) (r i) ⊆
      connectedComponentIn Vᶜ (a.point i))
    (n : ℕ) (κ : Fin n → I) (hκ : Injective κ) (b : Fin n)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : PositiveJordanParametrization H γ)
    (hin : ∀ j, closedBall (c (κ j)) (r (κ j)) ⊆ jordanInterior H)
    (O : Set ℂ) (hO : IsOpen O)
    (hsub : (closure (jordanInterior H) \ ⋃ j, closedBall (c (κ j)) (r (κ j))) ⊆ O)
    (w : Sphere → UnitAddCircle)
    (hu : SmoothCircleOn (fun z : ℂ => w (fi (z : Sphere))) O)
    {L : ℝ} (hL : 0 ≤ L) (hbounded : jordanInterior H ⊆ closedBall 0 L)
    (henergy : MemLp (circleFDeriv (fun z : ℂ => w (fi (z : Sphere)))) 2
      (volume.restrict (jordanInterior H \ ⋃ j, closedBall (c (κ j)) (r (κ j)))))
    (U : Fin n → Set Sphere) (v : Fin n → Sphere → ℝ)
    (hU : ∀ j ≠ b, IsOpen (U j))
    (hboundary : ∀ j ≠ b, ((↑) : ℂ → Sphere) '' frontier (jordanInterior (T (κ j))) ⊆ U j)
    (hv : ∀ j ≠ b, ContinuousOn (v j) (U j))
    (hproj : ∀ j ≠ b, ∀ x ∈ U j, (v j x : UnitAddCircle) = w x)
    (A : Fin n → ℝ) (hA : ∀ j ≠ b, ∀ x ∈ frontier (jordanInterior (T (κ j))),
      ∀ y ∈ frontier (jordanInterior (T (κ j))), |v j (x : Sphere) - v j (y : Sphere)| ≤ A j)
    (label : I → S) (hlabel : Injective label)
    (band : S → ℝ) (hband : Summable (fun s => band s ^ 2)) (hb : ∀ s, 0 ≤ band s)
    {η : ℝ} (hexcess : Real.sqrt
      (∑ j, max (A j - band (label (κ j))) 0 ^ 2) ≤ η) :
    |circleFormIntegral (fun z => infDist z (closedBall (c (κ b)) (r (κ b))))
      (fun z : ℂ => w (fi (z : Sphere))) γ| ≤
      Real.sqrt Real.pi * L * Real.sqrt
        (∫ z in jordanInterior H \ ⋃ j, closedBall (c (κ j)) (r (κ j)),
          ‖circleFDeriv (fun z : ℂ => w (fi (z : Sphere))) z‖ ^ 2) +
      2 * Real.pi * L *
        (Real.sqrt (∑' s : {s : S // s ≠ label (κ b)}, band s ^ 2) + η) := by
  classical
  have hnonneg (j : Fin n) (hj : j ≠ b) : 0 ≤ A j := by
    obtain ⟨x, hx⟩ := (isConnected_frontier_jordanInterior (T (κ j))).nonempty
    simpa only [sub_self, abs_zero] using hA j hj x hx x hx
  have hradius : (∑ j, r (κ j) ^ 2) ≤ L ^ 2 :=
    sum_radii_sq_le_of_disjoint_closed_disks (c ∘ κ) (r ∘ κ)
      (fun j => hr (κ j)) hL (fun j k hjk => hd (fun h => hjk (hκ h)))
      (fun j => (hin j).trans hbounded)
  exact circle_stokes_bound_off_distinguished (label ∘ κ) (hlabel.comp hκ) b band hband
    (r ∘ κ) A hnonneg hb hL hradius hexcess
    (assigned_model_stokes_bound hgreen a hf c r hr hd hext htarget n κ hκ b H γ hγ
      hin O hO hsub w hu hL hbounded henergy U v hU hboundary hv hproj A hA)

end CircleDomainRigidity

end

end OAI
