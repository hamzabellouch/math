import OAI.Analysis.CircleDomains.Modulus.AssignedStokesBudget

namespace OAI

/-! The finite Stokes bound consumes only nonsingular terminal excess.
No oscillation or real lift is required at the distinguished terminal. -/

open Set Function MeasureTheory Metric
open scoped Topology BigOperators
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem assigned_model_stokes_nonsingular_bound
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
      (∑ j : {j : Fin n // j ≠ b}, max (A j - band (label (κ j))) 0 ^ 2) ≤ η) :
    |circleFormIntegral (fun z => infDist z (closedBall (c (κ b)) (r (κ b))))
      (fun z : ℂ => w (fi (z : Sphere))) γ| ≤
      Real.sqrt Real.pi * L * Real.sqrt
        (∫ z in jordanInterior H \ ⋃ j, closedBall (c (κ j)) (r (κ j)),
          ‖circleFDeriv (fun z : ℂ => w (fi (z : Sphere))) z‖ ^ 2) +
      2 * Real.pi * L *
        (Real.sqrt (∑' s : {s : S // s ≠ label (κ b)}, band s ^ 2) + η) := by
  classical
  let A' (j : Fin n) := if j = b then band (label (κ j)) else A j
  have hAe (j : Fin n) (hj : j ≠ b) : A' j = A j := ite_eq_right hj
  have heq : (∑ j, max (A' j - band (label (κ j))) 0 ^ 2) =
      ∑ j : {j : Fin n // j ≠ b}, max (A j - band (label (κ j))) 0 ^ 2 := by
    rw [sum_off_distinguished b (fun j : Fin n => max (A j - band (label (κ j))) 0 ^ 2)]
    calc
      _ = ∑ j ∈ Finset.univ.erase b, max (A' j - band (label (κ j))) 0 ^ 2 := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ b)]
        simp only [A', ite_eq_left rfl, sub_self, max_self, zero_pow (by norm_num : 2 ≠ 0), add_zero]
      _ = _ := Finset.sum_congr rfl (fun j hj => by rw [hAe j (Finset.mem_erase.mp hj).1])
  apply assigned_model_stokes_band_bound hgreen a hf c r hr hd hext htarget n κ hκ b H γ hγ
    hin O hO hsub w hu hL hbounded henergy U v hU hboundary hv hproj A'
    (fun j hj => by simpa only [hAe j hj] using hA j hj) label hlabel band hband hb
  simpa only [heq] using hexcess

end CircleDomainRigidity

end

end OAI
