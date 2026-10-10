import OAI.Analysis.CircleDomains.Sobolev.AnnulusStokes
import OAI.Analysis.CircleDomains.Topology.SimultaneousRoundCollars

namespace OAI

/-! Stokes for selected holes of an actual finite model. The real collar
branches and their bounds are transported from the corresponding source
terminal boundaries. Holes outside the chosen Jordan mask need no branch. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology BigOperators

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem assigned_model_stokes_bound
    (hgreen : FiniteCircleGreenFormula)
    {I : Type*} [Fintype I] {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
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
      ∀ y ∈ frontier (jordanInterior (T (κ j))), |v j (x : Sphere) - v j (y : Sphere)| ≤ A j) :
    |circleFormIntegral (fun z => infDist z (closedBall (c (κ b)) (r (κ b))))
      (fun z : ℂ => w (fi (z : Sphere))) γ| ≤
      Real.sqrt Real.pi * L * Real.sqrt
        (∫ z in jordanInterior H \ ⋃ j, closedBall (c (κ j)) (r (κ j)),
          ‖circleFDeriv (fun z : ℂ => w (fi (z : Sphere))) z‖ ^ 2) +
      ∑ j ∈ Finset.univ.erase b, 2 * Real.pi * r (κ j) * A j := by
  classical
  apply finite_annulus_stokes_bound hgreen H γ hγ n (c ∘ κ) (r ∘ κ) (fun j => hr (κ j))
    (fun j k hjk => hd (fun he => hjk (hκ he))) hin O hO hsub _ hu hL hbounded henergy b A
  · intro j hj
    obtain ⟨x, hx⟩ := (isConnected_frontier_jordanInterior (T (κ j))).nonempty
    simpa only [sub_self, abs_zero] using hA j hj x hx x hx
  · intro ε hε
    have hex (j : Fin n) : ∃ δ > 0, ∀ ρ ∈ Ioo (0 : ℝ) δ, j ≠ b →
        Continuous (roundCollarRealLift fi (v j) (c (κ j)) (r (κ j) + ρ)) ∧
        (∀ t, (roundCollarRealLift fi (v j) (c (κ j)) (r (κ j) + ρ) t : UnitAddCircle) =
          w (fi (unitCircleParam (c (κ j)) (r (κ j) + ρ) t : Sphere))) ∧
        roundCollarRealLift fi (v j) (c (κ j)) (r (κ j) + ρ) 1 =
          roundCollarRealLift fi (v j) (c (κ j)) (r (κ j) + ρ) 0 ∧
        ∀ t ∈ Icc (0 : ℝ) 1, |roundCollarRealLift fi (v j) (c (κ j)) (r (κ j) + ρ) t -
          roundCollarRealLift fi (v j) (c (κ j)) (r (κ j) + ρ) 0| ≤ A j + ε := by
      by_cases hj : j = b
      · exact ⟨1, zero_lt_one, fun _ _ hne => (hne hj).elim⟩
      · obtain ⟨δ, hδ, hvalid⟩ := a.exists_round_collar_lifts hf c r hr hd hext (κ j) (htarget (κ j))
          (hU j hj) (hboundary j hj) (v j) (hv j hj) w (hproj j hj) (A j) (hA j hj) hε
        exact ⟨δ, hδ, fun ρ hρ _ => hvalid ρ ⟨hρ.1, hρ.2.le⟩⟩
    choose d hdpos hvalid using hex
    obtain ⟨δ, hδ, hδle⟩ := exists_common_positive_bound d hdpos
    refine ⟨δ, hδ, ?_⟩
    intro ρ hρ
    exact ⟨fun j => roundCollarRealLift fi (v j) (c (κ j)) (r (κ j) + ρ),
      fun j hj => hvalid j ρ ⟨hρ.1, hρ.2.trans_le (hδle j)⟩ hj⟩

end CircleDomainRigidity

end

end OAI
