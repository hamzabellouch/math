import OAI.Analysis.CircleDomains.Rigidity.MaskedStageTerminalLifts
import OAI.Analysis.CircleDomains.Modulus.NonsingularStokesBudget

namespace OAI

/-! Apply finite Stokes to an actual masked coordinate stage. The real
terminal lifts and their complete excess budget are derived from that
stage, with the singular terminal omitted. -/

open Set Function Filter MeasureTheory Metric
open scoped Topology BigOperators
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MaskedCoordinateStage.stokes_bound
    (hgreen : FiniteCircleGreenFormula)
    {S : Type*} {n : ℕ} {G U : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {C : Fin n → MaskedCoordinateData G U π σ}
    {Flag : Set S} {O : S → Set Sphere} {K₀ : Set (ℝ × ℝ)} {ε ρ : ℝ} {k₀ : ℕ}
    (T : MaskedCoordinateStage C Flag O K₀ ε ρ k₀) (hσ : Injective σ) (l : Fin n)
    (a : TerminalComponentAssignment T.terminals.H T.model.forward T.model.domain)
    (c : T.indices → ℂ) (r : T.indices → ℝ) (hr : ∀ s, 0 ≤ r s)
    (hd : Pairwise (Disjoint on fun s => closedBall (c s) (r s)))
    (hext : ((↑) : ℂ → Sphere) ⁻¹' T.model.domain = (⋃ s, closedBall (c s) (r s))ᶜ)
    (htarget : ∀ s, ((↑) : ℂ → Sphere) '' closedBall (c s) (r s) ⊆
      connectedComponentIn T.model.domainᶜ (a.point s))
    (m : ℕ) (κ : Fin m → T.indices) (hκ : Injective κ) (b : Fin m)
    (hsing : (κ b : S) = (C l).singular) (hmask : ∀ j, σ (κ j) ∈ (C l).mask)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : PositiveJordanParametrization H γ)
    (hin : ∀ j, closedBall (c (κ j)) (r (κ j)) ⊆ jordanInterior H)
    (W : Set ℂ) (hW : IsOpen W)
    (hsub : closure (jordanInterior H) \ ⋃ j, closedBall (c (κ j)) (r (κ j)) ⊆ W)
    (hsmooth : SmoothCircleOn (fun z : ℂ => sphereRealFunction (T.model.functions l)
      (T.model.inverse (z : Sphere))) W)
    {L : ℝ} (hL : 0 ≤ L) (hbounded : jordanInterior H ⊆ closedBall 0 L)
    (henergy : MemLp (circleFDeriv (fun z : ℂ => sphereRealFunction (T.model.functions l)
      (T.model.inverse (z : Sphere)))) 2
      (volume.restrict (jordanInterior H \ ⋃ j, closedBall (c (κ j)) (r (κ j))))) :
    |circleFormIntegral (fun z => infDist z (closedBall (c (κ b)) (r (κ b))))
      (fun z : ℂ => sphereRealFunction (T.model.functions l) (T.model.inverse (z : Sphere))) γ| ≤
      Real.sqrt Real.pi * L * Real.sqrt
        (∫ z in jordanInterior H \ ⋃ j, closedBall (c (κ j)) (r (κ j)),
          ‖circleFDeriv (fun z : ℂ => sphereRealFunction (T.model.functions l)
            (T.model.inverse (z : Sphere))) z‖ ^ 2) +
      2 * Real.pi * L *
        (Real.sqrt (∑' s : {s : S // s ≠ (C l).singular},
          ((C l).upper s - (C l).lower s) ^ 2) + ε) := by
  classical
  let : Fintype T.indices := T.indices_finite.fintype
  have hne (j : Fin m) (hj : j ≠ b) : σ (κ j) ≠ σ (C l).singular := by
    intro he
    apply hj
    apply hκ
    apply Subtype.ext
    exact (hσ he).trans hsing.symm
  choose V hV hboundary hcont hproj hosc using
    (fun j : {j : Fin m // j ≠ b} => T.nonsingular_terminal_lift l (κ j) (hmask j) (hne j j.property))
  let V' (j : Fin m) := if h : j ≠ b then V ⟨j, h⟩ else univ
  let A (j : Fin m) := Metric.diam
    (T.terminal_branch (κ j) l '' frontier (realJordanInterior (T.terminals.H (κ j))))
  let P := {s : T.indices // σ s ∈ (C l).mask ∧ σ s ≠ σ (C l).singular}
  let label : {j : Fin m // j ≠ b} → P := fun j => ⟨κ j, hmask j, hne j j.property⟩
  have hlabel : Injective label := by
    intro i j he
    apply Subtype.ext
    exact hκ (congrArg Subtype.val he)
  have hexc : Real.sqrt (∑ j : {j : Fin m // j ≠ b},
      max (A j - ((C l).upper (κ j) - (C l).lower (κ j))) 0 ^ 2) ≤ ε := by
    have h := finite_label_band_norm_le label hlabel
      (fun s : P => max (Metric.diam (T.terminal_branch s l ''
        frontier (realJordanInterior (T.terminals.H s))) -
          ((C l).upper s - (C l).lower s)) 0)
      (hasSum_fintype _).summable
    exact h.trans (T.terminal_excess l).le
  have hb := assigned_model_stokes_nonsingular_bound hgreen a T.model.equivalence
    c r hr hd hext htarget m κ hκ b H γ hγ hin W hW hsub
    (sphereRealFunction (T.model.functions l)) hsmooth hL hbounded henergy V'
    (fun j => sphereRealFunction (T.terminal_branch (κ j) l))
    (fun j hj => by simpa only [V', dite_eq_left hj] using hV ⟨j, hj⟩)
    (fun j hj => by simpa only [V', dite_eq_left hj] using hboundary ⟨j, hj⟩)
    (fun j hj => by simpa only [V', dite_eq_left hj] using hcont ⟨j, hj⟩)
    (fun j hj => by simpa only [V', dite_eq_left hj] using hproj ⟨j, hj⟩)
    A (fun j hj => hosc ⟨j, hj⟩) (fun s : T.indices => (s : S)) Subtype.val_injective
    (fun s => (C l).upper s - (C l).lower s) (C l).width_summable (C l).width_nonneg hexc
  rw [hsing] at hb
  exact hb

end CircleDomainRigidity.FiniteTransfer

end

end OAI
