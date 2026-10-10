import OAI.Analysis.CircleDomains.Rigidity.MaskedModelTerminalBranches
import OAI.Analysis.CircleDomains.Rigidity.AssembledMaskedModel
import OAI.Analysis.CircleDomains.Transfer.TerminalTransfer

namespace OAI

/-! Actual quotient branch neighborhoods induce the physical terminal
collars needed by the common masked model. -/

open Set Function Filter
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

theorem marked_model_terminal_control
    {I J : Type*} [Fintype I] [Fintype J] {n N : ℕ}
    {G B : Set Sphere} (hG : IsOpen G) {π : Sphere → Sphere} (hπ : Continuous π)
    {p : I → Sphere} {O : I → Set Sphere}
    (D : PhysicalTerminalDisks G π B p O) (H : J → ℂ ≃ₜ ℂ)
    (hTH : ∀ i j, Disjoint (closure (jordanInterior (D.H i))) (closure (jordanInterior (H j))))
    {K : Set (ℝ × ℝ)} (Mask : Fin n → Set Sphere)
    {f : Fin n → (ℝ × ℝ) → UnitAddCircle} {χ : (ℝ × ℝ) → ℝ}
    {θ : Fin n → ℝ} {ε : ℝ}
    (Q : MaskedModelData D.H H (realChartDomain G) K (fun l => physicalMask π (Mask l)) f χ N θ ε)
    (hTC : ∀ i, Disjoint (closedTerminalCap (D.H i)) (cutoffCore χ))
    (V : I → Set Sphere) (hV : ∀ i, IsOpen (V i)) (hOV : ∀ i, O i ⊆ V i)
    (u : I → Fin n → Sphere → ℝ) (S : Fin n → Finset I) (a : I → Fin n → ℝ)
    (hVM : ∀ l i, i ∈ S l → V i ⊆ Mask l)
    (hu : ∀ l i, i ∈ S l → ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => u i l (π (Complex.equivRealProdCLM.symm x : Sphere)))
      (realChartDomain G ∩ realChartDomain (π ⁻¹' V i)))
    (hproj : ∀ l i, i ∈ S l → ∀ x,
      x ∈ realChartDomain G ∩ realChartDomain (π ⁻¹' V i) →
      (u i l (π (Complex.equivRealProdCLM.symm x : Sphere)) : UnitAddCircle) = f l x)
    (ha : ∀ l i, i ∈ S l → 0 ≤ a i l)
    (hbound : ∀ l i, i ∈ S l → ∀ x ∈ frontier (jordanInterior (D.H i)),
      ∀ y ∈ frontier (jordanInterior (D.H i)),
      |shiftedStaircase (reciprocalGridStep N)
          (staircaseWidth (reciprocalGridStep N) Q.widthIndex) (θ l) (u i l (π (x : Sphere))) -
        shiftedStaircase (reciprocalGridStep N)
          (staircaseWidth (reciprocalGridStep N) Q.widthIndex) (θ l) (u i l (π (y : Sphere)))| ≤
          a i l + 4 * reciprocalGridStep N)
    {η : ℝ} (hsmall : reciprocalGridStep N * Real.sqrt (Fintype.card I : ℝ) < η) :
    ∃ (E : I → Set (ℝ × ℝ)) (w : I → Fin n → (ℝ × ℝ) → ℝ),
      (∀ i, IsOpen (E i) ∧ frontier (realJordanInterior (D.H i)) ⊆ E i) ∧
      (∀ l i, i ∈ S l → ContDiffOn ℝ ∞ (w i l) (E i) ∧
        ∀ᶠ x in 𝓝ˢ (frontier (realJordanInterior (D.H i))), (w i l x : UnitAddCircle) = Q.functions l x) ∧
      ∀ l, Real.sqrt (∑ i ∈ S l,
        max (Metric.diam (w i l '' frontier (realJordanInterior (D.H i))) - a i l) 0 ^ 2) < 4 * η := by
  let E (i : I) := (realChartDomain G ∩ realChartDomain (π ⁻¹' V i)) ∩ interior {x | χ x = 1}
  have hE (i : I) : IsOpen (E i) :=
    ((isOpen_realChartDomain hG).inter (isOpen_realChartDomain ((hV i).preimage hπ))).inter isOpen_interior
  have hDE (i : I) : frontier (realJordanInterior (D.H i)) ⊆ E i := by
    rw [frontier_realJordanInterior]
    rintro x ⟨z, hz, rfl⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa only [realChartDomain, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using
        (D.frontier_good i z hz).1
    · simpa only [realChartDomain, mem_preimage, ContinuousLinearEquiv.symm_apply_apply] using
        hOV i (D.closure_subset i (frontier_subset_closure hz))
    · exact boundary_in_one_plateau_of_disjoint_cutoffCore (D.H i) χ (hTC i) z hz
  obtain ⟨w, hw, hexcess⟩ := Q.terminal_branches hTH E hE hDE
    (fun i l x => u i l (π (Complex.equivRealProdCLM.symm x : Sphere))) S a
    (fun l i hi => (hu l i hi).mono inter_subset_left)
    (fun l i hi x hx => hVM l i hi hx.1.2)
    (fun l i hi x hx => hproj l i hi x hx.1)
    (fun i x hx => (show x ∈ {y | χ y = 1} from interior_subset hx.2)) ha
    (fun l i hi x hx y hy => by
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hbound l i hi x hx y hy) hsmall
  exact ⟨E, w, fun i => ⟨hE i, hDE i⟩, hw, hexcess⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
