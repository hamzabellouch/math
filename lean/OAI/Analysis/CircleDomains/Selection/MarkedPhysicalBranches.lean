import OAI.Analysis.CircleDomains.Topology.MarkedBranchNeighborhoods
import OAI.Analysis.CircleDomains.Topology.CutoffCore
import OAI.Analysis.CircleDomains.Topology.CircleLifts

namespace OAI

/-! The selected marked bands determine common physical branch
neighborhoods. Smoothness, projection, and the original widths refer to
the same chosen branches. -/

open Set Function Filter Classical
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem exists_marked_physical_branches
    {n : ℕ} {S : Type*} (L : Fin n → Type*)
    (U G : Set Sphere) (π : Sphere → Sphere)
    (M : Fin n → Set Sphere) (hM : ∀ l, IsClosed (M l))
    (hboundary : ∀ l, frontier (M l) ⊆ U)
    (σ : S → Sphere) (hσ : ∀ s, σ s ∉ U) (singular : Fin n → Sphere)
    (P : ∀ l, L l → Set Sphere) (hP : ∀ l i, IsOpen (P l i))
    (v : ∀ l, L l → Sphere → ℝ) (B : ∀ l, L l → ℝ)
    (hbound : ∀ l i x, |v l i x| ≤ B l i)
    (a b : Fin n → S → ℝ)
    (hband : ∀ s l, σ s ∈ M l → σ s ≠ singular l → ∃ i : L l,
      σ s ∈ P l i ∧ a l s = liminf (v l i) (𝓝[U] (σ s)) ∧
        b l s = limsup (v l i) (𝓝[U] (σ s)))
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hv : ∀ l i, ContDiffOn ℝ ∞
      (fun x : ℝ × ℝ => v l i (π (Complex.equivRealProdCLM.symm x : Sphere)))
      (realChartDomain G ∩ realChartDomain (π ⁻¹' P l i)))
    (hproj : ∀ l i x, x ∈ realChartDomain G ∩ realChartDomain (π ⁻¹' P l i) →
      (v l i (π (Complex.equivRealProdCLM.symm x : Sphere)) : UnitAddCircle) = f l x) :
    ∃ (N : S → Set Sphere) (u : S → Fin n → Sphere → ℝ) (C : S → Fin n → ℝ),
      (∀ s, IsOpen (N s) ∧ σ s ∈ N s) ∧
      (∀ s l, σ s ∈ M l → N s ⊆ interior (M l)) ∧
      (∀ s l, σ s ∉ M l → Disjoint (N s) (M l)) ∧
      (∀ s l x, |u s l x| ≤ C s l) ∧
      (∀ s l, σ s ∈ M l → σ s ≠ singular l →
        limsup (u s l) (𝓝[U ∩ N s] (σ s)) -
          liminf (u s l) (𝓝[U ∩ N s] (σ s)) = b l s - a l s) ∧
      (∀ s l, σ s ∈ M l → σ s ≠ singular l → ContDiffOn ℝ ∞
        (fun x : ℝ × ℝ => u s l (π (Complex.equivRealProdCLM.symm x : Sphere)))
        (realChartDomain G ∩ realChartDomain (π ⁻¹' N s))) ∧
      (∀ s l, σ s ∈ M l → σ s ≠ singular l → ∀ x,
        x ∈ realChartDomain G ∩ realChartDomain (π ⁻¹' N s) →
        (u s l (π (Complex.equivRealProdCLM.symm x : Sphere)) : UnitAddCircle) = f l x) := by
  obtain ⟨N, u, C, hN, hNM, hdisj, hb, hchosen, hwidth⟩ :=
    exists_marked_branch_neighborhoods L U M hM hboundary σ hσ singular P hP v B hbound a b hband
  refine ⟨N, u, C, hN, hNM, hdisj, hb, hwidth, ?_, ?_⟩
  · intro s l hs hne
    obtain ⟨i, hNP, hu⟩ := hchosen s l hs hne
    rw [hu]
    apply (hv l i).mono
    intro x hx
    exact ⟨hx.1, hNP hx.2⟩
  · intro s l hs hne x hx
    obtain ⟨i, hNP, hu⟩ := hchosen s l hs hne
    rw [hu]
    exact hproj l i x ⟨hx.1, hNP hx.2⟩

end CircleDomainRigidity

end

end OAI
