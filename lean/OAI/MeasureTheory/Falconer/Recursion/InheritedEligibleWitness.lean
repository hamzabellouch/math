import OAI.MeasureTheory.Falconer.Fourier.InheritedSymbolSupport
import OAI.MeasureTheory.Falconer.Angular.AngularLabelEligibility
import OAI.MeasureTheory.Falconer.Angular.AngularEnergyDropping

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem uniform_inheritedCircleSymbol_good {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset (ι)) (d : ι → PolicyDescriptor) (k : ι → ℕ),
    ∀ Q : DyadicSquare, Q.side = 1 → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (i : ℕ) (h : Plane → ℂ),
    ∀ e ∈ S, ValidDescriptor N (d e) →
    ∀ A ∈ occupiedAnchorPaths Q ρ (descriptorAnchor (d e)),
    ∀ x ∈ (Q.descendant A).carrier, ∀ dir,
    inheritedCircleSymbol S d k Q ρ m N lam sig J i h x dir ≠ 0 →
      dir ∈ descriptorGoodSet Q ρ m N lam sig J (i+1) A (d e) := by
  obtain ⟨N₀,hgood⟩ := uniform_inheritedMaskProduct_support hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ι inst S d k Q hQ ρ m lam i h e he hd A hA x hx dir hn
  have hz : inheritedMaskProduct S d k Q ρ m N lam sig J i (fun _ => x) (sourceAngle dir) ≠ 0 := by
    intro hzero
    exact hn (by simp only [inheritedCircleSymbol,hzero,Complex.ofReal_zero,mul_zero])
  have hsup := hgood N hN S d k Q hQ ρ m lam i (fun _ => x) 0 e he hd A hA hx
  simp only [iteratedDeriv_zero] at hsup
  have hh := hsup (subset_closure hz)
  simpa only [mem_preimage,sourceUnitDirection_sourceAngle] using hh

theorem uniform_inherited_eligible_good_witness {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (d : ι → PolicyDescriptor) (k : ι → ℕ),
    ∀ Q : DyadicSquare, Q.side = 1 → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (i : ℕ) (h : Plane → ℂ),
    ∀ e ∈ S, ValidDescriptor N (d e) →
    ∀ A ∈ occupiedAnchorPaths Q ρ (descriptorAnchor (d e)), ∀ n j : ℕ,
    AngularLabelEligible ρ (Q.descendant A).carrier
      (inheritedCircleSymbol S d k Q ρ m N lam sig J i h) n j →
    ∃ dir ∈ tsupport (circleAngularBin n j),
      dir ∈ descriptorGoodSet Q ρ m N lam sig J (i+1) A (d e) := by
  obtain ⟨N₀,hgood⟩ := uniform_inheritedCircleSymbol_good hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ι inst S d k Q hQ ρ m lam i h e he hd A hA n j hel
  exact eligible_label_good_direction (Q.descendant A).measurable hel _
    (hgood N hN S d k Q hQ ρ m lam i h e he hd A hA)

end PlanarFalconer

end OAI
