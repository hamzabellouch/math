import OAI.NumberTheory.Ostmann.Arithmetic.MovingDerivedLiveProductStep
import OAI.NumberTheory.Ostmann.Arithmetic.MovingCompensationFrequency
import OAI.NumberTheory.Ostmann.Arithmetic.MovingAmplitudeNext
import OAI.NumberTheory.Ostmann.Arithmetic.MovingRecursiveTemplateCaps
import OAI.NumberTheory.Ostmann.Arithmetic.MovingOriginalLeafMultiplier

namespace OAI

/-! # The actual product and integer-frequency constructions give the transfer step -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- The cap, monotonicity and frequency-scale hypotheses are discharged by
one and the same terminal product and compensation-cell construction. -/
theorem movingTemplatePrimeAmplitude_step_constructed_live {σ J : Type} [Fintype σ]
    (value : σ → ℕ) (hvalue : ∀ a, (value a).Prime)
    (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ)
    (q : J → ℕ) [∀ i, Fact (q i).Prime]
    (F : {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (hF : ∀ {n} (T : MovingSlotData σ n), F T 0 = 0)
    (g : ∀ i, ZMod (q i) → ℂ) (Dq : ∀ i, (ZMod (q i))ˣ) (S : Finset J)
    (ψ : SchwartzMap ℝ ℂ) (X lo hi W : ℝ) (hX : 0 < X)
    (hwindow : X * hi ≤ Real.exp W)
    (φ : ℝ → ℝ) (G c : ℕ → ℝ) (hout : ∀ t, 1 ≤ |t| → φ t = 0)
    (hμlower : ∀ j x, μ j x ≠ 0 → Real.exp (c j - 1) ≤ (value x : ℝ))
    (n r m : ℕ) (Y reserveMass : ℝ) (hm : 64 ≤ reserveMass) (hY : Y ≤ W)
    (hVeq : V = movingProductNaturalCutoff (movingCellPivotExponent G c) W Y reserveMass)
    (hbudget : ∀ j, 2 * movingCellPivotExponent G c j ≤
      movingProductExponent (movingCellPivotExponent G c) W j)
    (hpositive : 0 ≤ movingProductExponent (movingCellPivotExponent G c) W n -
      movingCellPivotExponent G c n)
    (Pg I : Finset ℕ) (hPg : ∀ p ∈ Pg, p.Prime) (hPI : Pg ⊆ I)
    (hI : ∀ p ∈ I, 0 < p) (hφ : ∀ x, 0 ≤ φ x)
    (hpos : 0 < smoothGiantMass Pg φ (G (n + 1)))
    (hμ : ∀ a, 0 ≤ μ n a) (hμmass : ∑ a, μ n a = 1)
    (ν : MovingRegularSlot n r m → σ → ℝ)
    (sets : ∀ q : ℕ, Finset (ZMod q))
    (hsets : ∀ a, (sets (value a)).Nonempty)
    (hcard : ∀ a, (sets (value a)).card < value a)
    (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (hgiant : ∀ q : Pg, ∀ x, ggiant q (-x) = conj (ggiant q x))
    (H : ℕ)
    (hHeq : H = ⌈Real.exp (movingProductExponent (movingCellPivotExponent G c) W n -
      movingCellPivotExponent G c n)⌉₊)
    (hIlower : ∀ p ∈ I, Real.exp (G (n + 1) - 1) ≤ (p : ℝ))
    (hlarge : ∀ (q : Pg) (y : MovingRegularSlot n r m → σ),
      (∏ i, ν i (y i)) ≠ 0 → ∀ ℓ, ℓ.Prime → ℓ ∣ (q : ℕ) * (∏ i, value (y i)) → V (n + 1) < ℓ)
    (hvg : ∀ q : Pg, V (n + 1) < (q : ℕ))
    (hφsupport : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hchild : V n ≤ childBound (n + 1))
    (hgap : ∀ XR : Pg, ∀ right : MovingRegularSlot n r m → σ, (∏ i, ν i (right i)) ≠ 0 →
      2 * pivotBound (n + 1) * childBound (n + 1) < (XR : ℕ) * ∏ i, value (right i))
    (hcomp : ∀ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) ≠ 0 →
      (∀ p ∈ I, p * (∏ i, value (u i)) ≤ pivotBound (n + 1)) ∧
      (∀ q, q.Prime → q ∣ ∏ i, value (u i) → childBound (n + 1) < q)) :
    let ρ := smoothGiantPrior Pg φ (G (n + 1))
    let greg := normalizedResidueFamily sets
    Real.exp (-smoothGiantLogNormalizer Pg φ (G (n + 1))) *
      ‖movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
        (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n (4 + r) m
        Pg ρ (movingTemplateRestoredPrior n r m (μ n) ν) greg ggiant favorable‖ ^ 2 ≤
      movingAmplitudeDiagonal value outside μ childBound pivotBound V
        (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G n r m Pg I
        ρ ν greg ggiant favorable +
      ‖movingTemplatePrimeAmplitude value outside μ childBound pivotBound V
        (movingOriginalLeaf value q F g Dq S ψ X lo hi) φ G (n + 1) r m
        Pg ρ (movingTemplateDoubledPrior n r m ν) greg ggiant favorable‖ := by
  have hV : Monotone V := by
    rw [hVeq]
    exact movingProductNaturalCutoff_monotone (movingCellPivotExponent G c) W Y reserveMass hbudget
  have hcap : ⌈Real.exp (movingProductExponent (movingCellPivotExponent G c) W n -
      movingCellPivotExponent G c n)⌉₊ ≤ H := by rw [hHeq]
  have hscale (u : TreeLeafIndex n × Fin 4 → σ) (hu : (∏ i, μ n (u i)) ≠ 0)
      (p : ℕ) (hp : p ∈ I) : 2 * V n * H ≤ V (n + 1) * (p * ∏ i, value (u i)) := by
    rw [hVeq, hHeq]
    exact movingProductNaturalCutoff_compensation_scale value μ G c hμlower W Y reserveMass
      hm hY hbudget n hpositive u hu p (hIlower p hp)
  exact movingTemplatePrimeAmplitude_step_of_live_cells value hvalue outside μ childBound pivotBound V hV
    q F hF g Dq S ψ X lo hi W hX hwindow φ G c hout hμlower n r m Pg I hPg hPI hI hφ
    hpos hμ hμmass ν sets hsets hcard ggiant favorable hgiant H hcap hIlower hscale
    hlarge hvg hφsupport hchild hgap hcomp

end Ostmann

end OAI
