import OAI.Analysis.CircleDomains.Rigidity.MaskedModelData
import OAI.Analysis.CircleDomains.Rigidity.PhysicalMaskedBranches

namespace OAI

/-! The same filled model has actual staircase branches on every selected
nonsingular terminal inside its mask. Exterior constant replacements do
not change these branches or their original-band excess estimate. -/

open Set Function Filter
open scoped Topology ContDiff

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MaskedModelData.terminal_branches
    {I J : Type*} [Fintype I] [Fintype J] {n N : ℕ}
    {T : I → ℂ ≃ₜ ℂ} {H : J → ℂ ≃ₜ ℂ}
    {G K : Set (ℝ × ℝ)} {M : Fin n → Set (ℝ × ℝ)}
    {f : Fin n → (ℝ × ℝ) → UnitAddCircle} {χ : (ℝ × ℝ) → ℝ}
    {θ : Fin n → ℝ} {ε : ℝ}
    (Q : MaskedModelData T H G K M f χ N θ ε)
    (hTH : ∀ i j, Disjoint (closure (jordanInterior (T i))) (closure (jordanInterior (H j))))
    (O : I → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hTO : ∀ i, frontier (realJordanInterior (T i)) ⊆ O i)
    (u : I → Fin n → (ℝ × ℝ) → ℝ) (S : Fin n → Finset I) (a : I → Fin n → ℝ)
    (hu : ∀ l i, i ∈ S l → ContDiffOn ℝ ∞ (u i l) (O i))
    (hOM : ∀ l i, i ∈ S l → O i ⊆ M l)
    (hproj : ∀ l i, i ∈ S l → ∀ x ∈ O i, (u i l x : UnitAddCircle) = f l x)
    (hχone : ∀ i x, x ∈ O i → χ x = 1)
    (ha : ∀ l i, i ∈ S l → 0 ≤ a i l)
    (hbound : ∀ l i, i ∈ S l → ∀ x ∈ frontier (jordanInterior (T i)),
      ∀ y ∈ frontier (jordanInterior (T i)),
      |shiftedStaircase (reciprocalGridStep N)
          (staircaseWidth (reciprocalGridStep N) Q.widthIndex) (θ l)
          (u i l (Complex.equivRealProdCLM x)) -
        shiftedStaircase (reciprocalGridStep N)
          (staircaseWidth (reciprocalGridStep N) Q.widthIndex) (θ l)
          (u i l (Complex.equivRealProdCLM y))| ≤ a i l + 4 * reciprocalGridStep N)
    {η : ℝ} (hsmall : reciprocalGridStep N * Real.sqrt (Fintype.card I : ℝ) < η) :
    ∃ w : I → Fin n → (ℝ × ℝ) → ℝ,
      (∀ l i, i ∈ S l → ContDiffOn ℝ ∞ (w i l) (O i) ∧
        ∀ᶠ x in 𝓝ˢ (frontier (realJordanInterior (T i))), (w i l x : UnitAddCircle) = Q.functions l x) ∧
      ∀ l, Real.sqrt (∑ i ∈ S l,
        max (Metric.diam (w i l '' frontier (realJordanInterior (T i))) - a i l) 0 ^ 2) < 4 * η := by
  apply physical_masked_terminal_branches T H hTH O hO hTO M Q.base Q.functions χ u S a hu
    ?_ hχone N (staircaseWidth_pos (reciprocalGridStep_pos N) Q.widthIndex)
    (staircaseWidth_lt (reciprocalGridStep_pos N) Q.widthIndex) θ Q.filled ha hbound hsmall
  intro l i hi x hx
  exact (hproj l i hi x hx).trans ((Q.base_mask l).self_of_nhdsSet (hOM l i hi hx)).symm

end CircleDomainRigidity.FiniteTransfer

end

end OAI
