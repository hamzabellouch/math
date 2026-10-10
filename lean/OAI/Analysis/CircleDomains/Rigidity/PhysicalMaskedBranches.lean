import OAI.Analysis.CircleDomains.Rigidity.MaskedTerminalBranches
import OAI.Analysis.CircleDomains.Selection.PhysicalTerminals
import OAI.Analysis.CircleDomains.Transfer.RealGridTransfer

namespace OAI

/-!
# Nonsingular branches on the actual physical terminal boundaries

The disjointness of terminal and filling caps supplies the untouched
boundary condition. The uniform staircase bounds from the physical
terminal construction then give the actual filled branches and the
square-sum excess estimate on each nonsingular subfamily.
-/

open Set Filter Function
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem physical_masked_terminal_branches
    {I J : Type*} [Fintype I] [Fintype J] {n : ℕ}
    (T : I → ℂ ≃ₜ ℂ) (H : J → ℂ ≃ₜ ℂ)
    (hTH : ∀ i j, Disjoint (closure (jordanInterior (T i))) (closure (jordanInterior (H j))))
    {Ω : Set (ℝ × ℝ)} (O : I → Set (ℝ × ℝ)) (hO : ∀ i, IsOpen (O i))
    (hTO : ∀ i, frontier (realJordanInterior (T i)) ⊆ O i)
    (M : Fin n → Set (ℝ × ℝ)) (f F : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (χ : (ℝ × ℝ) → ℝ) (u : I → Fin n → (ℝ × ℝ) → ℝ)
    (S : Fin n → Finset I) (a : I → Fin n → ℝ)
    (hu : ∀ l i, i ∈ S l → ContDiffOn ℝ ∞ (u i l) (O i))
    (hproj : ∀ l i, i ∈ S l → ∀ x ∈ O i, (u i l x : UnitAddCircle) = f l x)
    (hχone : ∀ i x, x ∈ O i → χ x = 1)
    (N : ℕ) {δ η : ℝ} (hδ : 0 < δ) (hδh : δ < reciprocalGridStep N / 4) (θ : Fin n → ℝ)
    (hF : IsMaskedFilledCircleFamily (fun j => realJordanInterior (H j)) Ω M
      (circleCutoffFamily f χ N δ θ) F)
    (ha : ∀ l i, i ∈ S l → 0 ≤ a i l)
    (hbound : ∀ l i, i ∈ S l → ∀ x ∈ frontier (jordanInterior (T i)),
      ∀ y ∈ frontier (jordanInterior (T i)),
      |shiftedStaircase (reciprocalGridStep N) δ (θ l) (u i l (Complex.equivRealProdCLM x)) -
        shiftedStaircase (reciprocalGridStep N) δ (θ l) (u i l (Complex.equivRealProdCLM y))| ≤
          a i l + 4 * reciprocalGridStep N)
    (hsmall : reciprocalGridStep N * Real.sqrt (Fintype.card I : ℝ) < η) :
    ∃ w : I → Fin n → (ℝ × ℝ) → ℝ,
      (∀ l i, i ∈ S l → ContDiffOn ℝ ∞ (w i l) (O i) ∧
        ∀ᶠ x in 𝓝ˢ (frontier (realJordanInterior (T i))), (w i l x : UnitAddCircle) = F l x) ∧
      ∀ l, Real.sqrt (∑ i ∈ S l,
        max (Metric.diam (w i l '' frontier (realJordanInterior (T i))) - a i l) 0 ^ 2) < 4 * η := by
  apply actual_masked_terminal_branches_of_staircase_bound
    (fun j => (realJordanInterior_geometry (H j)).1)
    (fun i => frontier (realJordanInterior (T i))) O hO hTO ?_
    M f F χ u S a hu hproj hχone N hδ hδh θ hF ha ?_ hsmall
  · intro i x hx j hj
    rw [frontier_realJordanInterior] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨y, hy, hyz⟩ := hj
    have heq : y = z := Complex.equivRealProdCLM.injective hyz
    exact Set.disjoint_left.mp (hTH i j) (frontier_subset_closure hz)
      (heq ▸ subset_closure hy)
  · intro l i hi x hx y hy
    rw [frontier_realJordanInterior] at hx hy
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨w, hw, rfl⟩ := hy
    exact hbound l i hi z hz w hw

end CircleDomainRigidity.FiniteTransfer

end

end OAI
