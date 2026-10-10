import OAI.Combinatorics.Progressions.Linear.FullFastHorizontalSpanning

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

variable {ι κ ν τ L : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

theorem exists_controlled_fullFastHorizontal_split
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (K : Submodule ℝ (LayerOneBasisIndex ω → ℝ)) (B : Matrix (LayerOneBasisIndex ω) ν ℚ)
    (hBspan : Submodule.span ℝ (Set.range (B.map (Rat.castHom ℝ)).col) = K)
    (b : ν → K) (hb : ∀ j, (b j).val = (B.map (Rat.castHom ℝ)).col j)
    (R : K →ₗ[ℝ] (τ → ℝ)) (n : ℕ) (hR : ∀ j, R (b j) ∈ realDenominatorGrid n)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (hB : ∀ i j, RationalHeightLE (B i j) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hsize : ((Fintype.card κ + Fintype.card ι + Fintype.card ν : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      ∃ split : (LayerOneBasisIndex ω → ℝ) →ₗ[ℝ] K,
        (∀ x, x ∈ F.fullFastHorizontalCoordinates e ω hF W ⊔ K →
          x - (split x).val ∈ F.fullFastHorizontalCoordinates e ω hF W) ∧
        (∀ x, ‖split x‖ ≤ Real.exp ((p + 2) ^ 19) * ‖x‖) ∧
        ∀ x, x ∈ realDenominatorGrid l → R (split x) ∈ realDenominatorGrid (n * m) := by
  have hrow : Fintype.card (LayerOneBasisIndex ω) ≤ Fintype.card ι :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hrows : (Fintype.card (LayerOneBasisIndex ω) : ℝ) ≤ p := by
    have hle : Fintype.card (LayerOneBasisIndex ω) ≤
        Fintype.card κ + Fintype.card ι + Fintype.card ν := by omega
    exact (Nat.cast_le.mpr hle).trans hsize
  have hcol : Fintype.card ((κ ⊕ TopGradedBasisIndex s ω) ⊕ ν) ≤
      Fintype.card κ + Fintype.card ι + Fintype.card ν := by
    rw [Fintype.card_sum]
    exact Nat.add_le_add_right (fullFastDiagonalGenerators_card (κ := κ) (s := s) (ω := ω)) _
  exact exists_controlled_kernel_split (F.fullFastHorizontalCoordinates e ω hF W) K
    (F.fullFastHorizontalMatrix e ω hF v) B (F.fullFastHorizontalMatrix_span e ω hF W hW v hv)
    hBspan b hb R n hR hH hl (F.fullFastHorizontalMatrix_height e ω hF v hH hheight) hB
    hp hrows ((Nat.cast_le.mpr hcol).trans hsize) hHp hlp

end Erdos3.NilpotentLieFiltration

end

end OAI
