import OAI.Analysis.KadisonKastler.FiniteNeighbor
import OAI.Analysis.KadisonKastler.UnitaryLifts
import OAI.Analysis.KadisonKastler.BoundaryFiniteIsomorphism

namespace OAI

/-! # Unitary approximants in a nearby finite factor

The finite-factor polar decomposition turns contraction approximants into
unitary approximants with three times the error. This supplies the actual
initial unitary family for boundary correction.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M N : VonNeumannAlgebra H}

local instance approximationOrder : PartialOrder (Algebra N) := CStarAlgebra.spectralOrder _
local instance approximationStarOrder : StarOrderedRing (Algebra N) :=
  CStarAlgebra.spectralOrderedRing _

/-- Polar normalization of a contraction approximant costs a factor of three. -/
theorem exists_unitary_near_of_II1
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (u : unitary (H →L[ℂ] H)) (x : Algebra N) (hx : ‖x‖ ≤ 1) :
    ∃ v : unitary (Algebra N),
      ‖(v : H →L[ℂ] H) - (u : H →L[ℂ] H)‖ ≤
        3 * ‖(x : H →L[ℂ] H) - (u : H →L[ℂ] H)‖ := by
  obtain ⟨v, hv⟩ := exists_unitary_polar hN x
  have hdefect : ‖star x * x - 1‖ ≤
      2 * ‖(x : H →L[ℂ] H) - (u : H →L[ℂ] H)‖ := by
    have h := norm_isometry_defect_le (A := H →L[ℂ] H)
      (x := x.val) hx u.property.1
    exact h
  have hpolar := (norm_unitary_polar_sub_le x v hv).trans hdefect
  refine ⟨v, ?_⟩
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (v : H →L[ℂ] H) (x : H →L[ℂ] H) (u : H →L[ℂ] H)
  change ‖(v : H →L[ℂ] H) - (x : H →L[ℂ] H)‖ ≤ _ at hpolar
  linarith

/-- Every unitary of the first algebra has a nearby unitary in the
neighboring finite factor. -/
theorem exists_unitary_approx_of_kkDistance
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    {b : ℝ} (hgap : kkDistance M N < b) (u : unitary (Algebra M)) :
    ∃ v : unitary (Algebra N),
      ‖(v : H →L[ℂ] H) - (u : H →L[ℂ] H)‖ < 3 * b := by
  obtain ⟨x, hx, hxu⟩ := exists_unitBall_approx
    ⟨(u : Algebra M).property, norm_unitary_le_one u⟩ hgap
  obtain ⟨v, hv⟩ := exists_unitary_near_of_II1 hN (ambientAlgebraUnitary u)
    (⟨x, hx.1⟩ : Algebra N) hx.2
  refine ⟨v, hv.trans_lt ?_⟩
  change 3 * ‖x - (u : H →L[ℂ] H)‖ < 3 * b
  rw [norm_sub_rev]
  exact mul_lt_mul_of_pos_left hxu (by norm_num)

/-- A family uniformly close to a unitary representation has multiplicative
defect at most three times its approximation error. -/
theorem unitary_family_multiplicative_defect
    {G : Type*} [Group G] (U : G →* unitary (H →L[ℂ] H))
    (V : G → unitary (H →L[ℂ] H)) {e : ℝ}
    (hV : ∀ g, ‖(V g : H →L[ℂ] H) - (U g : H →L[ℂ] H)‖ ≤ e)
    (g h : G) :
    ‖(V g : H →L[ℂ] H) * V h - V (g * h)‖ ≤ 3 * e := by
  have hmul : ‖(V g : H →L[ℂ] H) * V h - (U g : H →L[ℂ] H) * U h‖ ≤ 2 * e := by
    have heq : (V g : H →L[ℂ] H) * V h - (U g : H →L[ℂ] H) * U h =
        ((V g : H →L[ℂ] H) - U g) * V h +
          (U g : H →L[ℂ] H) * ((V h : H →L[ℂ] H) - U h) := by noncomm_ring
    rw [heq]
    calc
      _ ≤ ‖((V g : H →L[ℂ] H) - U g) * V h‖ +
          ‖(U g : H →L[ℂ] H) * ((V h : H →L[ℂ] H) - U h)‖ := norm_add_le _ _
      _ = ‖(V g : H →L[ℂ] H) - U g‖ + ‖(V h : H →L[ℂ] H) - U h‖ := by
        rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
      _ ≤ 2 * e := by linarith [hV g, hV h]
  have hlast : ‖(U g : H →L[ℂ] H) * U h - V (g * h)‖ ≤ e := by
    have hU : (U g : H →L[ℂ] H) * U h = (U (g * h) : H →L[ℂ] H) := by
      simp only [map_mul, Submonoid.coe_mul]
    rw [hU, norm_sub_rev]
    exact hV (g * h)
  have ht := norm_sub_le_norm_sub_add_norm_sub
    ((V g : H →L[ℂ] H) * V h) ((U g : H →L[ℂ] H) * U h)
    (V (g * h) : H →L[ℂ] H)
  linarith

end

end KadisonKastler

end OAI
