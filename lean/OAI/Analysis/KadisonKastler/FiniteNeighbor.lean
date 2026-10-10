import OAI.Analysis.KadisonKastler.BoundaryImprovement
import OAI.Analysis.KadisonKastler.ConcreteFiniteTrace

namespace OAI

/-! # Finiteness of a nearby von Neumann algebra

A finite factor has unitary polar decompositions.  An isometry close to
its unit ball is therefore close to a unitary, hence invertible.  This
proves the finiteness part of the manuscript's finite-neighbor lemma.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {A : Type*} [CStarAlgebra A]

/-- The defect of a contraction near an isometry is at most twice its error. -/
theorem norm_isometry_defect_le {x v : A} (hx : ‖x‖ ≤ 1)
    (hv : star v * v = 1) :
    ‖star x * x - 1‖ ≤ 2 * ‖x - v‖ := by
  have hvn : ‖v‖ ≤ 1 := by
    have h := congrArg norm hv
    rw [CStarRing.norm_star_mul_self] at h
    have h1 : ‖(1 : A)‖ ≤ 1 := norm_unitary_le_one (1 : unitary A)
    nlinarith [norm_nonneg v]
  have he : star x * x - 1 = star x * (x - v) + star (x - v) * v := by
    rw [star_sub, mul_sub, sub_mul, hv]
    noncomm_ring
  calc
    _ ≤ ‖star x * (x - v)‖ + ‖star (x - v) * v‖ := he ▸ norm_add_le _ _
    _ ≤ ‖x‖ * ‖x - v‖ + ‖x - v‖ * ‖v‖ := by
      simpa only [norm_star] using add_le_add
        (norm_mul_le (star x) (x - v)) (norm_mul_le (star (x - v)) v)
    _ ≤ 1 * ‖x - v‖ + ‖x - v‖ * 1 := add_le_add
      (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
      (mul_le_mul_of_nonneg_left hvn (norm_nonneg _))
    _ = _ := by ring

/-- A unitary polar factor is close to its element by its isometry defect. -/
theorem norm_unitary_polar_sub_le (x : A) (u : unitary A)
    [PartialOrder A] [StarOrderedRing A]
    (hu : (u : A) * CFC.abs x = x) :
    ‖(u : A) - x‖ ≤ ‖star x * x - 1‖ := by
  have he : (u : A) - x = (u : A) * (1 - CFC.abs x) := by
    rw [mul_sub, mul_one, hu]
  rw [he, CStarRing.norm_coe_unitary_mul, norm_sub_rev]
  exact norm_sqrt_sub_one_le _ (star_mul_self_nonneg _)

/-- Being within one of a unitary forces an isometry to be unitary. -/
theorem isometry_coisometry_of_near_unitary {v : A}
    (hv : star v * v = 1) (u : unitary A) (hclose : ‖v - (u : A)‖ < 1) :
    v * star v = 1 := by
  nontriviality A
  have hinv : ‖(((Unitary.toUnits u)⁻¹ : Aˣ) : A)‖ = 1 := by
    change ‖star (u : A)‖ = 1
    rw [norm_star, CStarRing.norm_coe_unitary]
  have hunit : IsUnit v :=
    (Units.ofNearby (Unitary.toUnits u) v (by
      simpa only [Unitary.val_toUnits_apply, hinv, inv_one] using hclose)).isUnit
  exact (hunit.mem_unitary_of_star_mul_self hv).2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M N : VonNeumannAlgebra H}

local instance finiteNeighborOrder : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance finiteNeighborStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

/-- Finiteness is preserved by a sufficiently small gap from a finite factor.
This is the finiteness assertion of the manuscript's finite-neighbor lemma;
factoriality is a separate assertion. -/
theorem finite_of_near_finite_factor
    (hfactor : ∀ x : Algebra M, (∀ y : Algebra M, y * x = x * y) →
      ∃ c : ℂ, x = c • (1 : Algebra M))
    (hfinite : ∀ v : Algebra M, star v * v = 1 → v * star v = 1)
    (hgap : kkDistance M N < 1 / 10) :
    ∀ v : Algebra N, star v * v = 1 → v * star v = 1 := by
  intro v hv
  have hvambient : star (v : H →L[ℂ] H) * v = 1 := congrArg Subtype.val hv
  have hvn : ‖(v : H →L[ℂ] H)‖ ≤ 1 := by
    have h := congrArg norm hvambient
    rw [CStarRing.norm_star_mul_self] at h
    have h1 : ‖(1 : H →L[ℂ] H)‖ ≤ 1 :=
      norm_unitary_le_one (1 : unitary (H →L[ℂ] H))
    nlinarith [norm_nonneg (v : H →L[ℂ] H)]
  obtain ⟨x, hx, hclose⟩ := exists_unitBall_approx (M := N) (N := M)
    ⟨v.property, hvn⟩ (by simpa only [kkDistance_comm N M] using hgap)
  rw [norm_sub_rev] at hclose
  let a : Algebra M := ⟨x, hx.1⟩
  obtain ⟨u, hu⟩ := Generator.Tracial.exists_unitary_polar_decomposition hfactor hfinite a
  let U : unitary (H →L[ℂ] H) :=
    Unitary.map (StarMonoidHom.ofClass M.toStarSubalgebra.subtype) u
  have hdefect : ‖star a * a - 1‖ < 2 * (1 / 10 : ℝ) := by
    have h := norm_isometry_defect_le hx.2 hvambient
    change ‖star a * a - 1‖ ≤ 2 * ‖x - (v : H →L[ℂ] H)‖ at h
    exact h.trans_lt (by nlinarith [hclose])
  have hup : ‖(u : Algebra M) - a‖ < 2 * (1 / 10 : ℝ) :=
    (norm_unitary_polar_sub_le a u hu).trans_lt hdefect
  change ‖(u : Algebra M).val - x‖ < 2 * (1 / 10 : ℝ) at hup
  have hnear : ‖(v : H →L[ℂ] H) - (U : H →L[ℂ] H)‖ < 1 := by
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (v : H →L[ℂ] H) x (U : H →L[ℂ] H)
    have hux : ‖x - (U : H →L[ℂ] H)‖ < 2 * (1 / 10 : ℝ) := by
      change ‖x - (u : Algebra M).val‖ < _
      simpa only [norm_sub_rev] using hup
    rw [norm_sub_rev (v : H →L[ℂ] H) x] at htri
    linarith
  apply Subtype.ext
  exact isometry_coisometry_of_near_unitary hvambient U hnear

end

end KadisonKastler

end OAI
