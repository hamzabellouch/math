import OAI.Analysis.KadisonKastler.UnitaryApproximation
import OAI.Analysis.KadisonKastler.Amenable
import OAI.Analysis.KadisonKastler.NearInclusionDistance
import Mathlib.Analysis.CStarAlgebra.Spectrum

namespace OAI

/-! # Unitary approximation in a closed neighbouring algebra

Spectral permanence reflects invertibility of a sufficiently close contraction
into the closed subalgebra. Its polar unitary then has at most three times the
original approximation error. No finiteness assumption on the target is needed.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

/-- Invertibility near an ambient unitary is reflected into a closed
C-star subalgebra. -/
theorem isUnit_of_near_ambient_unitary (S : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] (u : unitary A) (x : S)
    (hclose : ‖(x : A) - (u : A)‖ < 1) : IsUnit x := by
  apply S.coe_isUnit.mp
  nontriviality A
  have hinv : ‖(((Unitary.toUnits u)⁻¹ : Aˣ) : A)‖ = 1 := by
    change ‖star (u : A)‖ = 1
    rw [norm_star, CStarRing.norm_coe_unitary]
  exact (Units.ofNearby (Unitary.toUnits u) (x : A) (by
    simpa only [Unitary.val_toUnits_apply, hinv, inv_one] using hclose)).isUnit

/-- Polar normalization of a nearby contraction in an arbitrary closed
subalgebra costs a factor of three. -/
theorem exists_unitary_near_of_closed_subalgebra (S : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] (u : unitary A) (x : S) (hx : ‖x‖ ≤ 1)
    (hclose : ‖(x : A) - (u : A)‖ < 1) :
    ∃ v : unitary S, ‖(v : A) - (u : A)‖ ≤ 3 * ‖(x : A) - (u : A)‖ := by
  let := CStarAlgebra.spectralOrder S
  let := CStarAlgebra.spectralOrderedRing S
  have hi := isUnit_of_near_ambient_unitary S u x hclose
  obtain ⟨v, hv⟩ := exists_unitary_mul_abs hi.unit
  rw [hi.unit_spec] at hv
  have hdefect : ‖star x * x - 1‖ ≤ 2 * ‖(x : A) - (u : A)‖ :=
    norm_isometry_defect_le (A := A) (x := (x : A)) hx u.property.1
  have hpolar := (norm_unitary_polar_sub_le x v hv).trans hdefect
  refine ⟨v, ?_⟩
  have ht := norm_sub_le_norm_sub_add_norm_sub (v : A) (x : A) (u : A)
  change ‖(v : A) - (x : A)‖ ≤ _ at hpolar
  linarith

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M N : VonNeumannAlgebra H}

/-- A sufficiently small Kadison--Kastler gap supplies unitary approximants
in the second algebra, regardless of its type. -/
theorem exists_unitary_approx_of_small_kkDistance {b : ℝ}
    (hb : b ≤ 1) (hgap : kkDistance M N < b) (u : unitary (Algebra M)) :
    ∃ v : unitary (Algebra N),
      ‖(v : H →L[ℂ] H) - (u : H →L[ℂ] H)‖ < 3 * b := by
  let : IsClosed (N.toStarSubalgebra : Set (H →L[ℂ] H)) := isClosed_algebra N
  obtain ⟨x, hx, hxu⟩ := exists_unitBall_approx
    ⟨(u : Algebra M).property, norm_unitary_le_one u⟩ hgap
  have hclose : ‖x - (u : H →L[ℂ] H)‖ < b := by
    simpa only [norm_sub_rev] using hxu
  obtain ⟨v, hv⟩ := exists_unitary_near_of_closed_subalgebra
    N.toStarSubalgebra (ambientAlgebraUnitary u) (⟨x, hx.1⟩ : Algebra N) hx.2
    (hclose.trans_le hb)
  exact ⟨v, hv.trans_lt (mul_lt_mul_of_pos_left hclose (by norm_num))⟩

/-- Strict one-sided near inclusion also supplies unitary approximants.
The additional factor two normalizes the original algebra approximant. -/
theorem exists_unitary_approx_of_nearInclusion {γ : ℝ}
    (hsmall : 2 * γ ≤ 1) (hnear : NearInclusion M N γ)
    (u : unitary (Algebra M)) :
    ∃ v : unitary (Algebra N),
      ‖(v : H →L[ℂ] H) - (u : H →L[ℂ] H)‖ < 6 * γ := by
  let : IsClosed (N.toStarSubalgebra : Set (H →L[ℂ] H)) := isClosed_algebra N
  obtain ⟨x, hx, hxu⟩ := exists_unitBall_approx_of_nearInclusion hnear
    (show (u : H →L[ℂ] H) ∈ unitBall M from
      ⟨(u : Algebra M).property, norm_unitary_le_one u⟩)
  have hclose : ‖x - (u : H →L[ℂ] H)‖ < 2 * γ := by
    simpa only [norm_sub_rev] using hxu
  obtain ⟨v, hv⟩ := exists_unitary_near_of_closed_subalgebra
    N.toStarSubalgebra (ambientAlgebraUnitary u) (⟨x, hx.1⟩ : Algebra N) hx.2
    (hclose.trans_le hsmall)
  exact ⟨v, hv.trans_lt (by change 3 * ‖x - (u : H →L[ℂ] H)‖ < _; linarith)⟩

end

end KadisonKastler

end OAI
