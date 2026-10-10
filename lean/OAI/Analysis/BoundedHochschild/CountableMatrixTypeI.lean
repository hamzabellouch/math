import OAI.Analysis.BoundedHochschild.CountableMatrixCorners
import OAI.Analysis.BoundedHochschild.TypeICentralSupport

namespace OAI

/-! The generated countable matrix algebra is type I: its abelian diagonal
has full central support, since all diagonal projections are equivalent and
their sum is the ambient unit. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison FinitePathMain

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

theorem countableMatrixClosure_typeI (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = 1)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0)
    (ht : PredualTendsto e (fun s : Finset ℕ => ∑ i ∈ s, (c i).final) Filter.atTop 1) :
    TypeICentralSummand (1 : countableMatrixClosure e c) := by
  let R := countableMatrixClosure e c
  let p : R := ⟨(c 0).final, countableMatrixClosure_transition e c 0 0⟩
  have hp : AbelianProjection p := countableMatrixClosure_diagonal_abelian e c hi ho 0
  refine ⟨⟨IsStarProjection.one R, fun _ => Commute.one_left _⟩, ?_⟩
  intro q hq _ hq0
  have hqp : IsStarProjection (q * p) := hq.1.mul hp.1 (hq.2 p)
  have hle_p : q * p ≤ p := (hqp.le_iff_mul_eq_left hp.1).mpr (by
    rw [mul_assoc, hp.1.isIdempotentElem.eq])
  have hle_q : q * p ≤ q := (hqp.le_iff_mul_eq_right hq.1).mpr (by
    rw [← mul_assoc, hq.1.isIdempotentElem.eq])
  refine ⟨q * p, HochschildTypeII.abelian_of_le hp hqp hle_p, hle_q, ?_⟩
  intro hzero
  have hz : (q : M) * (c 0).final = 0 := congrArg Subtype.val hzero
  have hqstar : star (q : M) = (q : M) := congrArg Subtype.val hq.1.isSelfAdjoint.star_eq
  have hqdiag (i : ℕ) : (q : M) * (c i).final = 0 := by
    let t : R := ⟨(c i : M) * star (c 0 : M), countableMatrixClosure_transition e c i 0⟩
    have hcomm : (q : M) * (t : M) = (t : M) * (q : M) :=
      congrArg Subtype.val (hq.2 t).eq
    have htp : (t : M) * (c 0).final = (t : M) := by
      change ((c i : M) * star (c 0 : M)) * ((c 0 : M) * star (c 0 : M)) = _
      calc
        _ = (c i : M) * (star (c 0 : M) * (c 0 : M)) * star (c 0 : M) := by
          simp only [mul_assoc]
        _ = _ := by rw [show star (c 0 : M) * (c 0 : M) = 1 from hi 0, mul_one]
    have hqt : (q : M) * (t : M) = 0 := by
      calc
        _ = (q : M) * ((t : M) * (c 0).final) := by rw [htp]
        _ = ((t : M) * (q : M)) * (c 0).final := by rw [← mul_assoc, hcomm]
        _ = (t : M) * ((q : M) * (c 0).final) := by rw [mul_assoc]
        _ = 0 := by rw [hz, mul_zero]
    have htt : (t : M) * ((c 0 : M) * star (c i : M)) = (c i).final := by
      change ((c i : M) * star (c 0 : M)) * ((c 0 : M) * star (c i : M)) = _
      calc
        _ = (c i : M) * (star (c 0 : M) * (c 0 : M)) * star (c i : M) := by
          simp only [mul_assoc]
        _ = _ := by rw [show star (c 0 : M) * (c 0 : M) = 1 from hi 0, mul_one]
                    rfl
    rw [← htt, ← mul_assoc, hqt, zero_mul]
  have hann := orthogonal_projection_sum_annihilator e (fun i => (c i).final) (q : M) 1 ht
    (fun i => by
      simpa only [star_mul, (c i).final_proj.isSelfAdjoint.star_eq, hqstar, star_zero] using
        congrArg star (hqdiag i))
  apply hq0
  apply Subtype.ext
  change (q : M) = 0
  simpa only [one_mul] using hann

end BoundedHochschild.KadisonRingrose

end

end OAI
