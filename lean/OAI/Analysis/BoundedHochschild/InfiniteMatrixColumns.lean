import OAI.Analysis.BoundedHochschild.ProperlyInfiniteIsometries
import OAI.Analysis.BoundedHochschild.IsometryAbsorption

namespace OAI

/-!
# A unital countable system of equivalent orthogonal projections

Two orthogonal isometries give a countable shift. Its residual projection is
absorbed into the first column, so the finite diagonal sums converge weak-star
to the unit, without a countability assumption on the predual.
-/

noncomputable section

open Filter

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The concrete countable column system needed in the properly infinite
cohomology argument. All columns are isometries and their ranges sum to one. -/
theorem exists_countable_isometries_of_two (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {v w : M} (hv : star v * v = 1) (hw : star w * w = 1) (hvw : star v * w = 0) :
    ∃ c : ℕ → PartialIso M, (∀ i, (c i).initial = 1) ∧
      (∀ i j, i ≠ j → (c i).final * (c j).final = 0) ∧
      PredualTendsto e (fun s : Finset ℕ => ∑ i ∈ s, (c i).final) atTop 1 := by
  have hwi (i : ℕ) : star (v ^ i * w) * (v ^ i * w) = 1 := by
    rw [star_mul]
    calc
      _ = star w * (star (v ^ i) * v ^ i) * w := by simp only [mul_assoc]
      _ = 1 := by rw [isometry_pow_initial hv, mul_one, hw]
  let c (i : ℕ) : PartialIso M := ⟨v ^ i * w, by rw [mul_assoc, hwi, mul_one]⟩
  have hci (i) : (c i).initial = 1 := hwi i
  let p := (c 0).final
  have hp : IsStarProjection p := (c 0).final_proj
  have hpw : p = w * star w := by simp only [p, c, PartialIso.final, pow_zero, one_mul]
  have hpv : p * v = 0 := by
    have h : star w * v = 0 := by
      simpa only [star_mul, star_star, star_zero] using congrArg star hvw
    rw [hpw, mul_assoc, h, mul_zero]
  have hcfin (i) : (c i).final = (isometryColumn v hv p hp i).final := by
    change (v ^ i * w) * star (v ^ i * w) = (v ^ i * p) * star (v ^ i * p)
    rw [star_mul, star_mul, hp.isSelfAdjoint.star_eq]
    calc
      _ = v ^ i * (w * star w) * star (v ^ i) := by simp only [mul_assoc]
      _ = v ^ i * p * star (v ^ i) := by rw [hpw]
      _ = _ := by simp only [mul_assoc, ← mul_assoc p p, hp.isIdempotentElem.eq]
  have hco (i j) (hij : i ≠ j) : (c i).final * (c j).final = 0 := by
    rw [hcfin, hcfin]
    exact isometryColumn_final_orthogonal hv hp hpv hij
  obtain ⟨q, hq, hcq, hqmin, _⟩ := exists_orthogonal_projection_sum e
    (fun i => (c i).final) (fun i => (c i).final_proj) hco
  have hpq : p ≤ q := hcq 0
  have hpR : p * (1 - q) = 0 := by
    rw [mul_sub, mul_one, (hp.le_iff_mul_eq_left hq).mp hpq, sub_self]
  have hP : IsStarProjection (p + (1 - q)) := hp.add hq.one_sub hpR
  have hPw : (p + (1 - q)) * w = w := by
    have hqw : q * w = w := by
      have hh := partialIso_left_support hq (c 0) hpq
      simpa only [c, pow_zero, one_mul] using hh
    rw [add_mul, hpw, mul_assoc, hw, mul_one, sub_mul, one_mul, hqw, sub_self, add_zero]
  obtain ⟨b, hbi, hbf⟩ := isometry_onto_projection e hw hP hPw
  let d : ℕ → PartialIso M
    | 0 => b
    | n + 1 => c (n + 1)
  have hdi (i) : (d i).initial = 1 := by
    cases i with
    | zero => exact hbi
    | succ i => exact hci (i + 1)
  have hb_orth (i : ℕ) : b.final * (c (i + 1)).final = 0 := by
    have hR : (1 - q) * (c (i + 1)).final = 0 := by
      rw [sub_mul, one_mul, ((c (i + 1)).final_proj.le_iff_mul_eq_right hq).mp (hcq _), sub_self]
    rw [hbf, add_mul, hco 0 (i + 1) (by omega), hR, zero_add]
  have hdo (i j) (hij : i ≠ j) : (d i).final * (d j).final = 0 := by
    cases i with
    | zero =>
        cases j with
        | zero => exact (hij rfl).elim
        | succ j => exact hb_orth j
    | succ i =>
        cases j with
        | zero =>
            simpa only [star_mul, b.final_proj.isSelfAdjoint.star_eq,
              (c (i + 1)).final_proj.isSelfAdjoint.star_eq, star_zero] using
              congrArg star (hb_orth i)
        | succ j => exact hco (i + 1) (j + 1) hij
  obtain ⟨P, hPproj, hdP, hPmin, ht⟩ := exists_orthogonal_projection_sum e
    (fun i => (d i).final) (fun i => (d i).final_proj) hdo
  have hpP : p ≤ P := by
    calc
      p ≤ p + (1 - q) := le_add_of_nonneg_right hq.one_sub.nonneg
      _ = b.final := hbf.symm
      _ ≤ P := hdP 0
  have hqP : q ≤ P := by
    apply hqmin P hPproj
    intro i
    cases i with
    | zero => exact hpP
    | succ i => exact hdP (i + 1)
  have hRP : 1 - q ≤ P := by
    calc
      1 - q ≤ p + (1 - q) := le_add_of_nonneg_left hp.nonneg
      _ = b.final := hbf.symm
      _ ≤ P := hdP 0
  have h1P : 1 ≤ P := by
    apply ((IsStarProjection.one M).le_iff_mul_eq_right hPproj).mpr
    calc
      P * 1 = P * (q + (1 - q)) := by congr 1; abel
      _ = q + (1 - q) := by
        rw [mul_add, (hq.le_iff_mul_eq_right hPproj).mp hqP,
          (hq.one_sub.le_iff_mul_eq_right hPproj).mp hRP]
      _ = 1 := by abel
  have hPeq : P = 1 := le_antisymm hPproj.le_one h1P
  exact ⟨d, hdi, hdo, hPeq ▸ ht⟩

/-- Every algebra with no finite central summand has a unital countable matrix
column system. -/
theorem exists_countable_isometries (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) :
    ∃ c : ℕ → PartialIso M, (∀ i, (c i).initial = 1) ∧
      (∀ i j, i ≠ j → (c i).final * (c j).final = 0) ∧
      PredualTendsto e (fun s : Finset ℕ => ∑ i ∈ s, (c i).final) atTop 1 := by
  obtain ⟨v, w, hv, hw, hvw⟩ := exists_two_orthogonal_isometries e hno
  exact exists_countable_isometries_of_two e hv hw hvw

end BoundedHochschild.KadisonRingrose

end

end OAI
