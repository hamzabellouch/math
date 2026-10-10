import OAI.Analysis.BoundedHochschild.OrthogonalPartialIsoSums
import OAI.Analysis.BoundedHochschild.IsometryDefectColumns

namespace OAI

/-!
# Properly infinite projections from orthogonal columns

Countably many equivalent orthogonal projections split into even and odd
columns. The resulting operators are actual partial isometries in the algebra.
-/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u

variable {M : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

/-- A projection admits two orthogonal copies of itself inside itself. -/
def ProperlyInfiniteProjection (p : M) : Prop :=
  ∃ v w : PartialIso M, v.initial = p ∧ w.initial = p ∧
    v.final ≤ p ∧ w.final ≤ p ∧ v.final * w.final = 0

omit [PartialOrder M] [StarOrderedRing M] in
lemma column_transition_initial (v w : PartialIso M) (h : v.initial = w.initial) :
    star ((v : M) * star (w : M)) * ((v : M) * star (w : M)) = w.final := by
  calc
    _ = (w : M) * v.initial * star (w : M) := by
      simp only [star_mul, star_star, PartialIso.initial, mul_assoc]
    _ = w.final := by rw [h, w.mul_initial]; rfl

def columnTransition (v w : PartialIso M) (h : v.initial = w.initial) : PartialIso M :=
  ⟨(v : M) * star (w : M), by
    rw [mul_assoc, column_transition_initial v w h]
    have hw : star (w : M) * w.final = star (w : M) := by
      simpa only [star_mul, star_star, w.final_proj.isSelfAdjoint.star_eq] using
        congrArg star w.final_mul
    rw [mul_assoc, hw]⟩

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma columnTransition_initial (v w : PartialIso M) (h) :
    (columnTransition v w h).initial = w.final := column_transition_initial v w h

omit [PartialOrder M] [StarOrderedRing M] in
@[simp] lemma columnTransition_final (v w : PartialIso M) (h) :
    (columnTransition v w h).final = v.final := by
  change ((v : M) * star (w : M)) * star ((v : M) * star (w : M)) = _
  rw [star_mul, star_star]
  calc
    _ = (v : M) * w.initial * star (v : M) := by simp only [PartialIso.initial, mul_assoc]
    _ = v.final := by rw [← h, v.mul_initial]; rfl

lemma projection_le_complement_of_mul_zero {p q : M}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p * q = 0) : p ≤ 1 - q := by
  apply (hp.le_iff_mul_eq_left hq.one_sub).mpr
  rw [mul_sub, mul_one, hpq, sub_zero]

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- The supremum of countably many equivalent orthogonal projections is
properly infinite. Only the particular even/odd shift operators are needed. -/
theorem properlyInfinite_of_columns (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {p : M} (c : ℕ → PartialIso M) (hi : ∀ i, (c i).initial = p)
    (ho : ∀ i j, i ≠ j → (c i).final * (c j).final = 0) :
    ∃ q : M, IsStarProjection q ∧ ProperlyInfiniteProjection q ∧
      (∀ i, (c i).final ≤ q) ∧
      (∀ r : M, IsStarProjection r → (∀ i, (c i).final ≤ r) → q ≤ r) := by
  obtain ⟨q, hq, hqi, hqmin, _⟩ := exists_orthogonal_projection_sum e
    (fun i => (c i).final) (fun i => (c i).final_proj) ho
  let a (i : ℕ) := columnTransition (c (2 * i)) (c i) ((hi _).trans (hi _).symm)
  let b (i : ℕ) := columnTransition (c (2 * i + 1)) (c i) ((hi _).trans (hi _).symm)
  have hai (i) : (a i).initial = (c i).final := columnTransition_initial ..
  have hbi (i) : (b i).initial = (c i).final := columnTransition_initial ..
  have haf (i) : (a i).final = (c (2 * i)).final := columnTransition_final ..
  have hbf (i) : (b i).final = (c (2 * i + 1)).final := columnTransition_final ..
  obtain ⟨v, hvi, _, hvi_min, hvf_min⟩ := exists_countable_partialIso_sum e a
    (fun i j hij => by rw [hai, hai]; exact ho i j hij)
    (fun i j hij => by rw [haf, haf]; exact ho _ _ (by omega))
  obtain ⟨w, hwi, _, hwi_min, hwf_min⟩ := exists_countable_partialIso_sum e b
    (fun i j hij => by rw [hbi, hbi]; exact ho i j hij)
    (fun i j hij => by rw [hbf, hbf]; exact ho _ _ (by omega))
  have hvq : v.initial = q := le_antisymm
    (hvi_min q hq (fun i => by rw [hai]; exact hqi i))
    (hqmin _ v.initial_proj (fun i => by rw [← hai]; exact hvi i))
  have hwq : w.initial = q := le_antisymm
    (hwi_min q hq (fun i => by rw [hbi]; exact hqi i))
    (hqmin _ w.initial_proj (fun i => by rw [← hbi]; exact hwi i))
  refine ⟨q, hq, ⟨v, w, hvq, hwq,
    hvf_min q hq (fun i => by rw [haf]; exact hqi _),
    hwf_min q hq (fun i => by rw [hbf]; exact hqi _), ?_⟩, hqi, hqmin⟩
  have hw_even (i : ℕ) : w.final ≤ 1 - (a i).final := by
    apply hwf_min _ (a i).final_proj.one_sub
    intro j
    apply projection_le_complement_of_mul_zero (b j).final_proj (a i).final_proj
    rw [hbf, haf]
    exact ho _ _ (by omega)
  have hav (i : ℕ) : (a i).final ≤ 1 - w.final := by
    apply projection_le_complement_of_mul_zero (a i).final_proj w.final_proj
    exact HochschildTypeII.projection_orthogonal_of_le_complement (a i).final_proj
      w.final_proj (hw_even i)
  have h := HochschildTypeII.projection_orthogonal_of_le_complement w.final_proj
    v.final_proj (hvf_min _ w.final_proj.one_sub hav)
  simpa only [star_mul, v.final_proj.isSelfAdjoint.star_eq,
    w.final_proj.isSelfAdjoint.star_eq, star_zero] using congrArg star h

/-- A nonunitary isometry produces a nonzero properly infinite projection. -/
theorem nonunitary_isometry_has_properlyInfinite_projection
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) {v : M} (hv : star v * v = 1)
    (hnot : v * star v ≠ 1) :
    ∃ q : M, IsStarProjection q ∧ q ≠ 0 ∧ ProperlyInfiniteProjection q := by
  let p := isometryDefect v
  have hp : IsStarProjection p := isometryDefect_projection hv
  let c := isometryColumn v hv p hp
  obtain ⟨q, hq, hproper, hqi, _⟩ := properlyInfinite_of_columns e c
    (fun i => isometryColumn_initial ..)
    (fun i j hij => isometryColumn_final_orthogonal hv hp (isometryDefect_mul hv) hij)
  refine ⟨q, hq, ?_, hproper⟩
  intro hq0
  have hp0 : p = 0 := by
    have h : p ≤ q := by
      simpa only [c, isometryColumn, PartialIso.final, pow_zero, one_mul,
        hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq] using hqi 0
    exact le_antisymm (hq0 ▸ h) hp.nonneg
  exact hnot (sub_eq_zero.mp hp0).symm

end BoundedHochschild.KadisonRingrose

end

end OAI
