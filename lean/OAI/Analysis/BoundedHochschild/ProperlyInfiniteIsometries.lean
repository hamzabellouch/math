import OAI.Analysis.BoundedHochschild.MaximalInfiniteProjection
import OAI.Analysis.BoundedHochschild.InfiniteCentralReduction

namespace OAI

/-!
# Two isometries in an algebra without finite central summands

Comparison embeds the finite complement of a maximal properly infinite
projection into that projection. Its two orthogonal copies then absorb the
complement and give isometries with initial projection one.
-/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison FinitePathMain

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma finite_complement_embeds_properlyInfinite (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) {p : M} (hp : IsStarProjection p)
    (hproper : ProperlyInfiniteProjection p) (hfin : FiniteCorner (1 - p)) :
    ∃ t : PartialIso M, t.initial = 1 - p ∧ t.final ≤ p := by
  obtain ⟨z, t, hz, hti, htf, hzf, hzi⟩ := trace_free_central_comparison e hp.one_sub hp
  let s := centralCutPartialIso z hz.1 (fun a => (hz.2 a).eq) t
  have hsi : s.initial ≤ t.initial := by
    apply (s.initial_proj.le_iff_mul_eq_left t.initial_proj).mpr
    rw [centralCutPartialIso_initial, mul_assoc, t.initial_proj.isIdempotentElem.eq]
  have hsi_fin : FiniteCorner s.initial :=
    finiteCorner_mono s.initial_proj hp.one_sub (hsi.trans hti) hfin
  have hsf_fin : FiniteCorner s.final := by
    simpa only [adjointPartialIso_initial, adjointPartialIso_final] using
      finiteCorner_of_equivalent (adjointPartialIso s) (by
        simpa only [adjointPartialIso_final] using hsi_fin)
  have hzpfin : FiniteCorner (z * p) := by
    simpa only [s, centralCutPartialIso_final, hzf] using hsf_fin
  have hzp : IsStarProjection (z * p) := hz.1.mul hp (hz.2 p)
  have hzp0 : z * p = 0 := properlyInfinite_finite_eq_zero hzp
    (properlyInfinite_central_cut hp hz hproper) hzpfin
  have hzfin : FiniteCorner z := finiteCorner_mono hz.1 hp.one_sub
    (projection_le_complement_of_mul_zero hz.1 hp hzp0) hfin
  have hz0 : z = 0 := hno z hz.1 (fun a => (hz.2 a).eq)
    ((finiteCorner_iff z hz.1).mp hzfin)
  refine ⟨t, ?_, htf⟩
  simpa only [hz0, sub_zero, one_mul] using hzi

/-- The unit is properly infinite when no nonzero central corner is finite. -/
theorem properlyInfinite_one (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) : ProperlyInfiniteProjection (1 : M) := by
  obtain ⟨p, hp, hproper, hfin⟩ := exists_properlyInfinite_with_finite_complement e
  obtain ⟨t, hti, htf⟩ := finite_complement_embeds_properlyInfinite e hno hp hproper hfin
  obtain ⟨v, w, hvi, hwi, hvf, hwf, ho⟩ := hproper
  let b := composePartialIso w t (by rw [hwi]; exact htf)
  have hbi : b.initial = 1 - p := by rw [composePartialIso_initial, hti]
  have hbf : b.final ≤ w.final := composePartialIso_final_le ..
  have hi : v.initial * b.initial = 0 := by rw [hvi, hbi, hp.mul_one_sub_self]
  have hf : v.final * b.final = 0 := projection_mul_zero_of_bounds v.final_proj w.final_proj
    v.final_proj b.final_proj ho le_rfl hbf
  let a := v.orthogonalSum b hi hf
  have hai : a.initial = 1 := by
    rw [PartialIso.orthogonalSum_initial, hvi, hbi]
    abel
  have haf : a.final ≤ p := by
    apply (a.final_proj.le_iff_mul_eq_right hp).mpr
    rw [PartialIso.orthogonalSum_final, mul_add,
      (v.final_proj.le_iff_mul_eq_right hp).mp hvf,
      (b.final_proj.le_iff_mul_eq_right hp).mp (hbf.trans hwf)]
  let V := composePartialIso v a (by rw [hvi]; exact haf)
  let W := composePartialIso w a (by rw [hwi]; exact haf)
  have hV : V.final ≤ v.final := composePartialIso_final_le ..
  have hW : W.final ≤ w.final := composePartialIso_final_le ..
  exact ⟨V, W, (composePartialIso_initial ..).trans hai,
    (composePartialIso_initial ..).trans hai, V.final_proj.le_one, W.final_proj.le_one,
    projection_mul_zero_of_bounds v.final_proj w.final_proj V.final_proj W.final_proj ho hV hW⟩

/-- Actual orthogonal isometries, with no trace, separability, or factor assumption. -/
theorem exists_two_orthogonal_isometries (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (hno : NoFiniteCentralSummand M) :
    ∃ v w : M, star v * v = 1 ∧ star w * w = 1 ∧ star v * w = 0 := by
  obtain ⟨v, w, hvi, hwi, _, _, ho⟩ := properlyInfinite_one e hno
  exact ⟨(v : M), (w : M), hvi, hwi, PartialIso.star_mul_eq_zero_of_final_orthogonal ho⟩

end BoundedHochschild.KadisonRingrose

end

end OAI
