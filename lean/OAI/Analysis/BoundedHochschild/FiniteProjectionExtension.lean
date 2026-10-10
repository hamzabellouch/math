import OAI.Analysis.BoundedHochschild.FiniteProjectionEquivalence

namespace OAI

/-!
# Extension of embeddings in finite corners

A partial embedding into a finite projection extends whenever an embedding
of the larger initial projection exists. This is the cancellation step used
in Ringrose, *Lectures on the trace in a finite von Neumann algebra*, Lemma 5.1.
The construction uses only the predual and finiteness, not a trace.
-/

noncomputable section

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildComparison HochschildCorners

universe u

variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

lemma partialIso_left_support {q : M} (hq : IsStarProjection q)
    (v : PartialIso M) (hv : v.final ≤ q) : q * (v : M) = v := by
  calc
    q * (v : M) = q * (v.final * (v : M)) := by rw [v.final_mul]
    _ = (v : M) := by
      rw [← mul_assoc, (v.final_proj.le_iff_mul_eq_right hq).mp hv, v.final_mul]

lemma partialIso_right_support {q : M} (hq : IsStarProjection q)
    (v : PartialIso M) (hv : v.initial ≤ q) : (v : M) * q = v := by
  calc
    (v : M) * q = ((v : M) * v.initial) * q := by rw [v.mul_initial]
    _ = (v : M) := by
      rw [mul_assoc, (v.initial_proj.le_iff_mul_eq_left hq).mp hv, v.mul_initial]

/-- The unitary extending a supported partial isometry can be chosen in the
same finite corner. Its ambient initial and final projections are that corner. -/
theorem finite_partialIso_extends_in_corner (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {q : M} (hq : IsStarProjection q) (hfinite : FiniteCorner q)
    (v : PartialIso M) (hi : v.initial ≤ q) (hf : v.final ≤ q) :
    ∃ u : M, q * u = u ∧ u * q = u ∧ star u * u = q ∧ u * star u = q ∧
      u * v.initial = v := by
  let vC : PartialIso (Corner q hq) :=
    ⟨⟨(v : M), partialIso_left_support hq v hf, partialIso_right_support hq v hi⟩,
      Subtype.ext v.mul_star_mul⟩
  obtain ⟨u, hu⟩ := finite_partialIso_extends_unitary (cornerPredualEquiv q hq e)
    ((finiteCorner_iff q hq).mp hfinite) vC
  refine ⟨((u : Corner q hq) : M), (u : Corner q hq).property.1,
    (u : Corner q hq).property.2, ?_, ?_, ?_⟩
  · exact congrArg Subtype.val ((Unitary.mem_iff.mp u.property).1)
  · exact congrArg Subtype.val ((Unitary.mem_iff.mp u.property).2)
  · exact congrArg Subtype.val hu

/-- An embedding of a smaller projection into a finite corner extends to an
embedding of a larger projection as soon as the latter embeds in that corner. -/
theorem finite_partialIso_extension (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    {q : M} (hq : IsStarProjection q) (hfinite : FiniteCorner q)
    (v w : PartialIso M) (hvw : v.initial ≤ w.initial)
    (hvq : v.final ≤ q) (hwq : w.final ≤ q) :
    ∃ t : PartialIso M, v ≤ t ∧ t.initial = w.initial ∧ t.final ≤ q := by
  have hvp : (v : M) * w.initial = v := partialIso_right_support w.initial_proj v hvw
  have hqw : q * (w : M) = w := partialIso_left_support hq w hwq
  have hqv : q * (v : M) = v := partialIso_left_support hq v hvq
  let a : PartialIso M := ⟨(v : M) * star (w : M), by
    calc
      ((v : M) * star (w : M)) * star ((v : M) * star (w : M)) *
          ((v : M) * star (w : M)) =
          ((v : M) * w.initial) * star (v : M) * (v : M) * star (w : M) := by
        simp only [star_mul, star_star, PartialIso.initial, mul_assoc]
      _ = (v : M) * star (w : M) := by rw [hvp, v.mul_star_mul]⟩
  have haf : a.final = v.final := by
    change ((v : M) * star (w : M)) * star ((v : M) * star (w : M)) = v.final
    simp only [star_mul, star_star]
    calc
      _ = ((v : M) * w.initial) * star (v : M) := by
        simp only [PartialIso.initial, mul_assoc]
      _ = v.final := by rw [hvp]; rfl
  have hai : a.initial = (w : M) * v.initial * star (w : M) := by
    simp only [a, PartialIso.initial, star_mul, star_star, mul_assoc]
  have haiq : a.initial ≤ q := by
    apply (a.initial_proj.le_iff_mul_eq_right hq).mpr
    rw [hai, ← mul_assoc, ← mul_assoc, hqw]
  obtain ⟨u, hqu, huq, huu, _, hua⟩ := finite_partialIso_extends_in_corner e hq
    hfinite a haiq (by rw [haf]; exact hvq)
  have huwi : u * (w : M) * v.initial = v := by
    have h := congrArg (fun b : M => b * (w : M)) hua
    rw [hai] at h
    change u * ((w : M) * v.initial * star (w : M)) * (w : M) =
      ((v : M) * star (w : M)) * (w : M) at h
    have hiv : v.initial * w.initial = v.initial :=
      (v.initial_proj.le_iff_mul_eq_left w.initial_proj).mp hvw
    calc
      u * (w : M) * v.initial =
          u * ((w : M) * v.initial * star (w : M)) * (w : M) := by
        simp only [mul_assoc]
        change u * ((w : M) * v.initial) =
          u * ((w : M) * (v.initial * w.initial))
        rw [hiv]
      _ = (v : M) := by
        rw [h]
        simpa only [PartialIso.initial, mul_assoc] using hvp
  have hti : star (u * (w : M)) * (u * (w : M)) = w.initial := by
    calc
      _ = star (w : M) * (star u * u) * (w : M) := by
        simp only [star_mul, mul_assoc]
      _ = w.initial := by rw [huu, mul_assoc, hqw]; rfl
  let t : PartialIso M := ⟨u * (w : M), by
    rw [mul_assoc, hti]
    change u * (w : M) * w.initial = u * (w : M)
    rw [mul_assoc, w.mul_initial]⟩
  refine ⟨t, ⟨?_, huwi⟩, hti, ?_⟩
  · change v.initial ≤ star (u * (w : M)) * (u * (w : M))
    rw [hti]
    exact hvw
  · apply (t.final_proj.le_iff_mul_eq_right hq).mpr
    change q * ((u * (w : M)) * star (u * (w : M))) = _
    rw [← mul_assoc, ← mul_assoc, hqu]
    rfl

end KadisonRingrose
end BoundedHochschild

end

end OAI
