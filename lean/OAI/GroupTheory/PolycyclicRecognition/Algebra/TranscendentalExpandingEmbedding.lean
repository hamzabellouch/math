import OAI.GroupTheory.PolycyclicRecognition.Algebra.CountableFieldEmbeddings
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CompleteValuedExtensions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.EssentialFiniteness

namespace OAI

/-! # An expanding complex embedding for a transcendental element -/

noncomputable section
namespace PolycyclicRecognition

theorem exists_transcendental_complex_norm_gt_one
    (F : Type*) [Field F] [Countable F] [Algebra F ℂ] :
    ∃ z : ℂ, Transcendental F z ∧ 1 < ‖z‖ := by
  have : Uncountable ℂ := uncountable_complete_normedField ℂ
  obtain ⟨x, hx⟩ := exists_transcendental_of_countable F ℂ
  obtain ⟨n, hn⟩ := exists_nat_gt (‖x‖ + 1)
  refine ⟨x + n, ?_, ?_⟩
  · intro h
    apply hx
    simpa only [add_sub_cancel_right] using h.sub (isAlgebraic_natCast n)
  · have h := norm_sub_le (x + (n : ℂ)) x
    simp only [add_sub_cancel_left, norm_natCast] at h
    linarith

theorem transcendental_expanding_complex_embedding
    {K : Type*} [Field K] [CharZero K] [Algebra.EssFiniteType ℚ K]
    (z : K) (hz : Transcendental ℚ z) :
    ∃ f : K →+* ℂ, 1 < ‖f z‖ := by
  classical
  have : Uncountable ℂ := uncountable_complete_normedField ℂ
  obtain ⟨w, hw, hwn⟩ := exists_transcendental_complex_norm_gt_one ℚ
  let t : Unit → K := fun _ => z
  let s : Unit → ℂ := fun _ => w
  have ht : AlgebraicIndependent ℚ t := algebraicIndependent_unique_type_iff.mpr hz
  have hs : AlgebraicIndependent ℚ s := algebraicIndependent_unique_type_iff.mpr hw
  let F := IntermediateField.adjoin ℚ (Set.range t)
  let C := IntermediateField.adjoin ℚ (Set.range s)
  let e : F ≃ₐ[ℚ] C := independentAdjoinEquiv ht hs
  let f : F →ₐ[ℚ] ℂ := C.val.comp e.toAlgHom
  have he : f ⟨z, IntermediateField.subset_adjoin ℚ (Set.range t) ⟨(), rfl⟩⟩ = w := by
    exact independentAdjoinEquiv_generator ht hs ()
  let : Countable F := countable_adjoin_of_algebraicIndependent t ht
  let : Algebra F ℂ := f.toRingHom.toAlgebra
  let : Algebra.EssFiniteType F K := Algebra.EssFiniteType.of_comp ℚ F K
  obtain ⟨g⟩ := nonempty_algHom_of_countable_finite_trdeg F K ℂ
  refine ⟨g.toRingHom, ?_⟩
  have hg := g.commutes (⟨z, IntermediateField.subset_adjoin ℚ (Set.range t) ⟨(), rfl⟩⟩ : F)
  change g z = f ⟨z, IntermediateField.subset_adjoin ℚ (Set.range t) ⟨(), rfl⟩⟩ at hg
  change 1 < ‖g z‖
  rw [hg, he]
  exact hwn

end PolycyclicRecognition

end

end OAI
