import Mathlib
import OAI.Analysis.WeakInfiniteness.CoreSelection
import OAI.Analysis.WeakInfiniteness.IdealComparison2
import OAI.Analysis.WeakInfiniteness.PrimitiveIdealTest

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology CStarAlgebra

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma elementCuntz_of_primitive_support
    (hpi : ∀ x : A,0 ≤ x → ProperlyInfinite (diagonalCopies 1 x))
    {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsupp : ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
      NonUnitalRepresentationIrreducible π → π a ≠ 0 → π b ≠ 0) :
    ElementCuntzSubequiv a b := by
  apply generatedClosedIdeal_copies_cuntz hb ha (by norm_num : 1 ≤ 1) (hpi b hb) (k := 1)
  apply mem_closed_ideal_of_irreducible_test (generatedClosedIdeal b hb.isSelfAdjoint)
    (NonUnitalStarSubalgebra.isClosed_topologicalClosure _)
    (fun x hx c => generatedClosedIdeal_mul_left b c hb.isSelfAdjoint hx)
    (fun x hx c => generatedClosedIdeal_mul_right b c hb.isSelfAdjoint hx) ha
  intro H π hπ hI
  by_contra hn
  exact hsupp H π hπ hn (hI b (self_mem_generatedClosedIdeal b hb))

lemma norm_positiveCut_le {a : A} (ha : 0 ≤ a) {r : ℝ} (hr : 0 ≤ r) :
    ‖positiveCut r a‖ ≤ ‖a‖ := by
  apply norm_cfcₙ_le
  intro s hs
  have hs0 : 0 ≤ s := NonnegSpectrumClass.nonneg_of_mem_quasispectrum ha hs
  have hsn : s ≤ ‖a‖ := by simpa only [Real.norm_eq_abs,abs_of_nonneg hs0] using
    (NonUnitalIsometricContinuousFunctionalCalculus.norm_quasispectrum_le a hs ha.isSelfAdjoint)
  rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith) (norm_nonneg a)

lemma exists_left_approx_of_hereditary {a Q : A} (ha : 0 ≤ a)
    (hQ : Q ∈ hereditarySubalgebra a ha.isSelfAdjoint) (x : A) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : A, ‖a*s-Q*x‖ < δ := by
  have hm : Q*x ∈ closure (Set.range (fun s : A => a*s)) := by
    apply closure_minimal _ (isClosed_closure.preimage (continuous_id.mul continuous_const)) hQ
    rintro _ ⟨y,rfl⟩
    apply subset_closure
    exact ⟨y*a*x,by change a*(y*a*x)=(a*y*a)*x; simp only [mul_assoc]⟩
  obtain ⟨_,⟨s,rfl⟩,hs⟩ := Metric.mem_closure_iff.mp hm δ hδ
  exact ⟨s,by simpa only [dist_eq_norm'] using hs⟩

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_star_mul_approx_le (S T U V : A) {δ : ℝ} (hδ : 0 ≤ δ)
    (hU : ‖U‖ ≤ 2) (hV : ‖V‖ ≤ 2) (hSU : ‖S-U‖ ≤ δ) (hTV : ‖T-V‖ ≤ δ) :
    ‖star S*T-star U*V‖ ≤ (4+δ)*δ := by
  have hT : ‖T‖ ≤ 2+δ := by
    calc
      ‖T‖=‖(T-V)+V‖ := by rw [sub_add_cancel]
      _≤‖T-V‖+‖V‖ := norm_add_le _ _
      _≤δ+2 := add_le_add hTV hV
      _=2+δ := by ring
  calc
    ‖star S*T-star U*V‖=‖star (S-U)*T+star U*(T-V)‖ := by congr 1; simp only [star_sub]; noncomm_ring
    _≤‖star (S-U)*T‖+‖star U*(T-V)‖ := norm_add_le _ _
    _≤‖S-U‖*‖T‖+‖U‖*‖T-V‖ := by
      exact add_le_add (by simpa only [norm_star] using norm_mul_le (star (S-U)) T)
        (by simpa only [norm_star] using norm_mul_le (star U) (T-V))
    _≤δ*(2+δ)+2*δ := by gcongr
    _=(4+δ)*δ := by ring

lemma cut_square_cuntz_of_norm_coverage
    (hpi : ∀ x : A,0 ≤ x → ProperlyInfinite (diagonalCopies 1 x))
    {a Q : A} (ha : 0 ≤ a) (hQ : 0 ≤ Q) {r m : ℝ} (hr : 0 < r) (hm : 0 < m)
    (hcover : ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
      NonUnitalRepresentationIrreducible π → r ≤ ‖π a‖ → m ≤ ‖π Q‖) :
    ElementCuntzSubequiv (positiveCut (r^2) (a*a)) (positiveCut (m/2) Q) := by
  have haa : 0 ≤ a*a := by simpa only [ha.star_eq] using star_mul_self_nonneg a
  apply elementCuntz_of_primitive_support hpi (positiveCut_nonneg _ _) (positiveCut_nonneg _ _)
  intro H π hπ hn
  have hn' := norm_lt_of_positiveCut_image_ne_zero π haa (sq_nonneg r) hn
  rw [map_mul] at hn'
  have hnπ : ‖π a*π a‖=‖π a‖^2 := by
    simpa only [(map_nonneg π ha).star_eq,pow_two] using (CStarRing.norm_star_mul_self (x := π a))
  rw [hnπ] at hn'
  have har : r ≤ ‖π a‖ := by nlinarith [norm_nonneg (π a)]
  have hQr := hcover H π hπ har
  have he : π (positiveCut (m/2) Q)=positiveCut (m/2) (π Q) :=
    π.map_cfcₙ (fun s : ℝ => max (s-m/2) 0) Q (by fun_prop)
      (max_eq_right (by linarith)) (by fun_prop) hQ.isSelfAdjoint (map_nonneg π hQ).isSelfAdjoint
  rw [he]
  exact positiveCut_ne_zero_of_lt_norm (map_nonneg π hQ) (by positivity) (by linarith)

end

end WeakPureInfiniteness
end

end OAI
