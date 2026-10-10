import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Estimates.CasimirWords

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open scoped ContDiff
variable {V ι α : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fintype ι] [DecidableEq α]

lemma orderedAngularAssignmentsND_sublist (S : Finset α) (L : List (V →L[ℝ] V))
    {k : α → List (V →L[ℝ] V)} (hk : k ∈ orderedAngularAssignmentsND S L) (i : α) : List.Sublist (k i) L := by
  induction L generalizing k with
  | nil => simp only [orderedAngularAssignmentsND,List.mem_singleton] at hk; subst k; exact .refl _
  | cons A L ih =>
    obtain ⟨l,hl,hk⟩ := List.mem_flatMap.mp hk
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hk
    by_cases hij : i=j
    · subst i
      simpa only [Function.update_self] using (ih hl).cons_cons A
    · simpa only [Function.update_of_ne hij] using (ih hl).cons A

noncomputable def polynomialAngularSubwordsND (B : OrthonormalBasis ι ℝ V) (p : Polynomial ℂ) :
    Finset (List (V →L[ℝ] V)) := by
  classical
  exact ((casimirPolynomialTermsND B p).flatMap (fun a => a.2.sublists)).toFinset

lemma polynomialLeibnizTermsND_subword (B : OrthonormalBasis ι ℝ V) (p : Polynomial ℂ)
    (S : Finset α) {a : ℂ × (α → List (V →L[ℝ] V))}
    (ha : a ∈ polynomialLeibnizTermsND B p S) (i : α) :
    a.2 i ∈ polynomialAngularSubwordsND B p := by
  classical
  obtain ⟨b,hb,ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ha
  apply List.mem_toFinset.mpr
  exact List.mem_flatMap.mpr ⟨b,hb,List.mem_sublists.mpr (orderedAngularAssignmentsND_sublist S b.2 hk i)⟩

lemma polynomialAngularSubwordsND_budget (B : OrthonormalBasis ι ℝ V) (p : Polynomial ℂ)
    {L : List (V →L[ℝ] V)} (hL : L ∈ polynomialAngularSubwordsND B p) : L.length ≤ 2*p.natDegree := by
  classical
  obtain ⟨b,hb,hL⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hL)
  exact (List.mem_sublists.mp hL).length_le.trans (casimirPolynomialTermsND_budget B p hb)

end CurrentFalconer
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open Set Metric
open scoped ContDiff Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma compact_contDiffOn_derivative_bound {f : E → F} {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (hf : ContDiffOn ℝ ∞ f U)
    (m : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ j ≤ m, ∀ x ∈ K,
      ‖iteratedFDerivWithin ℝ j f U x‖ ≤ C := by
  have hbound (j : ℕ) : ∃ C : ℝ, ∀ x ∈ K,
      ‖iteratedFDerivWithin ℝ j f U x‖ ≤ C :=
    hK.exists_bound_of_continuousOn
      ((hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤)) hU.uniqueDiffOn).mono hKU)
  induction m with
  | zero =>
    obtain ⟨C,hC⟩ := hbound 0
    refine ⟨max 1 C, le_max_left _ _, ?_⟩
    intro j hj x hx
    have : j=0 := Nat.eq_zero_of_le_zero hj
    subst j
    exact (hC x hx).trans (le_max_right _ _)
  | succ m ih =>
    obtain ⟨D,hD,hboundD⟩ := ih
    obtain ⟨C,hC⟩ := hbound (m+1)
    refine ⟨max D C, hD.trans (le_max_left _ _), ?_⟩
    intro j hj x hx
    by_cases hjm : j ≤ m
    · exact (hboundD j hjm x hx).trans (le_max_left _ _)
    · have : j=m+1 := by omega
      subst j
      exact (hC x hx).trans (le_max_right _ _)

end CurrentFalconer
end GraphLiteralSupport
end
end

end OAI
