import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.SmoothFinsetProduct

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open scoped ContDiff
variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fintype ι]

noncomputable def casimirWordsND (B : OrthonormalBasis ι ℝ V) : ℕ → List (List (V →L[ℝ] V))
  | 0 => [[]]
  | k+1 => (casimirWordsND B k).flatMap (fun L =>
      Finset.univ.toList.flatMap (fun i => Finset.univ.toList.map (fun j =>
        angularGeneratorND (B i) (B j)::angularGeneratorND (B i) (B j)::L)))

lemma casimirWordsND_length (B : OrthonormalBasis ι ℝ V) (k : ℕ) :
    (casimirWordsND B k).length=(Fintype.card ι)^(2*k) := by
  induction k with
  | zero => simp [casimirWordsND]
  | succ k ih => simp [casimirWordsND,List.length_flatMap,ih,pow_mul,pow_succ]

lemma casimirWordsND_budget (B : OrthonormalBasis ι ℝ V) (k : ℕ)
    {L : List (V →L[ℝ] V)} (hL : L ∈ casimirWordsND B k) : L.length=2*k := by
  induction k generalizing L with
  | zero => simpa [casimirWordsND] using hL
  | succ k ih =>
    obtain ⟨M,hM,hL⟩ := List.mem_flatMap.mp hL
    obtain ⟨i,hi,hL⟩ := List.mem_flatMap.mp hL
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hL
    simp only [List.length_cons,ih hM]
    omega

lemma casimirOperatorND_eq_sum (B : OrthonormalBasis ι ℝ V) (f : SmoothFunctionND V) :
    casimirOperatorND B f = (1/2:ℂ) • ∑ i : ι, ∑ j : ι,
      angularOperatorND (angularGeneratorND (B i) (B j))
        (angularOperatorND (angularGeneratorND (B i) (B j)) f) := by
  apply Subtype.ext
  funext x
  simp only [Submodule.coe_smul,Pi.smul_apply,Submodule.coe_sum,Finset.sum_apply,smul_eq_mul]
  rfl

lemma casimirWordsND_expansion (B : OrthonormalBasis ι ℝ V) (k : ℕ) (f : SmoothFunctionND V) :
    ((casimirOperatorND B)^k) f = (1/2:ℂ)^k •
      ((casimirWordsND B k).map (fun L => angularWordOperatorND L f)).sum := by
  induction k with
  | zero => simp [casimirWordsND,angularWordOperatorND]
  | succ k ih =>
    rw [pow_succ',Module.End.mul_apply,ih,map_smul,map_list_sum]
    simp only [List.map_map,Function.comp_def,casimirOperatorND_eq_sum]
    have hs : ((casimirWordsND B k).map (fun L => (1/2:ℂ) •
        ∑ i : ι, ∑ j : ι, angularOperatorND (angularGeneratorND (B i) (B j))
          (angularOperatorND (angularGeneratorND (B i) (B j)) (angularWordOperatorND L f)))).sum =
        (1/2:ℂ) • ((casimirWordsND B k).map (fun L =>
          ∑ i : ι, ∑ j : ι, angularOperatorND (angularGeneratorND (B i) (B j))
            (angularOperatorND (angularGeneratorND (B i) (B j)) (angularWordOperatorND L f)))).sum := by
      simp only [List.smul_sum,List.map_map,Function.comp_def]
    rw [hs]
    simp only [smul_smul]
    rw [show (1/2:ℂ)^k*(1/2)=(1/2:ℂ)^(k+1) by rw [pow_succ]]
    congr 1
    simp only [casimirWordsND,List.flatMap_def,List.map_flatten,List.sum_flatten,List.map_map,
      Function.comp_def]
    apply congrArg List.sum
    apply List.map_congr_left
    intro L hL
    simp [angularWordOperatorND,Module.End.mul_apply]

noncomputable def casimirPolynomialTermsND (B : OrthonormalBasis ι ℝ V) (p : Polynomial ℂ) :
    List (ℂ × List (V →L[ℝ] V)) :=
  p.support.toList.flatMap (fun k => (casimirWordsND B k).map (fun L => (p.coeff k*(1/2)^k,L)))

lemma casimirPolynomialTermsND_budget (B : OrthonormalBasis ι ℝ V) (p : Polynomial ℂ)
    {a : ℂ × List (V →L[ℝ] V)} (ha : a ∈ casimirPolynomialTermsND B p) :
    a.2.length ≤ 2*p.natDegree := by
  obtain ⟨k,hk,ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨L,hL,rfl⟩ := List.mem_map.mp ha
  rw [casimirWordsND_budget B k hL]
  exact Nat.mul_le_mul_left 2 (Polynomial.le_natDegree_of_mem_supp _ (Finset.mem_toList.mp hk))

lemma casimirPolynomialTermsND_expansion (B : OrthonormalBasis ι ℝ V) (p : Polynomial ℂ)
    (f : SmoothFunctionND V) : differentialPolynomialND B p f =
      ((casimirPolynomialTermsND B p).map (fun a => a.1 • angularWordOperatorND a.2 f)).sum := by
  conv_lhs => rw [p.as_sum_support]
  simp only [differentialPolynomialND,map_sum,LinearMap.sum_apply,Polynomial.aeval_monomial,
    Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul,LinearMap.smul_apply]
  simp only [casimirPolynomialTermsND,List.flatMap_def,List.map_flatten,List.sum_flatten,
    List.map_map,Function.comp_def]
  rw [← List.sum_toFinset _ p.support.nodup_toList,Finset.toList_toFinset]
  apply Finset.sum_congr rfl
  intro k hk
  rw [casimirWordsND_expansion,smul_smul]
  simp only [List.smul_sum,List.map_map,Function.comp_def]

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
open scoped ContDiff
variable {V ι α : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fintype ι] [DecidableEq α]

noncomputable def polynomialLeibnizTermsND (B : OrthonormalBasis ι ℝ V) (p : Polynomial ℂ)
    (S : Finset α) : List (ℂ × (α → List (V →L[ℝ] V))) :=
  (casimirPolynomialTermsND B p).flatMap (fun a =>
    (orderedAngularAssignmentsND S a.2).map (fun k => (a.1,k)))

lemma polynomialLeibnizTermsND_budget (B : OrthonormalBasis ι ℝ V) (p : Polynomial ℂ)
    (S : Finset α) {a : ℂ × (α → List (V →L[ℝ] V))} (ha : a ∈ polynomialLeibnizTermsND B p S) :
    ∑ i ∈ S, (a.2 i).length ≤ 2*p.natDegree := by
  obtain ⟨b,hb,ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp ha
  rw [orderedAngularAssignmentsND_budget S b.2 hk]
  exact casimirPolynomialTermsND_budget B p hb

lemma polynomialLeibnizTermsND_expansion (B : OrthonormalBasis ι ℝ V) (p : Polynomial ℂ)
    (S : Finset α) (f : α → SmoothFunctionND V) :
    differentialPolynomialND B p (smoothFinsetProductND S f) =
      ((polynomialLeibnizTermsND B p S).map (fun a =>
        a.1 • smoothFinsetProductND S (fun i => angularWordOperatorND (a.2 i) (f i)))).sum := by
  rw [casimirPolynomialTermsND_expansion]
  simp only [polynomialLeibnizTermsND,List.flatMap_def,List.map_flatten,List.sum_flatten,
    List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  rw [angularWordOperatorND_ordered_product]
  simp only [List.smul_sum,List.map_map,Function.comp_def]

lemma polynomialLeibnizTermsND_length (B : OrthonormalBasis ι ℝ V) (p : Polynomial ℂ)
    (S : Finset α) : (polynomialLeibnizTermsND B p S).length ≤
      (casimirPolynomialTermsND B p).length*(max 1 S.card)^(2*p.natDegree) := by
  simp only [polynomialLeibnizTermsND,List.length_flatMap,List.length_map,orderedAngularAssignmentsND_length]
  calc
    _ ≤ ((casimirPolynomialTermsND B p).map (fun _ => (max 1 S.card)^(2*p.natDegree))).sum := by
      apply List.sum_le_sum
      intro a ha
      exact (Nat.pow_le_pow_left (le_max_right 1 S.card) a.2.length).trans
        (Nat.pow_le_pow_right (by omega) (casimirPolynomialTermsND_budget B p ha))
    _ = _ := by simp

lemma polynomialLeibnizTermsND_cost (B : OrthonormalBasis ι ℝ V) (p : Polynomial ℂ)
    (S : Finset α) : ((polynomialLeibnizTermsND B p S).map (fun a => ‖a.1‖)).sum ≤
      ((casimirPolynomialTermsND B p).map (fun a => ‖a.1‖)).sum*(max 1 (S.card:ℝ))^(2*p.natDegree) := by
  simp only [polynomialLeibnizTermsND,List.flatMap_def,List.map_flatten,List.sum_flatten,
    List.map_map,Function.comp_def]
  calc
    _ ≤ ((casimirPolynomialTermsND B p).map (fun a => ‖a.1‖*(max 1 (S.card:ℝ))^(2*p.natDegree))).sum := by
      apply List.sum_le_sum
      intro a ha
      simp only [List.map_const',List.sum_replicate,orderedAngularAssignmentsND_length,nsmul_eq_mul,Nat.cast_pow]
      rw [mul_comm]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (pow_le_pow_left₀ (Nat.cast_nonneg _) (le_max_right 1 (S.card:ℝ)) a.2.length).trans
        (pow_le_pow_right₀ (le_max_left _ _) (casimirPolynomialTermsND_budget B p ha))
    _ = _ := by rw [List.sum_map_mul_right]

end CurrentFalconer
end GraphLiteralSupport
end
end

end OAI
