import Mathlib
import OAI.Probability.SKGap.Stability.WordDiagStable
import OAI.Probability.SKGap.Gaussian.DiagonalNormTail
import OAI.Probability.SKGap.Stability.WordOrdinaryAgreement

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology

theorem zeroDiag_exact_word_uniform_prediction {j A D c : ℝ} (hj : 0<j) (hA : 0<A)
    (hs : sqrt j*A<1) (hD : 1≤D) (hAD : A≤D) (hc : 0<c) (L : ℕ) :
    ∃ (C : ℝ) (N : ℕ),0<C ∧ 0<N ∧ ∀ n,N≤n → ∀ p : Bool,
      (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
      {g | ∃ (a : Fin n→ℝ) (F : List (WordLetter (Fin n))),
          (∀ i,a i∈Icc 0 A) ∧ F.length≤L ∧ (∀ l∈F,l.bounded D) ∧ inverseCount F≤1 ∧
          c≤ComplexSpectral.lowerRayleigh (liftMatrix (stabilityMatrix a 1
            ((j/(n:ℝ))*∑ b,a b) (removeDiagonal (goeMatrix (j/n) g)))) ∧
          C< matrixWordSeminorm p
            (exactWord j a F (removeDiagonal (goeMatrix (j/n) g))-Matrix.diagonal (wordPrediction j a 1 F))} ≤
      (wordPatternSet L L).card*ENNReal.ofReal (3*exp (-(n:ℝ)))+
        ENNReal.ofReal (exp (-2*(n:ℝ)/(π^2*(sqrt (2*j))^2))) +
        (ENNReal.ofReal (2*exp (-(n:ℝ)/(π^2*j)))+
          ENNReal.ofReal (2*(n:ℝ)*exp (-1/(8*(j/n))))) := by
  obtain ⟨C,N,hC,hN,ht⟩ := zeroDiag_exact_word_simultaneous_prediction hj hA hs hD hAD hc L
  refine ⟨C,N,hC,hN,?_⟩
  intro n hn p
  have hn0 : 0<n := hN.trans_le hn
  let B := {g : MatrixCoordinates (Fin n)→ℝ | ∃ (a : Fin n→ℝ) (F : List (WordLetter (Fin n))),
    (∀ i,a i∈Icc 0 A) ∧ F.length≤L ∧ (∀ l∈F,l.bounded D) ∧ inverseCount F≤1 ∧
      c≤ComplexSpectral.lowerRayleigh (liftMatrix (stabilityMatrix a 1
        ((j/(n:ℝ))*∑ b,a b) (removeDiagonal (goeMatrix (j/n) g)))) ∧
      C< matrixWordSeminorm p
        (exactWord j a F (removeDiagonal (goeMatrix (j/n) g))-Matrix.diagonal (wordPrediction j a 1 F))}
  let E := {g | opNorm (removeDiagonal (goeMatrix (j/n) g))≤2*sqrt j+1+1 ∧ g∈B}
  let V := {g : MatrixCoordinates (Fin n)→ℝ | 2*sqrt j+1+1<opNorm (removeDiagonal (goeMatrix (j/n) g))}
  have hs : B⊆E∪V := by
    intro g hg
    by_cases h : opNorm (removeDiagonal (goeMatrix (j/n) g))≤2*sqrt j+1+1
    · exact Or.inl ⟨h,hg⟩
    · exact Or.inr (lt_of_not_ge h)
  exact ((measure_mono hs).trans (measure_union_le E V)).trans
    (add_le_add (ht n hn p) (zeroDiagGOE_norm_tail hj hn0))
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology

theorem exactWord_uniform_opNorm {j A D c R : ℝ} (hj : 0≤j) (hA : 0≤A)
    (hD : 0≤D) (hc : 0<c) (hR : 0≤R) (L : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ n,0<n → ∀ (a : Fin n→ℝ) (F : List (WordLetter (Fin n)))
      (M : Matrix (Fin n) (Fin n) ℝ),
      (∀ i,a i∈Icc 0 A) → F.length≤L → (∀ l∈F,l.bounded D) → Mᵀ=M → opNorm M≤R →
      (inverseCount F=0 ∨ c≤ComplexSpectral.lowerRayleigh (liftMatrix (stabilityMatrix a 1 ((j/(n:ℝ))*∑ b,a b) M))) →
      opNorm (exactWord j a F M)≤C := by
  let hi := max c (2+A*(R+j*A))
  obtain ⟨f,hf,_⟩ := exists_schwartz_inverse hc (le_max_left c (2+A*(R+j*A)))
  let B := actualWordBound f R j A D
  have hB : 1≤B := by
    have hh := path_constants_nonneg f hR hj hA
    unfold B actualWordBound
    linarith
  refine ⟨B^L,pow_pos (lt_of_lt_of_le zero_lt_one hB) _,?_⟩
  intro n hn a F M ha hFL hF hM hMR hstable
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  rcases hstable with hordinary|hstable
  · have he := actualWord_agrees_no_inverse f hR j a M hM hMR F hordinary
    rw [←he]
    exact ((actualWord_bounds f hR hj hA hD (fun i=>(ha i).1) (fun i=>(ha i).2)
      (show (1:ℝ)∈Icc 0 1 from ⟨zero_le_one,le_rfl⟩) F hF).1 M).trans (pow_le_pow_right₀ hB hFL)
  · have haq : ∀ i,0≤a i := fun i=>(ha i).1
    have haA : ∀ i,a i≤A := fun i=>(ha i).2
    have hq := diagonal_mean_bounds hj haq haA
    simp only [Fintype.card_fin] at hq
    have hb := stabilityMatrix_opNorm haq haA hA (show (1:ℝ)∈Icc 0 1 from ⟨zero_le_one,le_rfl⟩) hq.1 hMR
    have hnrm : opNorm (stabilityMatrix a 1 ((j/(n:ℝ))*∑ b,a b) M)≤hi := by
      apply hb.trans
      apply le_trans _ (le_max_right c (2+A*(R+j*A)))
      nlinarith
    have hu : -hi≤ComplexSpectral.lowerRayleigh (-liftMatrix (stabilityMatrix a 1 ((j/(n:ℝ))*∑ b,a b) M)) :=
      (neg_le_neg hnrm).trans (lowerRayleigh_neg_lift_ge _)
    rw [stabilityMatrix_path_rep a haq zero_le_one] at hstable hu
    have he := actualWord_agrees f hc hf hR j haq M hM hMR
      (by simpa only [Fintype.card_fin] using hstable) (by simpa only [Fintype.card_fin] using hu) F
    rw [←he]
    exact ((actualWord_bounds f hR hj hA hD haq haA
      (show (1:ℝ)∈Icc 0 1 from ⟨zero_le_one,le_rfl⟩) F hF).1 M).trans (pow_le_pow_right₀ hB hFL)
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Polynomial
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma wordRecursionAt_degree_budget (a : ι→ℝ) (P Q : List (WordLetter ι))
    (t : WordRecursionTerm ι) (ht : t∈wordRecursionAt a P Q) :
    (if t.inversePartner then 1 else 0)+ordinaryCount t.inner+ordinaryCount t.outer ≤
      ordinaryCount (P++(.noise::Q)) := by
  dsimp only [wordRecursionAt] at ht
  rw [List.mem_append] at ht
  rcases ht with ht|ht
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ht
    have hh := (wordPartners_counts a P c hc).1
    cases hi : c.inversePartner <;> simp [WordCut.asLeft,hi] at * <;> omega
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ht
    have hh := (wordPartners_counts a Q c hc).1
    cases hi : c.inversePartner <;> simp [WordCut.asRight,hi] at * <;> omega

omit [Fintype ι] in
lemma wordRecursionTerms_degree_budget (a : ι→ℝ) (F : List (WordLetter ι))
    (t : WordRecursionTerm ι) (ht : t∈wordRecursionTerms a F) :
    (if t.inversePartner then 1 else 0)+ordinaryCount t.inner+ordinaryCount t.outer ≤ ordinaryCount F := by
  unfold wordRecursionTerms at ht
  cases hs : firstNoiseSplit F with
  | none => simp [hs] at ht
  | some pq =>
    rcases pq with ⟨P,Q⟩
    have he := firstNoiseSplit_some F P Q hs
    simp only [hs] at ht
    simpa only [he] using wordRecursionAt_degree_budget a P Q t ht

def wordPredictionPolynomial (j : ℝ) (a : ι→ℝ) (F : List (WordLetter ι)) (i : ι) : ℝ[X] :=
  if ordinaryCount F=0 then C (wordDiagonal F i) else
    ((wordRecursionTerms a F).attach.map (fun th=>
      (if th.val.inversePartner then X else 1)*C j*
        (C ((Fintype.card ι:ℝ)⁻¹)*(∑ k,wordPredictionPolynomial j a th.val.inner k))*
          wordPredictionPolynomial j a th.val.outer i)).sum
termination_by ordinaryCount F
decreasing_by
  · exact (wordRecursionTerms_decreases a F th.val th.property).2
  · exact (wordRecursionTerms_decreases a F th.val th.property).1

lemma polynomial_list_degree_le (l : List ℝ[X]) (n : ℕ) (h : ∀ p∈l,p.natDegree≤n) : l.sum.natDegree≤n := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.sum_cons]
    exact (natDegree_add_le p l.sum).trans (max_le (h p (List.mem_cons_self)) (ih (fun q hq=>h q (List.mem_cons_of_mem _ hq))))
lemma polynomial_eval_list_sum (l : List ℝ[X]) (z : ℝ) :
    eval z l.sum=(l.map (eval z)).sum := by
  induction l with
  | nil => simp
  | cons p l ih => simp only [List.sum_cons,eval_add,List.map_cons,ih]

theorem wordPredictionPolynomial_spec (j : ℝ) (a : ι→ℝ) (F : List (WordLetter ι)) :
    ∀ i,(wordPredictionPolynomial j a F i).natDegree≤ordinaryCount F ∧
      ∀ z,eval z (wordPredictionPolynomial j a F i)=wordPrediction j a z F i := by
  generalize hk : ordinaryCount F=k
  induction k using Nat.strong_induction_on generalizing F with
  | h k ih =>
    have hsub (t : WordRecursionTerm ι) (ht : t∈wordRecursionTerms a F) :
        (∀ i,(wordPredictionPolynomial j a t.inner i).natDegree≤ordinaryCount t.inner ∧
          ∀ z,eval z (wordPredictionPolynomial j a t.inner i)=wordPrediction j a z t.inner i) ∧
        (∀ i,(wordPredictionPolynomial j a t.outer i).natDegree≤ordinaryCount t.outer ∧
          ∀ z,eval z (wordPredictionPolynomial j a t.outer i)=wordPrediction j a z t.outer i) := by
      have hh := wordRecursionTerms_decreases a F t ht
      exact ⟨ih _ (by omega) _ rfl,ih _ (by omega) _ rfl⟩
    intro i
    by_cases ho : ordinaryCount F=0
    · rw [wordPredictionPolynomial]
      simp only [ho,ite_true,natDegree_C,zero_le,eval_C,true_and]
      intro z
      exact (wordPrediction_base j a z F i ho).symm
    constructor
    · rw [wordPredictionPolynomial,ite_eq_right ho]
      apply polynomial_list_degree_le
      intro p hp
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hp
      have hs := hsub t.val t.property
      have hinner : (C ((Fintype.card ι:ℝ)⁻¹)*(∑ u,wordPredictionPolynomial j a t.val.inner u)).natDegree≤ordinaryCount t.val.inner :=
        (natDegree_C_mul_le _ _).trans (natDegree_sum_le_of_forall_le _ _ (fun u _=>(hs.1 u).1))
      have hw : (if t.val.inversePartner then (X:ℝ[X]) else 1).natDegree≤(if t.val.inversePartner then 1 else 0) := by
        cases t.val.inversePartner <;> simp
      have hj : ((if t.val.inversePartner then (X:ℝ[X]) else 1)*C j).natDegree≤(if t.val.inversePartner then 1 else 0) :=
        (natDegree_mul_C_le _ _).trans hw
      have hb := wordRecursionTerms_degree_budget a F t.val t.property
      rw [hk] at hb
      exact natDegree_mul_le.trans ((add_le_add (natDegree_mul_le.trans (add_le_add hj hinner)) (hs.2 i).1).trans hb)
    · intro z
      rw [wordPredictionPolynomial,ite_eq_right ho,wordPrediction,ite_eq_right ho,polynomial_eval_list_sum,List.map_map]
      congr 1
      apply List.map_congr_left
      intro t ht
      have hs := hsub t.val t.property
      simp only [Function.comp_def,eval_mul,eval_C,eval_finsetSum]
      simp_rw [(hs.1 _).2 z,(hs.2 _).2 z]
      cases t.val.inversePartner <;> simp only [Bool.false_eq_true,ite_false,ite_true,eval_one,eval_X] <;> ring
end SKGap
end
end

end OAI
