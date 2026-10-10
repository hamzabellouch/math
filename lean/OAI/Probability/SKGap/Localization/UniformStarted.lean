import Mathlib
import OAI.Probability.SKGap.Localization.CoefficientInputBridge
import OAI.Probability.SKGap.Localization.UniformRecipeClass
import OAI.Probability.SKGap.Matrix.StartedWordClosure
import OAI.Probability.SKGap.Localization.LocalRecipeClass

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series
open SKGap.Noncrossing.ClosedMarked Static
universe u
variable {Ω : Type u} {n : Ω→ℕ}
variable {ι κ σ κ₀ σ₀ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype σ]
variable [Fintype κ₀] [DecidableEq κ₀] [Fintype σ₀]

lemma errorBudget_mono {r : ℝ} (hr : 0 ≤ r) {s f s' f' : ℕ→ℝ}
    (hs : ∀a,s a ≤ s' a) (hf : ∀a,f a ≤ f' a) (k : ℕ) :
    (errorBudget r s f k).1 ≤ (errorBudget r s' f' k).1 ∧
    (errorBudget r s f k).2 ≤ (errorBudget r s' f' k).2 := by
  induction k using Nat.strong_induction_on with
  | h k ih=>
    rw [errorBudget,errorBudget]
    have h1:=Finset.sum_le_sum (fun (b : Fin k) (_:b∈Finset.univ)=>(ih b b.isLt).1)
    have h2:=Finset.sum_le_sum (fun (b : Fin k) (_:b∈Finset.univ)=>(ih b b.isLt).2)
    exact ⟨add_le_add (hs k) h2,add_le_add (add_le_add (add_le_add (hs k) h2)
      (mul_le_mul_of_nonneg_left h1 hr)) (hf k)⟩

theorem uniform_started_control (E : ∀a,Set (Spin (n a)))
    (D : ∀a,OrdinaryData (n a) ι κ σ) (I : ∀a,OrdinaryData (n a) Unit κ₀ σ₀)
    (w y : ∀a,VectorFields (n a))
    (T : ∀a,Spin (n a)→ι→SourceTree (Fin (n a)→ℝ))
    (t : ∀a,Spin (n a)→SourceTree (Fin (n a)→ℝ))
    (N L : ℕ) (c : LocalConstants) (j : ℝ)
    (hj : ∀a,(D a).j=j) (hij : ∀a,(I a).j=j) (hJ : ∀a,(D a).J=(I a).J)
    (h : ∀a x,x∈E a→LocalOrdinaryInput (D a) (T a x) x N c)
    (hW : ∀a x,x∈E a→w a x=(I a).sourceOf 1 (fun _=>y a) x)
    (hWf : ∀a x,x∈E a→∀i,w a (flip x i)=(I a).sourceOf 1 (fun _=>y a) (flip x i))
    (hY : ∀a x,x∈E a→y a x=(I a).fieldOf 1 (fun _=>w a) (fun _=>y a) x)
    (hYf : ∀a x,x∈E a→∀i,y a (flip x i)=(I a).fieldOf 1 (fun _=>w a) (fun _=>y a) (flip x i))
    (ha0 : ∀a x,x∈E a→∀i,0 ≤ (I a).implicitCoefficient x i)
    (hS : ∀a x,x∈E a→(1-SKGap.pathDiagonal ((I a).implicitCoefficient x) 1*
      ((I a).J-((I a).j*siteMean (I a).implicitCoefficient x) • 1)*SKGap.pathDiagonal ((I a).implicitCoefficient x) 1).PosDef)
    {C F B₀ M B Q : ℝ} (hB₀ : 0 ≤ B₀) (hM : 0 ≤ M) (hB : 0 ≤ B) (hQ : 0 ≤ Q) (hC : 0 ≤ C) (hF : 0 ≤ F)
    (hw₀ : ∀a x,x∈E a→SmallBound (w a) x B₀) (hy₀ : ∀a x,x∈E a→SmallBound (y a) x B₀)
    (hp₀ : ∀a x,x∈E a→vectorNorm ((I a).implicitPartial (y a) x) ≤ B₀)
    (hP : ∀a x,x∈E a→TraceControl ((I a).implicitSourcePrimitive (t a x) (y a) x) C)
    (hF' : ∀a x,x∈E a→TraceControl ((I a).implicitFieldPrimitive (t a x) (w a) (y a) x) F)
    (ha : ∀a x,x∈E a→∀i,|(I a).implicitCoefficient x i| ≤ c.A)
    (hm : ∀a x,x∈E a→∀l,Marked.mass (GradedWords.ordinaryWords j (T a x l)).1 ≤ Q ∧ Marked.mass (GradedWords.ordinaryWords j (T a x l)).2 ≤ Q)
    (hm₀ : ∀a x,x∈E a→Marked.mass (GradedWords.ordinaryWords j (t a x)).1 ≤ Q ∧ Marked.mass (GradedWords.ordinaryWords j (t a x)).2 ≤ Q)
    (hT : ∀a x,x∈E a→∀l,GradedControl c.A L (GradedWords.ordinaryWords j (T a x l)).1 ∧ GradedControl c.A L (GradedWords.ordinaryWords j (T a x l)).2)
    (ht : ∀a x,x∈E a→GradedControl c.A L (GradedWords.ordinaryWords j (t a x)).1 ∧ GradedControl c.A L (GradedWords.ordinaryWords j (t a x)).2)
    (hw : ∀a x,x∈E a→ClosedWordTestBound j ((I a).implicitCoefficient x) (D a).J c.A M (2*N+5))
    (hd : ∀a x,x∈E a→ClosedWordDiagramBound j ((I a).implicitCoefficient x) (D a).J c.A B (L+2*N+3)) :
    ∃K : ℝ,0 ≤ K ∧ ∀a x,x∈E a→SmallBound ((D a).startedSource (w a) (y a) N) x K ∧
      (∀l,SmallBound ((D a).startedPartial (w a) (y a) N l) x K) ∧
      (∑i,|derivativeMatrix ((D a).startedSource (w a) (y a) N) x i i|) ≤ K := by
  let W:=c.startedNormBudget j (Fintype.card ι) B₀
  let q:=|j| *c.A
  let Cs:=fun a=>if a=0 then C+F else c.startedSourceCost j (Fintype.card ι) (Fintype.card σ) B₀ a
  let Cf:=fun a=>if a=0 then q*(C+F)+F else c.startedFieldCost j (Fintype.card ι) B₀ a
  let R:=errorBudget q Cs Cf
  let V:=startedTraceBudget ((Fintype.card ι:ℝ)*((2+|j|)*Q)) (2+|j| *c.A) W (initialTraceBudget j c.A B₀ Q)
  let K:=|W N|+|V N*B+(R N).1*M|
  have hWK : W N ≤ K:=(le_abs_self _).trans (le_add_of_nonneg_right (abs_nonneg _))
  have hRK : V N*B+(R N).1*M ≤ K:=(le_abs_self _).trans (le_add_of_nonneg_left (abs_nonneg _))
  refine ⟨K,by dsimp [K];positivity,fun a x hx=>?_⟩
  have hh:=(D a).implicit_started_word_closure (I a) (w a) (y a) (T a x) (t a x)
    ((hj a).trans (hij a).symm) (hJ a) x N L c (h a x hx) (hW a x hx) (hWf a x hx) (hY a x hx) (hYf a x hx)
    (ha0 a x hx) (hS a x hx) hB₀ hM hB hQ (hw₀ a x hx) (hy₀ a x hx) (hp₀ a x hx) (hP a x hx) (hF' a x hx)
    (ha a x hx) (by simpa only [hj a] using hm a x hx) (by simpa only [hj a] using hm₀ a x hx)
    (by simpa only [hj a] using hT a x hx) (by simpa only [hj a] using ht a x hx)
    (by simpa only [hj a] using hw a x hx) (by simpa only [hj a] using hd a x hx) N le_rfl
  rw [hj a,hij a] at hh
  have hmean : |j*siteMean (I a).implicitCoefficient x| ≤ q := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (coefficient_mean_value (I a).implicitCoefficient x c.A_nonneg (ha a x hx)) (abs_nonneg j)
  have hb := errorBudget_mono (mul_nonneg (abs_nonneg j) c.A_nonneg)
    (fun k=>show Cs k ≤ Cs k from le_rfl)
    (s:=Cs) (f:=fun k=>if k=0 then |j*siteMean (I a).implicitCoefficient x| *(C+F)+F else c.startedFieldCost j (Fintype.card ι) B₀ k)
    (f':=Cf) (fun k=>by
      dsimp [Cf,q]
      split_ifs
      · exact add_le_add (mul_le_mul_of_nonneg_right hmean (add_nonneg hC hF)) le_rfl
      · rfl) N
  refine ⟨hh.1.mono hWK,fun l=>(hh.2.1 l).mono hWK,?_⟩
  exact (hh.2.2.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hb.1 hM))).trans hRK

theorem local_uniform_auxiliary_mean (E : ∀a,Set (Spin (n a))) (D : ∀a,OrdinaryData (n a) ι κ σ)
    (T : ∀a,Spin (n a)→ι→SourceTree (Fin (n a)→ℝ)) (N : ℕ) (c : LocalConstants)
    (h : ∀a x,x∈flipNeighborhood (E a)→LocalOrdinaryInput (D a) (T a x) x N c) (b : Fin N) :
    LocalUniformMultiplier E (fun a=>siteMean ((D a).auxCoefficient N b)) := by
  refine ⟨c.A,c.row (Fintype.card ι),c.A_nonneg,c.row_nonneg _,
    fun a x hx=>(h a x hx).mean_bound N le_rfl b,fun a x hx=>?_⟩
  have hm:=coefficient_mean_difference ((D a).auxCoefficient N b) x (c.row_nonneg _)
    ((h a x (Or.inl hx)).aux_bound N le_rfl b).difference
  have hs:=pow_le_pow_left₀ (norm_nonneg _) hm 2
  rw [EuclideanSpace.real_norm_sq_eq] at hs
  exact hs

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Static Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series SKGap.Noncrossing.ClosedMarked
universe u
variable {Ω : Type u} {n : Ω→ℕ} {κ κ₀ σ₀ : Type} [Fintype κ] [DecidableEq κ] [Fintype κ₀] [DecidableEq κ₀] [Fintype σ₀]
variable {M : ℕ} {j : ℝ} {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}
variable {E : ∀a,Set (Spin (n a))} {Θ : ∀a,κ→Observables (n a)} {w y : ∀a,VectorFields (n a)}

theorem finite_started_control (D₀ : ∀a,OrdinaryData (n a) (Fin M) κ Unit)
    (K₀ : ℝ) (H₀ : LocalFamilyRecipe E j J h Θ w y D₀ 1 0 K₀)
    (I : ∀a,OrdinaryData (n a) Unit κ₀ σ₀)
    (hij : ∀a,(I a).j=j) (hIJ : ∀a,(I a).J=J a)
    (T : ∀a,Spin (n a)→Fin M→SourceTree (Fin (n a)→ℝ))
    (t : ∀a,Spin (n a)→SourceTree (Fin (n a)→ℝ))
    (c : LocalConstants) (A : ℝ)
    (hc : ∀a x,x∈flipNeighborhood (E a)→LocalOrdinaryInput (D₀ a) (T a x) x 1 c)
    (index : Fin M→κ)
    (hθ : ∀a q,(D₀ a).θ (index q)=fun x=>j*(onsager j (J a) (h a) (q.val+1) x-onsager j (J a) (h a) q.val x))
    (Nmax L : ℕ) (C F B₀ W B Q : ℝ) (hA : 1≤A)
    (hC : 0≤C) (hF : 0≤F) (hB₀ : 0≤B₀) (hW : 0≤W) (hB : 0≤B) (hQ : 0≤Q)
    (hW₀ : ∀a x,x∈flipNeighborhood (E a)→w a x=(I a).sourceOf 1 (fun _=>y a) x)
    (hWf : ∀a x,x∈flipNeighborhood (E a)→∀i,w a (flip x i)=(I a).sourceOf 1 (fun _=>y a) (flip x i))
    (hY₀ : ∀a x,x∈flipNeighborhood (E a)→y a x=(I a).fieldOf 1 (fun _=>w a) (fun _=>y a) x)
    (hYf : ∀a x,x∈flipNeighborhood (E a)→∀i,y a (flip x i)=(I a).fieldOf 1 (fun _=>w a) (fun _=>y a) (flip x i))
    (ha0 : ∀a x,x∈flipNeighborhood (E a)→∀i,0≤(I a).implicitCoefficient x i)
    (hS : ∀a x,x∈flipNeighborhood (E a)→(1-SKGap.pathDiagonal ((I a).implicitCoefficient x) 1*
      ((I a).J-((I a).j*siteMean (I a).implicitCoefficient x) • 1)*SKGap.pathDiagonal ((I a).implicitCoefficient x) 1).PosDef)
    (hw₀ : ∀a x,x∈flipNeighborhood (E a)→SmallBound (w a) x B₀)
    (hy₀ : ∀a x,x∈flipNeighborhood (E a)→SmallBound (y a) x B₀)
    (hp₀ : ∀a x,x∈flipNeighborhood (E a)→vectorNorm ((I a).implicitPartial (y a) x)≤B₀)
    (hP : ∀a x,x∈flipNeighborhood (E a)→TraceControl ((I a).implicitSourcePrimitive (t a x) (y a) x) C)
    (hF' : ∀a x,x∈flipNeighborhood (E a)→TraceControl ((I a).implicitFieldPrimitive (t a x) (w a) (y a) x) F)
    (ha : ∀a x,x∈flipNeighborhood (E a)→∀i,|(I a).implicitCoefficient x i|≤A)
    (hm : ∀a x,x∈flipNeighborhood (E a)→∀l,Marked.mass (GradedWords.ordinaryWords j (T a x l)).1≤Q ∧ Marked.mass (GradedWords.ordinaryWords j (T a x l)).2≤Q)
    (hm₀ : ∀a x,x∈flipNeighborhood (E a)→Marked.mass (GradedWords.ordinaryWords j (t a x)).1≤Q ∧ Marked.mass (GradedWords.ordinaryWords j (t a x)).2≤Q)
    (hT : ∀a x,x∈flipNeighborhood (E a)→∀l,GradedControl A L (GradedWords.ordinaryWords j (T a x l)).1 ∧ GradedControl A L (GradedWords.ordinaryWords j (T a x l)).2)
    (ht : ∀a x,x∈flipNeighborhood (E a)→GradedControl A L (GradedWords.ordinaryWords j (t a x)).1 ∧ GradedControl A L (GradedWords.ordinaryWords j (t a x)).2)
    (hw : ∀a x,x∈flipNeighborhood (E a)→ClosedWordTestBound j ((I a).implicitCoefficient x) (J a) A W (2*Nmax+5))
    (hd : ∀a x,x∈flipNeighborhood (E a)→ClosedWordDiagramBound j ((I a).implicitCoefficient x) (J a) A B (L+2*Nmax+3)) :
    FiniteLocalRecipeControl E j J h Θ w y M Nmax A := by
  have transfer {σ : Type} [Fintype σ] (D : ∀a,OrdinaryData (n a) (Fin M) κ σ)
      (N p : ℕ) (K : ℝ) (H : LocalFamilyRecipe E j J h Θ w y D N p K) (hKA : K≤A) :
      ∃c' : LocalConstants,c'.A=A ∧ ∀a x,x∈flipNeighborhood (E a)→LocalOrdinaryInput (D a) (T a x) x N c' := by
    obtain ⟨S,hS,hs⟩:=H.seed
    refine ⟨c.withCoefficient A S hA hS,rfl,fun a x hx=>?_⟩
    obtain ⟨hJ,hj,hH,hp,hθ'⟩:=H.sameEnvironment H₀ a
    exact (hc a x hx).with_coefficients (D a) hJ hj hH hp hθ' N A S hA hS (hs a)
      ((H.coefficients a x hx).mono hKA)
  constructor
  · intro σ inst D N p K H hN hKA
    obtain ⟨c',hAc',hi⟩:=transfer D N p K H hKA
    apply uniform_started_control (fun a=>flipNeighborhood (E a)) D I w y T t N L c' j H.coupling hij
      (fun a=>(H.interaction a).trans (hIJ a).symm) hi hW₀ hWf hY₀ hYf ha0 hS hB₀ hW hB hQ hC hF hw₀ hy₀ hp₀ hP hF'
    · simpa only [hAc'] using ha
    · exact hm
    · exact hm₀
    · simpa only [hAc'] using hT
    · simpa only [hAc'] using ht
    · intro a x hx v hl hi hb
      rw [H.interaction a,hAc'] at *
      exact hw a x hx v (hl.trans (by omega)) hi hb
    · intro a x hx v hl hi hb
      rw [H.interaction a,hAc'] at *
      exact hd a x hx v (hl.trans (by omega)) hi hb
  · intro σ inst D N p K H hN hKA b
    obtain ⟨c',hAc',hi⟩:=transfer D N p K H hKA
    exact local_uniform_auxiliary_mean E D T N c' hi b
  · intro q
    refine ⟨|j|,c.V,abs_nonneg _,c.V_nonneg,
      fun a x hx=>onsager_parameter_bound j (J a) (h a) q.val x,fun a x hx=>?_⟩
    have hh' : ‖derivativeVector ((D₀ a).θ (index q)) x‖≤c.V :=
      (Finset.single_le_sum (fun r _=>norm_nonneg (derivativeVector ((D₀ a).θ r) x))
        (Finset.mem_univ (index q))).trans (hc a x (Or.inl hx)).parameter
    have hs:=pow_le_pow_left₀ (norm_nonneg _) hh' 2
    rw [hθ a q,EuclideanSpace.real_norm_sq_eq] at hs
    exact hs

end SKGapCutoff.Recipe

end
end

end OAI
