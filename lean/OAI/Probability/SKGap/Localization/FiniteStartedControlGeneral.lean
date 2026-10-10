import Mathlib
import OAI.Probability.SKGap.Localization.BufferedSelectionDiagnostics
import OAI.Probability.SKGap.Localization.RecipeArgumentPullback
import OAI.Probability.SKGap.Localization.UniformStarted

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Recipe
open Primary Static Matrix SKGap SKGap.Noncrossing SKGap.Noncrossing.Primary SKGap.Noncrossing.Primary.Tensor.Series SKGap.Noncrossing.ClosedMarked
universe u
variable {σ₁ : Type} [Fintype σ₁]
variable {Ω : Type u} {n : Ω→ℕ} {κ κ₀ σ₀ : Type} [Fintype κ] [DecidableEq κ] [Fintype κ₀] [DecidableEq κ₀] [Fintype σ₀]
variable {M : ℕ} {j : ℝ} {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}
variable {E : ∀a,Set (Spin (n a))} {Θ : ∀a,κ→Observables (n a)} {w y : ∀a,VectorFields (n a)}

theorem finite_started_control_seeds (D₀ : ∀a,OrdinaryData (n a) (Fin M) κ σ₁)
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

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary SKGap.Stein Static

variable {n M : ℕ}

def literalFullParameters (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (a c : Spin n→ℝ) : Fin M⊕Bool→Spin n→ℝ :=
  Sum.elim (fun q x=>j*(onsager j J h (q.val+1) x-onsager j J h q.val x))
    (fun b x=>if b then Real.sqrt (n:ℝ)*c x else a x)

def literalFullData (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (l : Fin M) (f : KernelExpr) (a c : Spin n→ℝ) (r e : Fin n→ℝ) :
    OrdinaryData n (Fin M) (Fin M⊕Bool) Bool :=
  (literalInitial J j (Real.sqrt (n:ℝ)) f (fld j J h l.val) (mag j J h l.val) a c r e).argumentPullback (fun _:Unit=>l) Sum.inr (fun q=>fld j J h q.val)
      (fun q=>mag j J h q.val) (literalFullParameters j J h a c)

lemma literalFullData_admissible (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (l : Fin M) (f : KernelExpr) (a c : Spin n→ℝ) (r e : Fin n→ℝ)
    (N p : ℕ) (hp : p≤l.val) : (literalFullData j J h l f a c r e).Admissible N p := by
  intro b hb q hq
  have hne : q≠l := by intro he;subst q;omega
  dsimp only [literalFullData]
  constructor
  · intro s
    rw [OrdinaryData.unitPullback_seedPartial
      (literalInitial J j (Real.sqrt (n:ℝ)) f (fld j J h l.val) (mag j J h l.val) a c r e)
      l Sum.inr (fun q : Fin M=>fld j J h q.val) (fun q : Fin M=>mag j J h q.val)
      (literalFullParameters j J h a c) rfl rfl]
    simp only [ite_eq_right hne]
  · intro s
    rw [OrdinaryData.unitPullback_auxPartial
      (literalInitial J j (Real.sqrt (n:ℝ)) f (fld j J h l.val) (mag j J h l.val) a c r e)
      l Sum.inr (fun q : Fin M=>fld j J h q.val) (fun q : Fin M=>mag j J h q.val)
      (literalFullParameters j J h a c) rfl rfl]
    simp only [ite_eq_right hne]

lemma literalFullData_coefficientClass (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (l : Fin M) (f : KernelExpr) (a c : Spin n→ℝ) (r e : Fin n→ℝ) (x : Spin n)
    {R B : ℝ} (hB : 0≤B) (ha : |a x|≤R) (haf : ∀k,|a (flip x k)|≤R)
    (hc : |Real.sqrt (n:ℝ)*c x|≤B) (hcf : ∀k,|Real.sqrt (n:ℝ)*c (flip x k)|≤B) (N : ℕ) :
    (literalFullData j J h l f a c r e).CoefficientClass N x (literalCoefficientBudget f j R B) := by
  exact (literalInitial_coefficientClass J j (Real.sqrt (n:ℝ)) f
    (fld j J h l.val) (mag j J h l.val) a c r e x hB ha haf hc hcf N).argumentPullback (fun _:Unit=>l) Sum.inr _ _ _ rfl rfl

lemma literalFullData_initial (j : ℝ) (J : Interaction n) (h : Fin n→ℝ)
    (l : Fin M) (f : KernelExpr) (a c : Spin n→ℝ) (r e : Fin n→ℝ)
    (w y : VectorFields n) (hn : 0<n) (x : Spin n)
    (heq : LiteralEquations J j f (fld j J h l.val) (mag j J h l.val) w y a c r e x) :
    (literalFullData j J h l f a c r e).startedSource w y 1 x=w x ∧
      (literalFullData j J h l f a c r e).startedAuxiliary w y 1 x=y x := by
  have hd : Real.sqrt (n:ℝ)≠0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  have hh:=(literalEquations_recipe J j (Real.sqrt (n:ℝ)) f (fld j J h l.val)
    (mag j J h l.val) w y a c r e hd x).mp heq
  exact OrdinaryData.unitPullback_started_duplicate _ l Sum.inr _ _ _ rfl rfl rfl w y x hh.1 hh.2.1

universe u
variable {Ω : Type u} {n : Ω→ℕ}

theorem literal_full_local_family (j : ℝ) (J : ∀b,Interaction (n b))
    (h : ∀b,Fin (n b)→ℝ) (l : Fin M) (f : KernelExpr)
    (a c : ∀b,Spin (n b)→ℝ) (r e : ∀b,Fin (n b)→ℝ)
    (w y : ∀b,VectorFields (n b)) (E : ∀b,Set (Spin (n b)))
    (hn : ∀b,0<n b) (he : ∀b,vectorNorm (e b)≤1)
    {R B : ℝ} (hB : 0≤B)
    (ha : ∀b x,x∈flipNeighborhood (flipNeighborhood (E b))→|a b x|≤R)
    (hc : ∀b x,x∈flipNeighborhood (flipNeighborhood (E b))→|Real.sqrt (n b:ℝ)*c b x|≤B)
    (heq : ∀b x,x∈E b→LiteralEquations (J b) j f (fld j (J b) (h b) l.val)
      (mag j (J b) (h b) l.val) (w b) (y b) (a b) (c b) (r b) (e b) x) :
    LocalFamilyRecipe E j J h (fun b=>literalFullParameters j (J b) (h b) (a b) (c b)) w y
      (fun b=>literalFullData j (J b) (h b) l f (a b) (c b) (r b) (e b)) 1 l.val
      (literalCoefficientBudget f j R B) := by
  refine ⟨le_rfl,fun _=>rfl,fun _=>rfl,fun _ _=>rfl,fun _ _=>rfl,fun _=>rfl,?_,?_,?_,?_⟩
  · refine ⟨2,by norm_num,fun b=>?_⟩
    exact literalInitial_seed_bound (J b) j f (fld j (J b) (h b) l.val)
      (mag j (J b) (h b) l.val) (a b) (c b) (r b) (e b) (hn b) (he b)
  · intro b x hx
    apply literalFullData_coefficientClass j (J b) (h b) l f (a b) (c b) (r b) (e b) x hB
    · exact ha b x (Or.inl hx)
    · intro k;exact ha b (flip x k) (Or.inr ⟨k,by simpa only [flip_flip] using hx⟩)
    · exact hc b x (Or.inl hx)
    · intro k;exact hc b (flip x k) (Or.inr ⟨k,by simpa only [flip_flip] using hx⟩)
  · intro b;exact literalFullData_admissible j (J b) (h b) l f (a b) (c b) (r b) (e b) 1 l.val le_rfl
  · intro b x hx;exact literalFullData_initial j (J b) (h b) l f (a b) (c b) (r b) (e b)
      (w b) (y b) (hn b) x (heq b x hx)

end SKGapCutoff.Recipe

end
end

end OAI
